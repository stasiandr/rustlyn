//! The resources an assembly carries beside its code.
//!
//! `ResourceManager.GetString("ERR_BadArg")` reads a `.resources` blob
//! embedded in the assembly: a table of names and values in the format
//! `System.Resources.ResourceReader` understands, listed in the manifest
//! under a name the manager derives from the class that owns it. A project
//! writes them as `.resx` files, which are XML; this turns the strings in
//! one into that blob, and the emitter embeds the blob.

/// One resource to embed: its manifest name, such as
/// `Microsoft.CodeAnalysis.CSharp.CSharpResources.resources`, and its bytes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Resource {
    pub name: String,
    pub data: Vec<u8>,
}

impl Resource {
    /// The `.resources` blob holding these strings, under this name.
    #[must_use]
    pub fn strings(name: &str, entries: &[(String, String)]) -> Self {
        Self {
            name: name.to_string(),
            data: string_resources(entries),
        }
    }
}

const MAGIC: u32 = 0xBEEF_CACE;
const READER: &str = "System.Resources.ResourceReader, mscorlib, Version=4.0.0.0, Culture=neutral, PublicKeyToken=b77a5c561934e089";
const SET: &str = "System.Resources.RuntimeResourceSet";
/// `ResourceTypeCode.String`.
const STRING: u8 = 1;

/// A `.resources` blob holding strings and nothing else, in the shape
/// `ResourceWriter` writes and `ResourceReader` reads.
///
/// The layout is a header naming the reader, then the names hashed and
/// sorted so the reader can search them, then the names themselves with the
/// offset of each value, then the values. Every string the format writes is
/// length-prefixed the way `BinaryWriter` does it: the names in UTF-16 with
/// the byte count in front, the values in UTF-8 with theirs.
#[must_use]
pub fn string_resources(entries: &[(String, String)]) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(&MAGIC.to_le_bytes());
    out.extend_from_slice(&1u32.to_le_bytes()); // header version
    let mut header = Vec::new();
    utf8_string(&mut header, READER);
    utf8_string(&mut header, SET);
    out.extend_from_slice(&(header.len() as u32).to_le_bytes());
    out.extend_from_slice(&header);

    out.extend_from_slice(&2u32.to_le_bytes()); // RuntimeResourceSet version
    out.extend_from_slice(&(entries.len() as u32).to_le_bytes());
    // No user types: a string is a type code the reader knows without a table.
    out.extend_from_slice(&0u32.to_le_bytes());
    // The hashes start on an eight-byte boundary, and the reader checks the
    // padding by its letters.
    let misaligned = out.len() & 7;
    if misaligned != 0 {
        for index in 0..8 - misaligned {
            out.push(b"PAD"[index % 3]);
        }
    }

    // Names in hash order, each with where its name and value were written.
    let mut names = Vec::new();
    let mut data = Vec::new();
    let mut sorted: Vec<(i32, usize)> = entries
        .iter()
        .enumerate()
        .map(|(index, (name, _))| (hash(name), index))
        .collect();
    sorted.sort_unstable();
    let mut positions = Vec::with_capacity(sorted.len());
    for (_, index) in &sorted {
        let (name, value) = &entries[*index];
        positions.push(names.len() as u32);
        utf16_string(&mut names, name);
        names.extend_from_slice(&(data.len() as u32).to_le_bytes());
        seven_bit(&mut data, u32::from(STRING));
        utf8_string(&mut data, value);
    }
    for (hash, _) in &sorted {
        out.extend_from_slice(&hash.to_le_bytes());
    }
    for position in &positions {
        out.extend_from_slice(&position.to_le_bytes());
    }
    let data_offset = out.len() + 4 + names.len();
    out.extend_from_slice(&(data_offset as u32).to_le_bytes());
    out.extend_from_slice(&names);
    out.extend_from_slice(&data);
    out
}

/// `FastResourceComparer.HashFunction`: what the reader hashes a name to.
fn hash(name: &str) -> i32 {
    let mut hash: u32 = 5381;
    for unit in name.encode_utf16() {
        hash = (hash << 5).wrapping_add(hash) ^ u32::from(unit);
    }
    hash as i32
}

fn seven_bit(out: &mut Vec<u8>, mut value: u32) {
    while value >= 0x80 {
        out.push((value as u8) | 0x80);
        value >>= 7;
    }
    out.push(value as u8);
}

fn utf8_string(out: &mut Vec<u8>, text: &str) {
    seven_bit(out, text.len() as u32);
    out.extend_from_slice(text.as_bytes());
}

fn utf16_string(out: &mut Vec<u8>, text: &str) {
    let units: Vec<u16> = text.encode_utf16().collect();
    seven_bit(out, (units.len() * 2) as u32);
    for unit in units {
        out.extend_from_slice(&unit.to_le_bytes());
    }
}

/// Every `<data name="…"><value>…</value></data>` in a `.resx` that holds a
/// string, in file order.
///
/// The format's own documentation sits at the top of every `.resx` as a
/// comment and contains `<data>` examples, so comments go first. An entry
/// with a type or a MIME type holds something that is not a string, and is
/// left out.
#[must_use]
pub fn resx_strings(text: &str) -> Vec<(String, String)> {
    let text = without_comments(text);
    let mut found = Vec::new();
    let mut rest = text.as_str();
    while let Some(start) = rest.find("<data ") {
        rest = &rest[start + "<data ".len()..];
        let Some(head) = rest.find('>') else { break };
        let (attributes, body) = rest.split_at(head);
        rest = &body[1..];
        if attributes.contains("type=") || attributes.contains("mimetype=") {
            continue;
        }
        let Some(name) = attribute(attributes, "name") else {
            continue;
        };
        let Some(value) = between(rest, "<value>", "</value>") else {
            continue;
        };
        found.push((name, unescape(value)));
    }
    found
}

fn without_comments(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(start) = rest.find("<!--") {
        out.push_str(&rest[..start]);
        match rest[start..].find("-->") {
            Some(end) => rest = &rest[start + end + "-->".len()..],
            None => return out,
        }
    }
    out.push_str(rest);
    out
}

fn attribute(attributes: &str, name: &str) -> Option<String> {
    let at = attributes.find(&format!("{name}=\""))? + name.len() + 2;
    let rest = &attributes[at..];
    Some(unescape(&rest[..rest.find('"')?]))
}

fn between<'a>(text: &'a str, open: &str, close: &str) -> Option<&'a str> {
    let start = text.find(open)? + open.len();
    let end = text[start..].find(close)? + start;
    Some(&text[start..end])
}

fn unescape(text: &str) -> String {
    text.replace("&lt;", "<")
        .replace("&gt;", ">")
        .replace("&quot;", "\"")
        .replace("&apos;", "'")
        .replace("&#xD;", "\r")
        .replace("&#xA;", "\n")
        .replace("&amp;", "&")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_blob_starts_with_the_magic_and_pads_the_hashes_to_eight_bytes() {
        let blob = string_resources(&[("Hello".to_string(), "world".to_string())]);
        assert_eq!(&blob[..4], &MAGIC.to_le_bytes());
        // Magic, header version, header size, the two names, the set
        // version, the counts: whatever that comes to, the hashes follow on
        // a boundary, behind letters of "PAD".
        let header_size = u32::from_le_bytes(blob[8..12].try_into().unwrap()) as usize;
        let after_counts = 12 + header_size + 12;
        let padding = (8 - (after_counts & 7)) & 7;
        assert_eq!(
            &blob[after_counts..after_counts + padding],
            &b"PADPADPA"[..padding]
        );
        let hashes = after_counts + padding;
        assert_eq!(
            i32::from_le_bytes(blob[hashes..hashes + 4].try_into().unwrap()),
            hash("Hello")
        );
    }

    #[test]
    fn the_hash_is_the_readers() {
        // 5381, shifted and folded over each UTF-16 unit.
        assert_eq!(hash(""), 5381);
        assert_eq!(hash("a"), ((5381u32 << 5).wrapping_add(5381) ^ 97) as i32);
    }

    #[test]
    fn a_resx_gives_its_string_entries_in_order() {
        let text = r#"<?xml version="1.0"?>
<root>
  <!-- <data name="Example"><value>not this</value></data> -->
  <data name="First" xml:space="preserve">
    <value>one &lt; two</value>
  </data>
  <data name="Icon" type="System.Drawing.Icon"><value>x</value></data>
  <data name="Second" xml:space="preserve">
    <value>line&#xD;&#xA;break</value>
  </data>
</root>"#;
        assert_eq!(
            resx_strings(text),
            vec![
                ("First".to_string(), "one < two".to_string()),
                ("Second".to_string(), "line\r\nbreak".to_string()),
            ]
        );
    }
}
