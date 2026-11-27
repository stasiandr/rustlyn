//! What a piece of removed code runs, read from its text. A line that is
//! gone has no syntax tree to bind, so the names in it are told apart by
//! their place: `new Gate(id)` runs the constructor of `Gate`, `o is Gate`
//! and `Gate g` only name the type; `Total` read in an expression runs a
//! property, a name in a string, a comment, `nameof` or `typeof` runs
//! nothing.

/// What one identifier of the code may run.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Use<'a> {
    pub word: &'a str,
    /// The name is in the place of an expression: a call, a read, a
    /// written member, a method group. It runs a method, a property, a
    /// field's initializer-free access, an event.
    pub expr: bool,
    /// `new Word(…)`, `new Word { … }`, a target-typed `new` whose type the
    /// declaration beside it gives: the constructor of the type runs.
    pub constructs: bool,
    /// In an attribute list: the constructor of `Word` or `WordAttribute`
    /// runs.
    pub attribute: bool,
    /// `: base(…)` or `: this(…)`, with `word` the keyword.
    pub chained: bool,
    /// How many arguments a call, a construction or an attribute gives;
    /// `None` where nothing is called (a read, a method group).
    pub args: Option<usize>,
}

/// The text with comments and the insides of string and character literals
/// blanked, byte for byte (a line break stays), so that positions are the
/// same. The code of an interpolation hole stays.
pub(crate) fn blank_noncode(text: &str) -> String {
    let bytes = text.as_bytes();
    let mut out = bytes.to_vec();
    code(bytes, 0, &mut out, false);
    String::from_utf8(out).unwrap_or_else(|_| text.to_owned())
}

fn blank(out: &mut [u8], from: usize, to: usize) {
    let to = to.min(out.len());
    for byte in &mut out[from..to] {
        if *byte != b'\n' {
            *byte = b' ';
        }
    }
}

/// Reads code from `at`, to the end or, in a hole, to the `}` that closes
/// it; gives where it stopped.
fn code(bytes: &[u8], mut at: usize, out: &mut [u8], hole: bool) -> usize {
    let mut depth = 0usize;
    while at < bytes.len() {
        let byte = bytes[at];
        let next = bytes.get(at + 1).copied();
        match byte {
            b'/' if next == Some(b'/') => {
                let end = bytes[at..]
                    .iter()
                    .position(|&b| b == b'\n')
                    .map_or(bytes.len(), |n| at + n);
                blank(out, at, end);
                at = end;
            }
            b'/' if next == Some(b'*') => {
                let end = find(bytes, at + 2, b"*/").map_or(bytes.len(), |n| n + 2);
                blank(out, at, end);
                at = end;
            }
            b'"' => at = string(bytes, at, out, false, false),
            b'$' | b'@' => {
                // `$"`, `@"`, `$@"`, `@$"`, `$$"""`.
                let mut end = at;
                let (mut interpolated, mut verbatim) = (false, false);
                while let Some(&b) = bytes.get(end) {
                    match b {
                        b'$' => interpolated = true,
                        b'@' => verbatim = true,
                        _ => break,
                    }
                    end += 1;
                }
                if bytes.get(end) == Some(&b'"') {
                    at = string(bytes, end, out, interpolated, verbatim);
                } else {
                    at += 1;
                }
            }
            b'\'' => {
                let mut end = at + 1;
                while end < bytes.len() && bytes[end] != b'\'' && bytes[end] != b'\n' {
                    end += if bytes[end] == b'\\' { 2 } else { 1 };
                }
                blank(out, at + 1, end);
                at = (end + 1).min(bytes.len());
            }
            b'{' if hole => {
                depth += 1;
                at += 1;
            }
            b'}' if hole => {
                if depth == 0 {
                    return at;
                }
                depth -= 1;
                at += 1;
            }
            _ => at += 1,
        }
    }
    at
}

fn find(bytes: &[u8], from: usize, needle: &[u8]) -> Option<usize> {
    bytes
        .get(from..)?
        .windows(needle.len())
        .position(|w| w == needle)
        .map(|n| from + n)
}

/// A string literal that opens with the quote at `open`: its inside is
/// blanked, the holes of an interpolated one are code. Gives the byte after
/// it.
fn string(bytes: &[u8], open: usize, out: &mut [u8], interpolated: bool, verbatim: bool) -> usize {
    let mut quotes = 0;
    while bytes.get(open + quotes) == Some(&b'"') {
        quotes += 1;
    }
    // `""` is an empty string; three or more open a raw string.
    let raw = quotes >= 3;
    let start = if raw { open + quotes } else { open + 1 };
    // The quotes of an interpolated string go too: its holes are code that
    // a reader of tokens must not take for a literal.
    if interpolated {
        blank(out, open, start);
    }
    let mut at = start;
    while at < bytes.len() {
        let byte = bytes[at];
        if raw {
            if byte == b'"' && bytes[at..].iter().take_while(|&&b| b == b'"').count() >= quotes {
                blank(out, start, at);
                if interpolated {
                    blank(out, at, at + quotes);
                }
                return at + quotes;
            }
        } else if byte == b'"' {
            if verbatim && bytes.get(at + 1) == Some(&b'"') {
                blank(out, at, at + 2);
                at += 2;
                continue;
            }
            if interpolated {
                out[at] = b' ';
            }
            return at + 1;
        } else if byte == b'\\' && !verbatim {
            blank(out, at, at + 2);
            at += 2;
            continue;
        } else if byte == b'\n' && !verbatim {
            // An unterminated string stops at the end of its line.
            return at;
        }
        if interpolated && byte == b'{' {
            if bytes.get(at + 1) == Some(&b'{') {
                blank(out, at, at + 2);
                at += 2;
                continue;
            }
            let end = code(bytes, at + 1, out, true);
            at = (end + 1).min(bytes.len());
            continue;
        }
        if byte != b'\n' {
            out[at] = b' ';
        }
        at += 1;
    }
    at
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Kind {
    Ident,
    Literal,
    Punct,
}

#[derive(Debug, Clone, Copy)]
struct Tok<'a> {
    kind: Kind,
    text: &'a str,
    /// Whitespace between this token and the one before it.
    spaced: bool,
}

impl Tok<'_> {
    fn is(&self, text: &str) -> bool {
        self.kind != Kind::Literal && self.text == text
    }

    fn ident(&self) -> bool {
        self.kind == Kind::Ident
    }
}

fn tokens(code: &str) -> Vec<Tok<'_>> {
    let bytes = code.as_bytes();
    let mut toks = Vec::new();
    let mut at = 0;
    let mut spaced = false;
    while at < bytes.len() {
        let byte = bytes[at];
        if byte.is_ascii_whitespace() {
            spaced = true;
            at += 1;
            continue;
        }
        let ident_byte = |b: u8| b.is_ascii_alphanumeric() || b == b'_' || b >= 0x80;
        let start = at;
        let kind = if ident_byte(byte)
            || (byte == b'@' && bytes.get(at + 1).is_some_and(|&b| ident_byte(b)))
        {
            at += 1;
            while at < bytes.len() && ident_byte(bytes[at]) {
                at += 1;
            }
            if byte.is_ascii_digit() {
                // A number: `1.5f`, `0x1F`.
                while at < bytes.len()
                    && (ident_byte(bytes[at])
                        || (bytes[at] == b'.' && bytes.get(at + 1).is_some_and(u8::is_ascii_digit)))
                {
                    at += 1;
                }
                Kind::Literal
            } else {
                Kind::Ident
            }
        } else if byte == b'"' || byte == b'\'' {
            at += 1;
            while at < bytes.len() && bytes[at] != byte {
                at += 1;
            }
            at = (at + 1).min(bytes.len());
            Kind::Literal
        } else {
            let two = code.get(at..at + 2).unwrap_or_default();
            at += if matches!(
                two,
                "=>" | "::"
                    | "?."
                    | "=="
                    | "!="
                    | "<="
                    | ">="
                    | "&&"
                    | "||"
                    | "??"
                    | "+="
                    | "-="
                    | "++"
                    | "--"
                    | "->"
            ) {
                2
            } else {
                1
            };
            Kind::Punct
        };
        // `>=` closes nothing generic; but `=>` after `>` is a lambda.
        toks.push(Tok {
            kind,
            text: &code[start..at.min(code.len())],
            spaced,
        });
        spaced = false;
    }
    toks
}

/// Words that, before a name, leave it in the place of an expression.
fn leaves_expression(word: &str) -> bool {
    matches!(
        word,
        "return"
            | "await"
            | "yield"
            | "throw"
            | "case"
            | "in"
            | "else"
            | "do"
            | "when"
            | "and"
            | "or"
            | "not"
            | "ref"
            | "out"
            | "lock"
            | "goto"
    )
}

/// Words that follow a name inside an expression or a pattern.
fn continues_expression(word: &str) -> bool {
    matches!(
        word,
        "is" | "as" | "and" | "or" | "when" | "with" | "switch" | "in" | "not"
    )
}

/// The identifiers of `code` that stand where something runs, or where a
/// constructor does. `code` has no comments or strings in it
/// ([`blank_noncode`]).
pub(crate) fn uses(code: &str) -> Vec<Use<'_>> {
    let toks = tokens(code);
    let n = toks.len();
    // Generic argument lists: `List<Gate>`, `Run<int>(x)`. `inside[i]` is
    // true for what is between the angle brackets, `closing[i]` for the `>`.
    let mut inside = vec![false; n];
    let mut closing = vec![false; n];
    let mut matching: Vec<Option<usize>> = vec![None; n];
    for i in 1..n {
        if !(toks[i].is("<") && toks[i - 1].ident() && !toks[i].spaced) {
            continue;
        }
        let mut depth = 0usize;
        let mut j = i;
        let mut end = None;
        while j < n {
            let t = toks[j];
            if t.is("<") {
                depth += 1;
            } else if t.is(">") {
                depth -= 1;
                if depth == 0 {
                    end = Some(j);
                    break;
                }
            } else if !(t.ident()
                || t.is(".")
                || t.is(",")
                || t.is("?")
                || t.is("[")
                || t.is("]")
                || t.is("::"))
            {
                break;
            }
            j += 1;
        }
        if let Some(end) = end {
            inside[i + 1..end].fill(true);
            closing[end] = true;
            matching[i] = Some(end);
        }
    }
    // The bracket each token is in: its kind, and for a brace whether it
    // follows `new` (an anonymous type).
    let mut stack: Vec<(char, bool)> = Vec::new();
    let mut within: Vec<Option<(char, bool)>> = Vec::with_capacity(n);
    for i in 0..n {
        within.push(stack.last().copied());
        let t = toks[i];
        if t.is("(") || t.is("[") {
            stack.push((t.text.chars().next().unwrap_or('('), false));
        } else if t.is("{") {
            stack.push(('{', i > 0 && toks[i - 1].is("new")));
        } else if (t.is(")") || t.is("]") || t.is("}")) && !stack.is_empty() {
            stack.pop();
        }
    }
    let mut found = Vec::new();
    for i in 0..n {
        let t = toks[i];
        if !t.ident() {
            continue;
        }
        let prev = i.checked_sub(1).map(|p| toks[p]);
        if (t.is("base") || t.is("this"))
            && prev.is_some_and(|p| p.is(":"))
            && toks.get(i + 1).is_some_and(|next| next.is("("))
        {
            found.push(Use {
                word: t.text,
                expr: false,
                constructs: false,
                attribute: false,
                chained: true,
                args: Some(count_arguments(&toks, &inside, i + 1)),
            });
            continue;
        }
        // The qualified name this is the last of: `Ns.Gate`, `a.b.Total`.
        let mut first = i;
        let mut plain = true;
        while first >= 2 && (toks[first - 1].is(".") || toks[first - 1].is("::")) {
            if toks[first - 2].ident() {
                first -= 2;
            } else {
                plain = false;
                break;
            }
        }
        if first >= 1 && (toks[first - 1].is(".") || toks[first - 1].is("?.")) {
            plain = false;
        }
        let before = if plain {
            first.checked_sub(1).map(|p| toks[p])
        } else {
            None
        };
        // What follows: past generic arguments, `?`, `[]`.
        let mut after = i + 1;
        if let Some(close) = matching.get(after).copied().flatten() {
            after = close + 1;
        }
        let generic = after != i + 1;
        let mut look = after;
        if toks.get(look).is_some_and(|x| x.is("?") && !x.spaced) {
            look += 1;
        }
        while toks.get(look).is_some_and(|x| x.is("["))
            && toks.get(look + 1).is_some_and(|x| x.is("]") || x.is(","))
        {
            look += 2;
        }
        let next = toks.get(look).copied();
        let name_after = next.is_some_and(|x| x.ident() && !continues_expression(x.text));
        let eq_next = next.is_some_and(|x| x.is("="));

        // Where the name is a type or a declaration, not an expression.
        let mut typed = inside[i] || closing[i];
        if let Some(b) = before {
            if b.ident() && !leaves_expression(b.text) {
                typed = true;
            }
            if b.is("]") {
                typed = true;
            }
            if b.is(">") && closing[first - 1] {
                typed = true;
            }
            if b.is("?")
                && !b.spaced
                && first >= 2
                && toks[first - 2].ident()
                && !toks[first - 2].is("return")
            {
                typed = true;
            }
            // `typeof(Gate)`, `nameof(a.X)`, `sizeof`, `default(T)`.
            if b.is("(")
                && first >= 2
                && matches!(
                    toks[first - 2].text,
                    "typeof" | "nameof" | "sizeof" | "default"
                )
                && toks[first - 2].ident()
            {
                typed = true;
            }
            // A cast: `(Gate)x`.
            if b.is("(")
                && next.is_some_and(|x| x.is(")"))
                && toks.get(look + 1).is_some_and(|x| {
                    (x.ident() && !continues_expression(x.text))
                        || x.kind == Kind::Literal
                        || x.is("(")
                        || x.is("!")
                        || x.is("~")
                })
            {
                typed = true;
            }
            // A named argument, a name in an anonymous type.
            if (b.is("(") || b.is(","))
                && next.is_some_and(|x| x.is(":"))
                && within[first].is_some_and(|(open, _)| open == '(' || open == '[')
            {
                typed = true;
            }
            if (b.is("{") || b.is(","))
                && eq_next
                && within[first].is_some_and(|(open, anon)| open == '{' && anon)
            {
                typed = true;
            }
            // A base list or a constraint: `class A : Gate`, `where T : Gate`.
            if b.is(":") || b.is(",") {
                let mut k = first;
                let mut colon = false;
                let mut declaring = false;
                while k > 0 {
                    k -= 1;
                    let x = toks[k];
                    if x.is(";") || x.is("{") || x.is("}") || x.is("=>") || x.is("=") {
                        break;
                    }
                    if x.is(":") {
                        colon = true;
                    }
                    if x.ident()
                        && matches!(
                            x.text,
                            "class" | "struct" | "interface" | "record" | "enum" | "where"
                        )
                        && !(k > 0 && toks[k - 1].is("."))
                    {
                        declaring = colon || b.is(":");
                        break;
                    }
                }
                if declaring {
                    typed = true;
                }
            }
        }
        if name_after {
            typed = true;
        }

        let constructing = before.is_some_and(|b| b.is("new"))
            && first >= 1
            && !(first >= 2 && toks[first - 2].is("."))
            && next.is_some_and(|x| x.is("(") || x.is("{"));
        // `Gate g = new();`: the type the declaration names.
        let target = {
            let mut k = look;
            // `Gate g =`: a name, then `=`, then `new`, then `(` or `{`.
            let named = toks
                .get(k)
                .is_some_and(|x| x.ident() && !continues_expression(x.text));
            k += 1;
            named
                && !generic
                && before.is_none_or(|b| !b.is("new"))
                && toks.get(k).is_some_and(|x| x.is("="))
                && toks.get(k + 1).is_some_and(|x| x.is("new"))
                && toks.get(k + 2).is_some_and(|x| x.is("(") || x.is("{"))
        };
        // `[Gate]`, `[Gate(1)]`, `[assembly: Gate]`.
        let attribute = within[first].is_some_and(|(open, _)| open == '[')
            && before.is_some_and(|b| b.is("[") || b.is(",") || b.is(":"))
            && attribute_list(&toks, first);
        // The arguments of what is called, constructed or attached.
        let args = if target {
            let at = look + 3;
            Some(if toks[at].is("(") {
                count_arguments(&toks, &inside, at)
            } else {
                0
            })
        } else if next.is_some_and(|x| x.is("(")) {
            Some(count_arguments(&toks, &inside, look))
        } else if constructing || attribute {
            Some(0)
        } else {
            None
        };
        found.push(Use {
            word: t.text,
            expr: !typed && !constructing,
            constructs: constructing || target,
            attribute,
            chained: false,
            args,
        });
    }
    found
}

/// How many arguments the parenthesis that opens at token `open` holds.
fn count_arguments(toks: &[Tok<'_>], generic: &[bool], open: usize) -> usize {
    let (mut depth, mut commas, mut content) = (0usize, 0usize, false);
    for (k, t) in toks.iter().enumerate().skip(open) {
        if t.is("(") || t.is("[") || t.is("{") {
            depth += 1;
            content |= depth > 1;
        } else if t.is(")") || t.is("]") || t.is("}") {
            depth = depth.saturating_sub(1);
            if depth == 0 {
                break;
            }
        } else if depth == 1 && t.is(",") && !generic[k] {
            commas += 1;
        } else if depth >= 1 {
            content = true;
        }
    }
    if content { commas + 1 } else { 0 }
}

/// Whether the `[` that holds token `at` opens an attribute list: it starts
/// a statement or a member rather than indexing a value.
fn attribute_list(toks: &[Tok<'_>], at: usize) -> bool {
    let mut depth = 0usize;
    let mut k = at;
    while k > 0 {
        k -= 1;
        let t = toks[k];
        if t.is("]") {
            depth += 1;
        } else if t.is("[") {
            if depth == 0 {
                return k == 0 || matches!(toks[k - 1].text, ";" | "{" | "}" | "]" | ")");
            }
            depth -= 1;
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;

    fn words(code: &str) -> Vec<(&str, bool, bool)> {
        let blanked = blank_noncode(code);
        let leaked: &'static str = Box::leak(blanked.into_boxed_str());
        uses(leaked)
            .into_iter()
            .map(|u| (u.word, u.expr, u.constructs))
            .collect()
    }

    fn runs(code: &str, name: &str) -> bool {
        words(code)
            .iter()
            .any(|&(w, expr, new)| w == name && (expr || new))
    }

    #[test]
    fn a_type_position_runs_nothing() {
        assert!(!runs("return o is Gate;", "Gate"));
        assert!(!runs("return o is Gate && true;", "Gate"));
        assert!(!runs("Same(obj as Gate);", "Gate"));
        assert!(!runs("bool Same(Gate g) { return g != null; }", "Gate"));
        assert!(!runs("var x = (Gate)o;", "Gate"));
        assert!(!runs("var t = typeof(Gate);", "Gate"));
        assert!(!runs("var t = nameof(Gate);", "Gate"));
        assert!(!runs("List<Gate> all;", "Gate"));
        assert!(!runs("Gate[] all = null;", "Gate"));
        assert!(!runs("Gate? g = null;", "Gate"));
        assert!(!runs("class Door : Gate {", "Gate"));
        assert!(!runs("where T : Gate", "Gate"));
        assert!(!runs("foreach (Gate g in gates) {", "Gate"));
        assert!(!runs("var n = nameof(a.Total).Length;", "Total"));
        assert!(!runs("Foo(Total: 3);", "Total"));
        assert!(!runs("var a = new { Total = 1 };", "Total"));
    }

    #[test]
    fn words_in_comments_and_strings_run_nothing() {
        assert!(!runs("var s = \"new Gate(1)\"; // new Gate(2)", "Gate"));
        assert!(!runs("/* Run(); */ x();", "Run"));
        assert!(!runs("var s = @\"a \"\"Run()\"\" b\";", "Run"));
        assert!(!runs("var s = $\"{{Run()}}\";", "Run"));
        assert!(runs("var s = $\"x {Run()} y\";", "Run"));
    }

    #[test]
    fn a_run_is_found() {
        assert!(runs("var g = new Gate(id);", "Gate"));
        assert!(runs("var g = new Game.Gate(id);", "Gate"));
        assert!(runs("var g = new Gate<int>(id);", "Gate"));
        assert!(runs("var g = new Gate { Id = 1 };", "Gate"));
        assert!(runs("Gate g = new();", "Gate"));
        assert!(runs("Gate g = new() { Id = 1 };", "Gate"));
        assert!(!runs("var g = new Gate[3];", "Gate"));
        assert!(runs("Run();", "Run"));
        assert!(runs("x.Run(1);", "Run"));
        assert!(runs("var a = await Run();", "Run"));
        assert!(runs("return Run<int>(1);", "Run"));
        assert!(runs("var n = x.Total;", "Total"));
        assert!(runs("return Total;", "Total"));
        assert!(runs("Use(Total);", "Total"));
        assert!(runs("button.Click += Run;", "Run"));
        assert!(runs("var f = (Func<int>)Run;", "Run"));
        assert!(runs("var g = new Gate { Total = 1 };", "Total"));
        assert!(runs("if (x is { Total: 3 }) {}", "Total"));
        assert!(runs("var a = new { Total };", "Total"));
        assert!(runs("var p = (Total);", "Total"));
        assert!(runs("case Total:", "Total"));
    }

    #[test]
    fn attributes_and_chained_constructors() {
        let attr = |code: &str, name: &str| {
            let blanked = blank_noncode(code);
            let leaked: &'static str = Box::leak(blanked.into_boxed_str());
            uses(leaked).iter().any(|u| u.word == name && u.attribute)
        };
        assert!(attr("[Gate]", "Gate"));
        assert!(attr("[Gate(1)] int x;", "Gate"));
        assert!(attr("[Serializable, Gate]", "Gate"));
        assert!(!attr("var a = list[Gate];", "Gate"));
        let chained = |code: &str, name: &str| {
            let blanked = blank_noncode(code);
            let leaked: &'static str = Box::leak(blanked.into_boxed_str());
            uses(leaked).iter().any(|u| u.word == name && u.chained)
        };
        assert!(chained("public Door(int x) : base(x) {", "base"));
        assert!(chained("public Door() : this(1) {}", "this"));
        assert!(!chained("var a = b ? this.x : 3;", "this"));
    }
}
