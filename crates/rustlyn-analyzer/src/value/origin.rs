//! Where a value comes from — where the value graph stops because the
//! answer is found: a literal in the code, a constant, an enum value, a
//! config's JSON, the Unity inspector, the engine's time or a random
//! number. The graph shows them as nodes of their own: they are the answer
//! to "where does it come from".
//!
//! Only classification by text and names here, without the compiler.
use super::text::trim_spaces;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[repr(u8)]
pub enum Kind {
    /// A literal in the code: `0`, `"idle"`, `true`.
    Literal = 0,
    /// `const`, or an assembly member such as `Vector3.zero`, `int.MaxValue`.
    Constant,
    /// `JobType.Courier`.
    EnumValue,
    /// The initial value of a field or property in its declaration.
    Initial,
    /// A default: `default`, `null`, `new()`, a parameter's `= 5` the call did not pass.
    DefaultValue,
    /// The project's config JSON: a model whose keys a host's rules describe.
    Config,
    /// JSON in general: a message, a service's answer, `JsonConvert.Deserialize`.
    Json,
    /// A table column, a database query.
    Database,
    /// The network: a value from a linked project that cannot be followed there.
    Network,
    /// The Unity inspector: the value lives in a prefab, a scene or an asset.
    Inspector,
    /// A dependency container: `[Inject]`, `[Injectable]`.
    Injection,
    /// `Time.deltaTime`, `DateTime.UtcNow`, `Stopwatch`.
    Time,
    /// `Random.Range`, `Guid.NewGuid`.
    Random,
    /// Player input: keyboard, touches, UI fields, the console.
    Input,
    /// Files, PlayerPrefs, the environment, HTTP, resources.
    External,
    /// The engine's state: Transform, physics, the screen.
    Engine,
    /// An assembly member nothing more is known about.
    Library,
}

impl Kind {
    pub const ALL: [Kind; 17] = [
        Kind::Literal,
        Kind::Constant,
        Kind::EnumValue,
        Kind::Initial,
        Kind::DefaultValue,
        Kind::Config,
        Kind::Json,
        Kind::Database,
        Kind::Network,
        Kind::Inspector,
        Kind::Injection,
        Kind::Time,
        Kind::Random,
        Kind::Input,
        Kind::External,
        Kind::Engine,
        Kind::Library,
    ];

    pub fn from_raw(raw: u8) -> Option<Kind> {
        Kind::ALL.get(raw as usize).copied()
    }

    /// The kind's stable name, as `--json` writes it.
    pub fn raw_name(self) -> &'static str {
        match self {
            Kind::Literal => "literal",
            Kind::Constant => "constant",
            Kind::EnumValue => "enumValue",
            Kind::Initial => "initial",
            Kind::DefaultValue => "defaultValue",
            Kind::Config => "config",
            Kind::Json => "json",
            Kind::Database => "database",
            Kind::Network => "network",
            Kind::Inspector => "inspector",
            Kind::Injection => "injection",
            Kind::Time => "time",
            Kind::Random => "random",
            Kind::Input => "input",
            Kind::External => "external",
            Kind::Engine => "engine",
            Kind::Library => "library",
        }
    }

    /// How a node's subtitle and the legend name the kind.
    pub const fn label(self) -> &'static str {
        match self {
            Kind::Literal => "literal",
            Kind::Constant => "constant",
            Kind::EnumValue => "enum value",
            Kind::Initial => "initial value",
            Kind::DefaultValue => "default",
            Kind::Config => "config",
            Kind::Json => "JSON",
            Kind::Database => "database",
            Kind::Network => "network",
            Kind::Inspector => "Unity inspector",
            Kind::Injection => "dependency injection",
            Kind::Time => "time",
            Kind::Random => "random number",
            Kind::Input => "player input",
            Kind::External => "files and environment",
            Kind::Engine => "engine",
            Kind::Library => "assembly",
        }
    }

    /// The value is set in the code, rather than coming from outside while the game runs.
    pub fn is_written_in_code(self) -> bool {
        matches!(
            self,
            Kind::Literal | Kind::Constant | Kind::EnumValue | Kind::Initial | Kind::DefaultValue
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ValueOrigin {
    pub kind: Kind,
    /// What to show: `1500`, `Time.deltaTime`, `car_spawn_check_radius`.
    pub title: String,
}

impl ValueOrigin {
    pub fn new(kind: Kind, title: impl Into<String>) -> Self {
        ValueOrigin {
            kind,
            title: title.into(),
        }
    }
}

/// What an assembly member is to the value graph.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Library {
    /// A source: time, a random number, input, files, the engine.
    Origin(Kind),
    /// A library constant: `Vector3.zero`, `int.MaxValue`, `string.Empty`.
    Constant,
    /// A transformation: `Math.Max`, `Parse`, `list.Count`, `ToString()` —
    /// the value comes from the arguments and the receiver, and the call
    /// itself is not a source.
    Transform,
    /// Unknown: a member of someone else's assembly.
    Unknown,
}

/// An assembly member by its type's name (full `UnityEngine.Time` or short
/// `Time`) and the member's name. The short name is for when the compiler
/// does not know the type (`Math.Min` on net8.0) and it was taken from the text.
pub fn classify(type_name: &str, member: &str) -> Library {
    let cleaned = clean_type(type_name);
    let parts: Vec<&str> = cleaned.split('.').filter(|p| !p.is_empty()).collect();
    let Some(&short) = parts.last() else {
        return Library::Unknown;
    };
    let namespace = parts[..parts.len() - 1].join(".");
    let unity = namespace.is_empty() || namespace.starts_with("UnityEngine");
    let system = namespace.is_empty() || namespace.starts_with("System");

    // Time.
    if short == "Time" && unity {
        return Library::Origin(Kind::Time);
    }
    if short == "Stopwatch" && system {
        return Library::Origin(Kind::Time);
    }
    if ["DateTime", "DateTimeOffset"].contains(&short)
        && ["Now", "UtcNow", "Today"].contains(&member)
    {
        return Library::Origin(Kind::Time);
    }
    if short == "Environment" && member.starts_with("TickCount") {
        return Library::Origin(Kind::Time);
    }
    if short == "AudioSettings" && member == "dspTime" {
        return Library::Origin(Kind::Time);
    }
    if short == "TimeProvider" {
        return Library::Origin(Kind::Time);
    }
    // Random.
    if short == "Random" && (unity || system || namespace.starts_with("Unity.Mathematics")) {
        return Library::Origin(Kind::Random);
    }
    if short == "Guid" && member == "NewGuid" {
        return Library::Origin(Kind::Random);
    }
    if short == "RandomNumberGenerator" {
        return Library::Origin(Kind::Random);
    }
    // Player input.
    if short == "Input" && unity {
        return Library::Origin(Kind::Input);
    }
    if namespace.starts_with("UnityEngine.InputSystem") {
        return Library::Origin(Kind::Input);
    }
    if short == "Console" && member.starts_with("Read") {
        return Library::Origin(Kind::Input);
    }
    if ["InputField", "TMP_InputField"].contains(&short) && member == "text" {
        return Library::Origin(Kind::Input);
    }
    if ["Slider", "Scrollbar", "Dropdown", "TMP_Dropdown"].contains(&short) && member == "value" {
        return Library::Origin(Kind::Input);
    }
    if short == "Toggle" && member == "isOn" {
        return Library::Origin(Kind::Input);
    }
    // JSON.
    if ["JsonConvert", "JsonSerializer"].contains(&short)
        && (member.starts_with("Deserialize") || member.starts_with("Populate"))
    {
        return Library::Origin(Kind::Json);
    }
    if short == "JsonUtility" && member.starts_with("FromJson") {
        return Library::Origin(Kind::Json);
    }
    if ["JObject", "JToken", "JArray", "JValue"].contains(&short) {
        return Library::Origin(Kind::Json);
    }
    // Database.
    let databases = [
        "MySqlConnector",
        "MySql.Data",
        "Npgsql",
        "Dapper",
        "Microsoft.EntityFrameworkCore",
        "System.Data",
        "StackExchange.Redis",
        "MongoDB",
        "Microsoft.Data",
    ];
    if databases
        .iter()
        .any(|d| namespace == *d || namespace.starts_with(&format!("{d}.")))
    {
        return Library::Origin(Kind::Database);
    }
    // Files, the environment, the network, resources.
    if short == "Path" {
        return Library::Transform;
    }
    if namespace == "System.IO" || namespace.starts_with("System.IO.") {
        return Library::Origin(Kind::External);
    }
    if namespace == "System.Net" || namespace.starts_with("System.Net.") {
        return Library::Origin(Kind::External);
    }
    if [
        "PlayerPrefs",
        "Environment",
        "UnityWebRequest",
        "HttpClient",
        "WebClient",
        "Resources",
        "Addressables",
        "AssetDatabase",
        "AssetBundle",
        "SystemInfo",
        "Application",
        "EditorPrefs",
    ]
    .contains(&short)
    {
        return Library::Origin(Kind::External);
    }
    // Pure functions and what is taken from a value: from the arguments and the receiver.
    // Except the constants of the same types: `Vector3.zero` next to `Vector3.Lerp`
    // (while `transform.up` is not a constant: Transform is not among them).
    if TRANSFORMS.contains(&short) {
        return if CONSTANTS.contains(&member) {
            Library::Constant
        } else {
            Library::Transform
        };
    }
    // Everything else of Unity is the engine's state: Transform, physics, the camera.
    if namespace.starts_with("UnityEngine")
        || namespace.starts_with("UnityEditor")
        || namespace.starts_with("Unity.")
        || [
            "Transform",
            "GameObject",
            "Component",
            "MonoBehaviour",
            "Physics",
            "Physics2D",
            "Camera",
            "Screen",
            "Animator",
            "Rigidbody",
            "Rigidbody2D",
            "Collider",
            "NavMeshAgent",
            "Renderer",
        ]
        .contains(&short)
    {
        return Library::Origin(Kind::Engine);
    }
    Library::Unknown
}

/// `System.Collections.Generic.Dictionary`2` and `List<int>` without arity
/// or type arguments; `int?` is `int`.
pub fn clean_type(type_name: &str) -> String {
    let mut result = type_name;
    if let Some(angle) = result.find('<') {
        result = &result[..angle];
    }
    if let Some(tick) = result.find('`') {
        result = &result[..tick];
    }
    loop {
        if let Some(rest) = result.strip_suffix('?') {
            result = rest;
        } else if let Some(rest) = result.strip_suffix("[]") {
            result = rest;
        } else {
            break;
        }
    }
    trim_spaces(result).to_owned()
}

/// Types whose members transform what they are given: math, strings,
/// collections, numbers, time as a quantity.
pub const TRANSFORMS: &[&str] = &[
    "Math",
    "MathF",
    "Mathf",
    "math",
    "Convert",
    "BitConverter",
    "BinaryPrimitives",
    "Enum",
    "Array",
    "Buffer",
    "String",
    "string",
    "StringBuilder",
    "Char",
    "char",
    "Encoding",
    "Regex",
    "Match",
    "Group",
    "Enumerable",
    "Queryable",
    "ParallelEnumerable",
    "Tuple",
    "ValueTuple",
    "KeyValuePair",
    "Nullable",
    "Lazy",
    "Object",
    "object",
    "ValueType",
    "Int16",
    "Int32",
    "Int64",
    "UInt16",
    "UInt32",
    "UInt64",
    "Byte",
    "SByte",
    "Single",
    "Double",
    "Decimal",
    "Boolean",
    "int",
    "uint",
    "long",
    "ulong",
    "short",
    "ushort",
    "byte",
    "sbyte",
    "float",
    "double",
    "decimal",
    "bool",
    "Half",
    "BigInteger",
    "Complex",
    "TimeSpan",
    "DateTime",
    "DateTimeOffset",
    "DateOnly",
    "TimeOnly",
    "Guid",
    "Uri",
    "Version",
    "List",
    "Dictionary",
    "HashSet",
    "SortedSet",
    "SortedDictionary",
    "SortedList",
    "LinkedList",
    "Queue",
    "Stack",
    "PriorityQueue",
    "ConcurrentDictionary",
    "ConcurrentQueue",
    "ConcurrentBag",
    "ConcurrentStack",
    "ImmutableArray",
    "ImmutableList",
    "ImmutableDictionary",
    "ImmutableHashSet",
    "ReadOnlyCollection",
    "IEnumerable",
    "IEnumerator",
    "ICollection",
    "IList",
    "IDictionary",
    "ISet",
    "IReadOnlyList",
    "IReadOnlyCollection",
    "IReadOnlyDictionary",
    "IReadOnlySet",
    "CollectionExtensions",
    "CollectionsMarshal",
    "Span",
    "ReadOnlySpan",
    "Memory",
    "ReadOnlyMemory",
    "ArraySegment",
    "MemoryExtensions",
    "MemoryMarshal",
    "Unsafe",
    "Task",
    "ValueTask",
    "Interlocked",
    "Volatile",
    "StringComparer",
    "Comparer",
    "EqualityComparer",
    "CultureInfo",
    "StringComparison",
    "Vector2",
    "Vector3",
    "Vector4",
    "Vector2Int",
    "Vector3Int",
    "Quaternion",
    "Matrix4x4",
    "Plane",
    "Ray",
    "Color",
    "Color32",
    "Rect",
    "RectInt",
    "Bounds",
    "BoundsInt",
    "LayerMask",
    "AnimationCurve",
    "Gradient",
    "float2",
    "float3",
    "float4",
    "int2",
    "int3",
    "int4",
    "quaternion",
    "float4x4",
];

/// Members that are a constant of any type: `Vector3.zero`, `int.MaxValue`.
pub const CONSTANTS: &[&str] = &[
    "MaxValue",
    "MinValue",
    "Epsilon",
    "PositiveInfinity",
    "NegativeInfinity",
    "NaN",
    "Empty",
    "Zero",
    "One",
    "zero",
    "one",
    "up",
    "down",
    "left",
    "right",
    "forward",
    "back",
    "identity",
    "positiveInfinity",
    "negativeInfinity",
    "white",
    "black",
    "red",
    "green",
    "blue",
    "clear",
    "gray",
    "grey",
    "yellow",
    "cyan",
    "magenta",
    "PI",
    "E",
    "Tau",
    "Deg2Rad",
    "Rad2Deg",
    "Infinity",
    "NegativeInfinity",
    "MaxLength",
    "Ordinal",
    "OrdinalIgnoreCase",
    "InvariantCulture",
    "InvariantCultureIgnoreCase",
    "CurrentCulture",
];

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn libraries() {
        assert_eq!(
            classify("UnityEngine.Time", "deltaTime"),
            Library::Origin(Kind::Time),
            "Time.deltaTime is time"
        );
        assert!(
            classify("System.DateTime", "UtcNow") == Library::Origin(Kind::Time)
                && classify("System.DateTime", "AddSeconds") == Library::Transform,
            "DateTime.UtcNow is time, AddSeconds is not"
        );
        assert_eq!(
            classify("Stopwatch", "Frequency"),
            Library::Origin(Kind::Time),
            "Stopwatch by its short name"
        );
        assert!(
            classify("UnityEngine.Random", "Range") == Library::Origin(Kind::Random)
                && classify("Random", "Next") == Library::Origin(Kind::Random)
                && classify("System.Guid", "NewGuid") == Library::Origin(Kind::Random),
            "random"
        );
        assert_eq!(
            classify("UnityEngine.Input", "GetAxis"),
            Library::Origin(Kind::Input),
            "player input"
        );
        assert_eq!(
            classify("Newtonsoft.Json.JsonConvert", "DeserializeObject"),
            Library::Origin(Kind::Json),
            "JSON"
        );
        assert!(
            classify("System.Environment", "GetEnvironmentVariable")
                == Library::Origin(Kind::External)
                && classify("UnityEngine.PlayerPrefs", "GetInt") == Library::Origin(Kind::External)
                && classify("System.IO.File", "ReadAllText") == Library::Origin(Kind::External),
            "files and environment"
        );
        assert!(
            classify("UnityEngine.Mathf", "Clamp") == Library::Transform
                && classify("Math", "Min") == Library::Transform
                && classify("System.Collections.Generic.Dictionary`2", "TryGetValue")
                    == Library::Transform,
            "math and collections transform"
        );
        assert!(
            classify("UnityEngine.Vector3", "zero") == Library::Constant
                && classify("int", "MaxValue") == Library::Constant,
            "library constants"
        );
        assert_eq!(
            classify("UnityEngine.Transform", "up"),
            Library::Origin(Kind::Engine),
            "transform.up is the engine, not a constant"
        );
        assert_eq!(
            classify("Scellecs.Morpeh.World", "Default"),
            Library::Unknown,
            "someone else's assembly is unknown"
        );
        assert!(
            clean_type("List<int>") == "List"
                && clean_type("Dictionary`2") == "Dictionary"
                && clean_type("int?") == "int"
                && clean_type("Item[]") == "Item",
            "a type without generics and ?"
        );
    }
}
