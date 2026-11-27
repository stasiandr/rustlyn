//! The value graph on examples, from simple to involved: a constant, a
//! constant through a parameter, a sum in a method, input, chains of calls,
//! fields, properties… Each example is a small project in a temporary
//! folder, a real Rustlyn session and the graph without a window
//! (`headless::graph_of`). The cursor in the text is `$0`; the sources and
//! chains of node titles are checked.

use std::path::{Path, PathBuf};
use std::sync::Arc;

use rustlyn_ide::Session;

use super::compiler::{Compiler, Outline, Target};
use super::graph::{Graph, Reach};
use super::headless;
use super::project::{Project, Projects};
use super::symbols::IndexSymbols;
use super::testing::TempDir;
use super::text::last_component;
use super::wording::{English, Unknown, Wording};

/// A compiler that writes what it was asked to stderr (`GRAPH_TRACE=1`).
struct Traced(Arc<Session>);

impl Compiler for Traced {
    fn definition(&self, path: &str, offset: usize, text: Option<&str>) -> Vec<Target> {
        let found = Compiler::definition(&*self.0, path, offset, text);
        trace(&format!(
            "definition {}@{offset} → {:?}",
            last_component(path),
            found.iter().map(|t| &t.name).collect::<Vec<_>>()
        ));
        found
    }
    fn references(&self, path: &str, offset: usize, text: Option<&str>) -> Vec<Target> {
        let found = Compiler::references(&*self.0, path, offset, text);
        trace(&format!(
            "references {}@{offset} → {:?}",
            last_component(path),
            found
                .iter()
                .map(|t| format!("{}:{}:{}", last_component(&t.path), t.line + 1, t.character))
                .collect::<Vec<_>>()
        ));
        found
    }
    fn implementations(&self, path: &str, offset: usize) -> Vec<Target> {
        let found = Compiler::implementations(&*self.0, path, offset);
        trace(&format!(
            "implementations {}@{offset} → {}",
            last_component(path),
            found.len()
        ));
        found
    }
    fn outline(&self, path: &str) -> Option<Outline> {
        let found = Compiler::outline(&*self.0, path);
        trace(&format!(
            "outline {} → {:?}",
            last_component(path),
            found.as_ref().map(|o| o.declarations.len())
        ));
        found
    }
    fn open(&self, path: &str) -> bool {
        let opened = Compiler::open(&*self.0, path);
        trace(&format!("open {} → {opened}", last_component(path)));
        opened
    }
    fn close(&self, path: &str) {
        trace(&format!("close {}", last_component(path)));
        Compiler::close(&*self.0, path);
    }
}

fn trace(line: &str) {
    if std::env::var_os("GRAPH_TRACE").is_some() {
        eprintln!("  · {line}");
    }
}

/// The graph from the value at `$0`. Files are `(path, text)`; exactly one `$0`.
struct Case {
    graph: Graph,
    tree: String,
    sources: String,
    _dir: TempDir,
}

fn case(files: &[(&str, &str)]) -> Case {
    case_with(files, Reach::default())
}

fn case_with(files: &[(&str, &str)], reach: Reach) -> Case {
    let dir = TempDir::new("graph-case");
    let root = dir.canonical();
    let mut cursor = None;
    for (name, text) in files {
        if let Some(at) = text.find("$0") {
            assert!(cursor.is_none(), "one cursor per example");
            cursor = Some(((*name).to_owned(), text[..at].encode_utf16().count()));
        }
        dir.write(name, &text.replace("$0", ""));
    }
    let (file, offset) = cursor.expect("a cursor `$0` in the example");
    let path = |name: &str| Path::new(&root).join(name).to_string_lossy().into_owned();
    let session = Arc::new(Session::new(&root, None, Vec::new()));
    let paths: Vec<PathBuf> = files
        .iter()
        .map(|(name, _)| PathBuf::from(path(name)))
        .collect();
    session.reindex(&paths);
    // The compiler finds mentions in the project's compilation.
    session.compile(&paths);
    let symbols = Arc::new(IndexSymbols::new(session.index()));
    let compiler: Arc<dyn Compiler> = Arc::new(Traced(session));
    // As a window does: the file under the cursor is open, and asked about.
    assert!(compiler.open(&path(&file)), "the file opens");
    let found = compiler
        .definition(&path(&file), offset, None)
        .into_iter()
        .next()
        .unwrap_or_else(|| {
            panic!("the compiler did not recognize the name under the cursor in {file}")
        });
    let mut project = Project::new(root.clone());
    project.compiler = Some(compiler);
    project.symbols = Some(symbols);
    let projects = Projects {
        home: Some(root),
        list: vec![project],
    };
    let graph = headless::graph_of(&found, &projects, reach).expect("the graph builds");
    let tree = headless::tree(&graph, &English);
    let sources = headless::sources_summary(&graph, &English);
    Case {
        graph,
        tree,
        sources,
        _dir: dir,
    }
}

impl Case {
    /// A chain of titles (substrings) from the value to a source.
    #[track_caller]
    fn path(&self, chain: &str) -> &Self {
        let titles: Vec<String> = chain.split("<-").map(|t| t.trim().to_owned()).collect();
        assert!(
            self.graph.has_path(&titles, &English),
            "no chain «{chain}» in the graph:\n{}\nsources: {}",
            self.tree,
            self.sources
        );
        self
    }

    /// The graph's sources on one line — exactly these.
    #[track_caller]
    fn sources(&self, expected: &str) -> &Self {
        assert_eq!(
            self.sources, expected,
            "the graph's sources:\n{}",
            self.tree
        );
        self
    }

    /// No such chain: `a` in `Sum(2, 3)` cannot have the source 3.
    #[track_caller]
    fn no_path(&self, chain: &str) -> &Self {
        let titles: Vec<String> = chain.split("<-").map(|t| t.trim().to_owned()).collect();
        assert!(
            !self.graph.has_path(&titles, &English),
            "an extra chain «{chain}» in the graph:\n{}",
            self.tree
        );
        self
    }

    /// Print the graph while writing an example (`cargo test -- --nocapture`).
    #[allow(dead_code)]
    #[track_caller]
    fn show(&self) -> &Self {
        eprintln!("{}\nsources: {}", self.tree, self.sources);
        self
    }
}
#[test]
fn s01_constant_in_a_field() {
    case(&[(
        "A.cs",
        "class A {\n    int $0x;\n    void Init() { x = 5; }\n}\n",
    )])
    .path("A.x <- A.Init <- 5")
    .sources("literal 5");
}

#[test]
fn s02_constant_through_a_local() {
    case(&[("A.cs", "class A {\n    int x;\n    void Init() {\n        int a = 5;\n        int b = a;\n        x = b;\n    }\n    int Get() { return $0x; }\n}\n")]).path("A.x <- A.Init <- 5").sources("literal 5");
}

#[test]
fn s03_named_constant() {
    case(&[(
        "A.cs",
        "class A {\n    const int Speed = 7;\n    int $0x;\n    void Init() { x = Speed; }\n}\n",
    )])
    .path("A.x <- A.Init <- A.Speed <- A.Speed <- 7")
    .sources("constant 7");
}

#[test]
fn s04_constant_passed_to_a_method() {
    case(&[(
        "A.cs",
        "class A {\n    int $0x;\n    void Set(int v) { x = v; }\n    void Init() { Set(5); }\n}\n",
    )])
    .path("A.x <- A.Set <- v <- A.Init <- 5")
    .sources("literal 5");
}

#[test]
fn s05_sum_of_two_constants_in_a_method() {
    case(&[("A.cs", "class A {\n    int $0x;\n    int Sum(int a, int b) => a + b;\n    void Init() { x = Sum(2, 3); }\n}\n")]).path("A.x <- A.Init <- Sum() <- A.Sum <- a <- A.Init <- 2").path("A.x <- A.Init <- Sum() <- A.Sum <- b <- A.Init <- 3").no_path("a <- A.Init <- 3").no_path("b <- A.Init <- 2").sources("literal 2 · literal 3");
}

#[test]
fn s06_sum_through_a_local_and_return() {
    case(&[("A.cs", "class A {\n    int $0x;\n    int Sum(int a, int b) {\n        var s = a + b;\n        return s;\n    }\n    void Init() { x = Sum(2, 3); }\n}\n")]).path("A.x <- A.Init <- Sum() <- A.Sum <- a <- A.Init <- 2").path("A.Sum <- b <- A.Init <- 3").no_path("a <- A.Init <- 3").sources("literal 2 · literal 3");
}

#[test]
fn s07_sum_in_a_method_writes_a_field() {
    case(&[("A.cs", "class A {\n    int $0x;\n    void Add(int a, int b) { x = a + b; }\n    void Init() { Add(2, 3); }\n}\n")]).path("A.x <- A.Add <- a <- A.Init <- 2").path("A.Add <- b <- A.Init <- 3").no_path("a <- A.Init <- 3").sources("literal 2 · literal 3");
}

#[test]
fn s08_input_entry_point_parameter() {
    case(&[("A.cs", "class A {\n    static string $0name;\n    static void Main(string[] args) { name = args[0]; }\n}\n")]).path("A.name <- A.Main <- args <- Main(args)").sources("files and environment Main(args)");
}

#[test]
fn s09_console_input() {
    case(&[("A.cs", "using System;\nclass A {\n    static string $0line;\n    static void Main() { line = Console.ReadLine(); }\n}\n")]).path("A.line <- A.Main <- Console.ReadLine()").sources("player input Console.ReadLine()");
}

#[test]
fn s10_chain_of_calls() {
    case(&[("A.cs", "class A {\n    int $0x;\n    void C(int c) { x = c; }\n    void B(int b) { C(b + 1); }\n    void A1(int a) { B(a * 2); }\n    void Init() { A1(10); }\n}\n")]).path("A.x <- A.C <- c <- A.B <- b <- A.A1 <- a <- A.Init <- 10").sources("literal 10");
}

#[test]
fn s11_several_calls() {
    case(&[("A.cs", "class A {\n    int $0x;\n    void Set(int v) { x = v; }\n    void One() { Set(1); }\n    void Two() { Set(2); }\n}\n")]).path("A.x <- A.Set <- v <- A.One <- 1").path("A.x <- A.Set <- v <- A.Two <- 2").sources("literal 1 · literal 2");
}

#[test]
fn s12_field_of_another_class() {
    case(&[
        ("Pawn.cs", "class Pawn {\n    public int $0Health;\n}\n"),
        (
            "Game.cs",
            "class Game {\n    void Spawn(Pawn p) { p.Health = 100; }\n}\n",
        ),
    ])
    .path("Pawn.Health <- Game.Spawn <- 100")
    .sources("literal 100");
}

#[test]
fn s13_auto_property() {
    case(&[
        (
            "Pawn.cs",
            "class Pawn {\n    public int $0Health { get; set; }\n}\n",
        ),
        (
            "Game.cs",
            "class Game {\n    void Spawn(Pawn p) { p.Health = 100; }\n}\n",
        ),
    ])
    .path("Pawn.Health <- Game.Spawn <- 100")
    .sources("literal 100");
}

#[test]
fn s14_property_with_a_field() {
    case(&[
        ("Pawn.cs", "class Pawn {\n    int _health;\n    public int Health { get => _health; set => _health = value; }\n    public int Get() => $0_health;\n}\n"),
        ("Game.cs", "class Game {\n    void Spawn(Pawn p) { p.Health = 100; }\n}\n"),
    ]).path("Pawn._health <- Pawn.Health <- Pawn.Health <- Game.Spawn <- 100").sources("literal 100");
}

#[test]
fn s15_constructor() {
    case(&[
        ("Pawn.cs", "class Pawn {\n    readonly int $0health;\n    public Pawn(int health) { this.health = health; }\n}\n"),
        ("Game.cs", "class Game {\n    Pawn Spawn() => new Pawn(42);\n}\n"),
    ]).path("Pawn.health <- Pawn.Pawn <- health <- Game.Spawn <- 42").sources("literal 42");
}

#[test]
fn s16_compound_assignment() {
    case(&[(
        "A.cs",
        "class A {\n    int $0x = 1;\n    void Tick() { x += 2; }\n}\n",
    )])
    .path("A.x <- A.Tick <- 2")
    .path("A.x <- A.x <- 1")
    .sources("literal 2 · initial value 1");
}

#[test]
fn s17_ternary() {
    case(&[(
        "A.cs",
        "class A {\n    int $0x;\n    void Set(bool fast) { x = fast ? 10 : 3; }\n}\n",
    )])
    .path("A.x <- A.Set <- 10")
    .path("A.x <- A.Set <- 3")
    .sources("literal 10 · literal 3");
}

#[test]
fn s18_call_as_root() {
    case(&[("A.cs", "class A {\n    int x = 4;\n    int Get() => x * 2;\n    void Use() { var y = $0Get(); }\n}\n")]).path("Get() <- A.Get <- A.x <- A.x <- 4").sources("initial value 4");
}

#[test]
fn s19_recursion() {
    case(&[("A.cs", "class A {\n    int $0x;\n    void Set(int v) { if (v > 0) Set(v - 1); x = v; }\n    void Init() { Set(3); }\n}\n")]).path("A.x <- A.Set <- v <- A.Init <- 3").sources("literal 3");
}

#[test]
fn s20_interface() {
    case(&[(
        "A.cs",
        "interface ISource { int Value(); }\nclass Five : ISource { public int Value() => 5; }\nclass A {\n    int $0x;\n    void Init(ISource s) { x = s.Value(); }\n}\n",
    )]).path("A.x <- A.Init <- s.Value() <- Five.Value <- 5").sources("literal 5");
}

#[test]
fn s21_out_parameter() {
    case(&[("A.cs", "class A {\n    int $0x;\n    static bool Read(out int v) { v = 9; return true; }\n    void Init() { Read(out x); }\n}\n")]).path("A.x <- A.Init <- Read.v <- A.Read <- 9").sources("literal 9");
}

#[test]
fn s22_static_field_through_the_type() {
    case(&[
        ("Config.cs", "static class Config {\n    public static int $0Max;\n}\n"),
        ("Boot.cs", "class Boot {\n    void Run() { Config.Max = Limits.Default; }\n}\nstatic class Limits { public const int Default = 64; }\n"),
    ]).path("Config.Max <- Boot.Run <- Limits.Default <- Limits.Default <- 64").sources("constant 64");
}

#[test]
fn s23_sum_of_constants_directly() {
    case(&[(
        "A.cs",
        "class A {\n    int $0x;\n    void Init() { x = 2 + 3; }\n}\n",
    )])
    .path("A.x <- A.Init <- 2 + 3")
    .sources("literal 2 + 3");
}

#[test]
fn s24_method_of_another_class_returns_a_field() {
    case(&[
        ("Car.cs", "class Car {\n    float speed;\n    public Car(float speed) { this.speed = speed; }\n    public float GetSpeed() => speed;\n}\n"),
        ("Race.cs", "class Race {\n    float $0top;\n    void Start() {\n        var car = new Car(120f);\n        top = car.GetSpeed();\n    }\n}\n"),
    ]).path("Race.top <- Race.Start <- car.GetSpeed() <- Car.GetSpeed <- Car.speed <- Car.Car <- speed <- Race.Start <- 120f").sources("literal 120f");
}

#[test]
fn s25_computed_property() {
    case(&[("A.cs", "class A {\n    int a = 1;\n    int b;\n    public int Total => a + b;\n    void Init() { b = 4; }\n    int Use() => $0Total;\n}\n")]).path("A.Total <- A.Total <- A.a <- A.a <- 1").path("A.Total <- A.Total <- A.b <- A.Init <- 4").sources("initial value 1 · literal 4");
}

#[test]
fn s26_object_initializer() {
    case(&[
        ("Pawn.cs", "class Pawn {\n    public int $0Health;\n}\n"),
        (
            "Game.cs",
            "class Game {\n    Pawn Spawn() => new Pawn { Health = 75 };\n}\n",
        ),
    ])
    .path("Pawn.Health <- Game.Spawn <- 75")
    .sources("literal 75");
}

#[test]
fn s27_lambda() {
    case(&[("A.cs", "using System;\nclass A {\n    int $0x;\n    void Init() {\n        Func<int> make = () => 5;\n        x = make();\n    }\n}\n")]).path("A.x <- A.Init <- 5").sources("literal 5");
}

#[test]
fn s28_collection() {
    case(&[("A.cs", "using System.Collections.Generic;\nclass A {\n    List<int> $0items = new List<int>();\n    void Init() { items.Add(5); items.Add(6); }\n}\n")]).path("A.items <- A.Init <- 5").path("A.items <- A.Init <- 6").sources("literal 5 · literal 6 · initial value new List<int>()");
}

#[test]
fn s29_static_method_with_arguments() {
    case(&[
        ("MathUtil.cs", "static class MathUtil {\n    public static int Clamp(int v, int min, int max) => v < min ? min : v > max ? max : v;\n}\n"),
        ("A.cs", "class A {\n    int $0x;\n    void Set(int raw) { x = MathUtil.Clamp(raw, 0, 10); }\n    void Init() { Set(42); }\n}\n"),
    ]).path("A.x <- A.Set <- MathUtil.Clamp() <- MathUtil.Clamp <- v <- A.Set <- raw <- A.Init <- 42").path("MathUtil.Clamp <- min <- A.Set <- 0").path("MathUtil.Clamp <- max <- A.Set <- 10").sources("literal 42 · literal 0 · literal 10");
}

#[test]
fn s30_generic_method() {
    case(&[("A.cs", "class A {\n    int $0x;\n    static T Id<T>(T v) => v;\n    void Init() { x = Id(5); }\n}\n")]).path("A.x <- A.Init <- Id() <- A.Id <- v <- A.Init <- 5").sources("literal 5");
}

#[test]
fn s31_overridden_property() {
    case(&[(
        "A.cs",
        "abstract class Unit { public abstract int Speed { get; } }\nclass Fast : Unit { public override int Speed => 7; }\nclass A {\n    int $0x;\n    void Init(Unit u) { x = u.Speed; }\n}\n",
    )]).path("A.x <- A.Init <- Unit.Speed <- Fast.Speed <- 7").sources("literal 7");
}

#[test]
fn s32_event_subscription() {
    case(&[(
        "A.cs",
        "using System;\nclass Bus {\n    public event Action<int> Changed;\n    public void Fire() { Changed?.Invoke(5); }\n}\nclass A {\n    int $0x;\n    void Init(Bus bus) { bus.Changed += OnChanged; }\n    void OnChanged(int v) { x = v; }\n}\n",
    )]).path("A.x <- A.OnChanged <- v <- Bus.Fire <- 5").sources("literal 5");
}

#[test]
fn s33_named_argument_and_default() {
    case(&[("A.cs", "class A {\n    int $0x;\n    void Set(int v = 3) { x = v; }\n    void One() { Set(v: 5); }\n    void Two() { Set(); }\n}\n")]).path("A.x <- A.Set <- v <- A.One <- 5").path("A.x <- A.Set <- v <- A.Set <- 3").sources("literal 5 · default 3");
}

#[test]
fn s34_async() {
    case(&[("A.cs", "using System.Threading.Tasks;\nclass A {\n    int $0x;\n    async Task<int> Load() { await Task.Delay(1); return 5; }\n    async Task Init() { x = await Load(); }\n}\n")]).path("A.x <- A.Init <- Load() <- A.Load <- 5").sources("literal 5");
}

#[test]
fn s35_switch_expression() {
    case(&[("A.cs", "class A {\n    int $0x;\n    void Set(int mode) { x = mode switch { 1 => 10, 2 => 20, _ => 0 }; }\n}\n")]).path("A.x <- A.Set <- 10").path("A.Set <- 20").path("A.Set <- 0").sources("literal 10 · literal 20 · literal 0");
}

#[test]
fn s36_increment() {
    case(&[("A.cs", "class A {\n    int $0count;\n    void Hit() { count++; }\n    void Reset() { count = 0; }\n}\n")]).path("A.count <- A.Hit").path("A.count <- A.Reset <- 0").sources("literal 0");
}

#[test]
fn s37_tuple() {
    case(&[(
        "A.cs",
        "class A {\n    int $0x;\n    int y;\n    void Init() { (x, y) = (1, 2); }\n}\n",
    )])
    .path("A.x <- A.Init <- 1")
    .no_path("A.Init <- 2")
    .sources("literal 1");
}

#[test]
fn s38_chain_across_files() {
    case(&[
        ("Settings.cs", "class Settings {\n    public const float BaseSpeed = 3.5f;\n    public float Multiplier { get; set; } = 2f;\n}\n"),
        ("Mover.cs", "class Mover {\n    float speed;\n    public Mover(Settings s) { speed = Compute(s); }\n    float Compute(Settings s) => Settings.BaseSpeed * s.Multiplier;\n    public float $0Speed => speed;\n}\n"),
    ]).path("Mover.Speed <- Mover.Speed <- Mover.speed <- Mover.Mover <- Compute() <- Mover.Compute <- Settings.BaseSpeed <- Settings.BaseSpeed <- 3.5f").path("Mover.Compute <- Settings.Multiplier <- Settings.Multiplier <- 2f").sources("constant 3.5f · initial value 2f");
}

#[test]
fn s39_local_as_root() {
    case(&[("A.cs", "class A {\n    int Calc(int a) {\n        var $0r = a * 2;\n        if (a > 10) r = 0;\n        return r;\n    }\n    void Init() { Calc(7); }\n}\n")]).path("r <- A.Calc <- a <- A.Init <- 7").path("r <- A.Calc <- 0").sources("literal 0 · literal 7");
}

#[test]
fn s40_parameter_as_root() {
    case(&[("A.cs", "class A {\n    void Set(int $0v) { }\n    void One() { Set(1); }\n    void Two(int k) { Set(k); }\n    void Three() { Two(3); }\n}\n")]).path("v <- A.One <- 1").path("v <- A.Two <- k <- A.Three <- 3").sources("literal 1 · literal 3");
}

#[test]
fn s41_struct_through_a_copy() {
    case(&[("A.cs", "struct Pos { public int x; }\nclass A {\n    Pos $0pos;\n    void Move() {\n        var p = pos;\n        p.x = 3;\n        pos = p;\n    }\n}\n")]).path("A.pos <- A.Move <- 3").sources("literal 3");
}

#[test]
fn s42_base_constructor() {
    case(&[(
        "A.cs",
        "class Unit {\n    protected int $0hp;\n    public Unit(int hp) { this.hp = hp; }\n}\nclass Tank : Unit {\n    public Tank() : base(500) { }\n}\n",
    )]).path("Unit.hp <- Unit.Unit <- hp <- Tank.Tank <- 500").sources("literal 500");
}

#[test]
fn s43_factory() {
    case(&[(
        "A.cs",
        "class Pawn {\n    public int $0Health;\n    public static Pawn Create(int h) => new Pawn { Health = h };\n}\nclass Game {\n    void Spawn() { var p = Pawn.Create(10); }\n}\n",
    )]).path("Pawn.Health <- Pawn.Create <- h <- Game.Spawn <- 10").sources("literal 10");
}

#[test]
fn s44_setter_with_logic() {
    case(&[(
        "A.cs",
        "using System;\nclass Pawn {\n    int $0_hp;\n    const int Max = 100;\n    public int Hp { get => _hp; set { _hp = Math.Clamp(value, 0, Max); } }\n}\nclass Game {\n    void Hit(Pawn p) { p.Hp = 250; }\n}\n",
    )]).path("Pawn._hp <- Pawn.Hp <- Pawn.Hp <- Game.Hit <- 250").path("Pawn._hp <- Pawn.Hp <- Pawn.Max <- Pawn.Max <- 100").sources("literal 250 · constant 100");
}

#[test]
fn s45_dictionary() {
    case(&[("A.cs", "using System.Collections.Generic;\nclass A {\n    Dictionary<string, int> $0values = new();\n    void Init() { values[\"hp\"] = 5; }\n}\n")]).path("A.values <- A.Init <- 5").sources("literal 5 · initial value new()");
}

#[test]
fn s46_field_from_a_field() {
    case(&[(
        "A.cs",
        "class A {\n    int max = 100;\n    int $0hp;\n    void Reset() { hp = max; }\n}\n",
    )])
    .path("A.hp <- A.Reset <- A.max <- A.max <- 100")
    .sources("initial value 100");
}

#[test]
fn s47_chain_across_classes() {
    case(&[
        ("Input.cs", "using System;\nclass PlayerInput {\n    public string Read() => Console.ReadLine();\n}\n"),
        ("Controller.cs", "class Controller {\n    readonly Model model;\n    public Controller(Model m) { model = m; }\n    public void Tick(PlayerInput input) { model.SetName(input.Read()); }\n}\n"),
        ("Model.cs", "class Model {\n    public string Name { get; private set; }\n    public void SetName(string name) { Name = name.Trim(); }\n}\n"),
        ("View.cs", "class View {\n    string $0label;\n    public void Render(Model m) { label = \"Hi, \" + m.Name; }\n}\n"),
    ]).path("View.label <- View.Render <- Model.Name <- Model.SetName <- name <- Controller.Tick <- input.Read() <- PlayerInput.Read <- Console.ReadLine()").sources("player input Console.ReadLine()");
}

#[test]
fn s48_unity_time() {
    case(&[("A.cs", "using UnityEngine;\nclass Mover {\n    public float speed = 2f;\n    float $0step;\n    void Update() { step = speed * Time.deltaTime; }\n}\n")]).path("Mover.step <- Mover.Update <- Time.deltaTime").path("Mover.Update <- Mover.speed <- Mover.speed <- 2f").sources("time Time.deltaTime · initial value 2f");
}

#[test]
fn s49_unity_random() {
    case(&[("A.cs", "using UnityEngine;\nclass Spawner {\n    int $0count;\n    void Start() { count = Random.Range(1, 5); }\n}\n")]).path("Spawner.count <- Spawner.Start <- Random.Range()").sources("random number Random.Range()");
}

#[test]
fn s50_unity_input_and_saves() {
    case(&[(
        "A.cs",
        "using UnityEngine;\nclass Player {\n    float $0move;\n    int best;\n    void Update() { move = Input.GetAxis(\"Horizontal\"); }\n    void Load() { best = PlayerPrefs.GetInt(\"best\"); }\n}\n",
    )]).path("Player.move <- Player.Update <- Input.GetAxis()").sources("player input Input.GetAxis()");
}

#[test]
fn s51_ref_parameter() {
    case(&[("A.cs", "class A {\n    int $0x;\n    static void Inc(ref int v) { v += 1; }\n    void Tick() { Inc(ref x); }\n    void Init() { x = 10; }\n}\n")]).path("A.x <- A.Tick <- Inc.v <- A.Inc <- 1").path("A.x <- A.Init <- 10").sources("literal 10 · literal 1");
}

#[test]
fn s52_interpolation() {
    case(&[("A.cs", "class A {\n    string $0title;\n    int id = 7;\n    void Init() { title = $\"Player {id}\"; }\n}\n")]).path("A.title <- A.Init <- A.id <- A.id <- 7").sources("initial value 7");
}

#[test]
fn s53_null_coalescing() {
    case(&[("A.cs", "class A {\n    int? maybe;\n    int $0x;\n    void Init() { x = maybe ?? 7; }\n    void Set() { maybe = 3; }\n}\n")]).path("A.x <- A.Init <- 7").path("A.x <- A.Init <- A.maybe <- A.Set <- 3").sources("literal 7 · literal 3");
}

#[test]
fn s54_chain_of_members() {
    case(&[(
        "A.cs",
        "class C { public int $0c; }\nclass B { public C b = new C(); }\nclass A {\n    B a = new B();\n    void Init() { a.b.c = 5; }\n}\n",
    )]).path("C.c <- A.Init <- 5").sources("literal 5");
}

#[test]
fn s55_generic_class() {
    case(&[(
        "A.cs",
        "class Box<T> { public T $0Value; }\nclass A {\n    void Init() { var box = new Box<int> { Value = 3 }; }\n}\n",
    )]).path("Box.Value <- A.Init <- 3").sources("literal 3");
}

#[test]
fn s56_virtual_method() {
    case(&[(
        "A.cs",
        "class Weapon { public virtual int Damage() => 1; }\nclass Sword : Weapon { public override int Damage() => 2; }\nclass A {\n    int $0dmg;\n    void Hit(Weapon w) { dmg = w.Damage(); }\n}\n",
    )]).path("A.dmg <- A.Hit <- w.Damage() <- Weapon.Damage <- 1").path("w.Damage() <- Sword.Damage <- 2").sources("literal 1 · literal 2");
}

#[test]
fn s57_mutual_cycle() {
    case(&[("A.cs", "class A {\n    int $0a;\n    int b;\n    void One() { a = b; }\n    void Two() { b = a + 1; }\n    void Init() { a = 0; }\n}\n")]).path("A.a <- A.One <- A.b <- A.Two <- A.a").path("A.a <- A.Init <- 0").sources("literal 0");
}

#[test]
fn s58_linq() {
    case(&[(
        "A.cs",
        "using System.Linq;\nusing System.Collections.Generic;\nclass A {\n    List<int> items = new List<int> { 1, 2, 3 };\n    int $0total;\n    void Init() { total = items.Select(i => i * 2).Sum(); }\n}\n",
    )]).path("A.total <- A.Init <- A.items <- A.items <- 1").path("A.items <- A.items <- 3").sources("initial value 1 · initial value 2 · initial value 3");
}

#[test]
fn s59_static_readonly_and_enum() {
    case(&[(
        "A.cs",
        "enum Mode { Easy, Hard }\nclass Rules { public static readonly int Lives = 3; }\nclass A {\n    Mode $0mode;\n    int lives;\n    void Init(bool hard) { mode = hard ? Mode.Hard : Mode.Easy; lives = Rules.Lives; }\n}\n",
    )]).path("A.mode <- A.Init <- Mode.Hard").path("A.mode <- A.Init <- Mode.Easy").sources("enum value Mode.Hard · enum value Mode.Easy");
}

#[test]
fn s60_value_from_a_call_with_a_field_argument() {
    case(&[(
        "A.cs",
        "class Pawn { public int Health = 30; }\nclass A {\n    static int Get(Pawn p) => p.Health;\n    int $0shown;\n    void Show(Pawn p) { shown = Get(p); }\n}\n",
    )]).path("A.shown <- A.Show <- Get() <- A.Get <- Pawn.Health <- Pawn.Health <- 30").sources("initial value 30");
}

// MARK: - writes through references, constructors and indexers
//
// Each example is written so that the value its field gets is known by
// construction: the literal passed or assigned is the only one.

#[test]
fn s61_ref_argument_through_this() {
    case(&[(
        "A.cs",
        "class A {\n    int $0T;\n    void Set() { Helper(ref this.T); }\n    static void Helper(ref int x) { x = 3001; }\n}\n",
    )]).path("A.T <- A.Set <- Helper.x <- A.Helper <- 3001").sources("literal 3001");
}

#[test]
fn s62_ref_argument_through_another_object() {
    case(&[(
        "A.cs",
        "class A {\n    int $0T;\n    void Set(A o) { Helper(ref o.T); }\n    static void Helper(ref int x) { x = 3002; }\n}\n",
    )]).sources("literal 3002");
}

#[test]
fn s63_out_argument_through_this() {
    case(&[(
        "A.cs",
        "class A {\n    int $0T;\n    void Set() { Helper(out this.T); }\n    static void Helper(out int x) { x = 3003; }\n}\n",
    )]).sources("literal 3003");
}

#[test]
fn s64_ref_local_is_another_name_for_the_field() {
    case(&[(
        "A.cs",
        "class A {\n    int $0T;\n    void Set() { ref int r = ref T; r = 3005; }\n}\n",
    )])
    .sources("literal 3005");
}

#[test]
fn s65_ref_local_of_this_field() {
    case(&[(
        "A.cs",
        "class A {\n    int $0T;\n    void Set() { ref int r = ref this.T; r = 3006; }\n}\n",
    )])
    .sources("literal 3006");
}

#[test]
fn s66_interlocked_exchange() {
    case(&[(
        "A.cs",
        "using System.Threading;\nclass A {\n    int $0T;\n    void Set() { Interlocked.Exchange(ref T, 2003); }\n}\n",
    )]).sources("literal 2003");
}

#[test]
fn s67_interlocked_compare_exchange() {
    case(&[(
        "A.cs",
        "using System.Threading;\nclass A {\n    int $0T;\n    void Set() { Interlocked.CompareExchange(ref T, 2004, 0); }\n}\n",
    )]).sources("literal 2004");
}

#[test]
fn s68_volatile_write() {
    case(&[(
        "A.cs",
        "using System.Threading;\nclass A {\n    int $0T;\n    void Set() { Volatile.Write(ref T, 2005); }\n}\n",
    )]).sources("literal 2005");
}

#[test]
fn s69_interlocked_add() {
    case(&[(
        "A.cs",
        "using System.Threading;\nclass A {\n    int $0T;\n    void Set() { Interlocked.Add(ref T, 2006); }\n}\n",
    )]).sources("literal 2006");
}

#[test]
fn s70_ref_return_written_by_its_caller() {
    case(&[(
        "A.cs",
        "class A {\n    int $0T;\n    ref int Slot() { return ref T; }\n    void Set() { Slot() = 2002; }\n}\n",
    )]).path("A.T <- A.Slot <- 2002").sources("literal 2002");
}

#[test]
fn s71_ref_return_taken_by_a_ref_local() {
    case(&[(
        "A.cs",
        "class A {\n    int $0T;\n    ref int Slot() => ref T;\n    void Set() { ref int r = ref Slot(); r = 2007; }\n}\n",
    )]).sources("literal 2007");
}

#[test]
fn s72_compound_assignment_through_a_ref_parameter() {
    case(&[(
        "A.cs",
        "class A {\n    int $0T;\n    void Set() { Helper(ref this.T); }\n    static void Helper(ref int x) { x += 2014; }\n}\n",
    )]).sources("literal 2014");
}

#[test]
fn s73_primary_constructor_parameter_from_its_callers() {
    case(&[(
        "A.cs",
        "class Cfg(int t) { public int $0T = t; }\nclass Use { Cfg Make() { return new Cfg(4001); } }\n",
    )]).path("Cfg.T <- ctor.t <- Use.Make <- 4001").sources("literal 4001");
}

#[test]
fn s74_positional_record_parameter_from_its_callers() {
    case(&[(
        "A.cs",
        "record Rec(int $0V);\nclass Use { Rec Make() { return new Rec(4002); } }\n",
    )])
    .sources("literal 4002");
}

#[test]
fn s75_indexer_setter_from_the_assignments_of_the_indexer() {
    case(&[(
        "A.cs",
        "class A {\n    int $0T;\n    int this[int i] { set { T = value; } }\n    void Set() { this[0] = 1030; }\n}\n",
    )]).sources("literal 1030");
}

#[test]
fn s76_indexer_assigned_from_another_class() {
    case(&[(
        "A.cs",
        "class A {\n    int $0T;\n    public int this[int i] { set { T = value; } }\n}\nclass B { void Run(A a) { a[1] = 1031; } }\n",
    )]).sources("literal 1031");
}

#[test]
fn s77_a_reference_that_escapes_is_said_to() {
    let found = case(&[(
        "A.cs",
        "using System.Threading;\nclass A {\n    int $0T;\n    void Set() { Interlocked.Increment(ref T); }\n}\n",
    )]);
    // The graph says where the reference goes and that it is not followed;
    // the words for the reader are the subtitle's.
    assert!(
        found.tree.contains("Interlocked.Increment(ref …) [unknown"),
        "the value may be written through a reference:\n{}",
        found.tree
    );
    assert!(
        English
            .unknown(Unknown::ThroughReference)
            .contains("may be written through it"),
        "the way it is said"
    );
    assert!(
        !found.tree.contains("no writes were found"),
        "not an assertion of no writes:\n{}",
        found.tree
    );
}

#[test]
fn s78_primary_constructor_parameter_that_members_capture() {
    // A parameter the members use is a field of the compiler's making; the
    // callers of the constructor write it all the same.
    case(&[(
        "A.cs",
        "class E(int t) { public int $0T = t; public int G() => t; }\nclass Use { E Make() { return new E(4003); } }\n",
    )])
    .path("E.T <- E.<t>P <- Use.Make <- 4003")
    .sources("literal 4003");
}

#[test]
fn s79_captured_parameter_asked_for_by_itself() {
    case(&[(
        "A.cs",
        "class E(int $0t) { public int G() => t; }\nclass Use { E Make() { return new E(4004); } }\n",
    )])
    .sources("literal 4004");
}

#[test]
fn s80_captured_parameter_of_a_struct_and_one_not_captured() {
    case(&[(
        "A.cs",
        "struct S(int t) { public int $0T = t; public int G() => t + 1; }\nclass Use { S Make() { return new S(4005); } }\n",
    )])
    .sources("literal 4005");
    case(&[(
        "A.cs",
        "class P(int t) { public int $0T = t; }\nclass Use { P Make() { return new P(4006); } }\n",
    )])
    .sources("literal 4006");
}

#[test]
fn s81_captured_parameter_of_two_with_two_callers() {
    let found = case(&[(
        "A.cs",
        "class E(int a, int b) { public int $0B = b; public int G() => a + b; }\nclass Use { void M() { var x = new E(1, 4007); var y = new E(2, 4008); } }\n",
    )]);
    let tree = &found.tree;
    assert!(tree.contains("4007") && tree.contains("4008"), "{tree}");
    assert!(
        !tree.contains("literal 1\n") && !tree.contains("literal 2\n"),
        "{tree}"
    );
}
