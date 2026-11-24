use super::*;
use crate::value::ecs::{StashCall, stash_calls, stash_field_writes, stash_of_local};

fn utf16(text: &str) -> Vec<u16> {
    text.encode_utf16().collect()
}

/// The range of the first `what` in `s` (UTF-16), from `from`.
fn range(s: &str, what: &str, from: usize) -> R {
    let units = utf16(s);
    let needle = utf16(what);
    let at = (from..=units.len().saturating_sub(needle.len()))
        .find(|&i| units[i..i + needle.len()] == needle[..])
        .expect("present");
    R::new(at, needle.len())
}

fn first(s: &str, what: &str) -> R {
    range(s, what, 0)
}

/// A name `length` long at the start of the first `pattern`.
fn name(s: &str, pattern: &str, length: usize, from: usize) -> R {
    R::new(range(s, pattern, from).location, length)
}

fn text(units: &[u16], r: Option<R>) -> Option<String> {
    r.map(|r| string(units, r))
}

fn whole(units: &[u16]) -> R {
    R::new(0, units.len())
}

#[test]
fn writes_and_reads() {
    let access_of = |line: &str, name: &str| access(&utf16(line), first(line, name));
    let rhs_text = |line: &str, name: &str| -> Option<String> {
        match access_of(line, name) {
            Access::Write { rhs: Some(rhs), .. } => Some(string(&utf16(line), rhs)),
            _ => None,
        }
    };
    assert_eq!(
        rhs_text("health.Value = d.Amount;", "Value").as_deref(),
        Some("d.Amount"),
        "assignment is a write, the right-hand side up to ;"
    );
    assert_eq!(
        access_of("if (health.Value == 0) return;", "Value"),
        Access::Read,
        "== is a read"
    );
    assert_eq!(
        access_of("var x = c.Value;", "Value"),
        Access::Read,
        "right of = is a read"
    );
    assert_eq!(
        access_of("Func<int> f = () => Value;", "Value"),
        Access::Read,
        "in a lambda it is a read"
    );
    assert_eq!(
        access_of("c.Count++;", "Count"),
        Access::Write {
            rhs: None,
            compound: true
        },
        "++ after is a write"
    );
    assert_eq!(
        access_of("++c.Count;", "Count"),
        Access::Write {
            rhs: None,
            compound: true
        },
        "++ before a chain is a write"
    );
    assert!(
        matches!(
            access_of("hp.Value -= damage * 2;", "Value"),
            Access::Write { compound: true, .. }
        ) && rhs_text("hp.Value -= damage * 2;", "Value").as_deref() == Some("damage * 2"),
        "-= is a compound write"
    );
    assert_eq!(
        rhs_text(
            "_stash.Set(e, new Health { Value = max, Regen = 1 });",
            "Value"
        )
        .as_deref(),
        Some("max"),
        "initializer: up to a comma of its level"
    );
    assert_eq!(
        rhs_text(
            "_stash.Set(e, new Health { Value = Math.Max(a, b) });",
            "Value"
        )
        .as_deref(),
        Some("Math.Max(a, b)"),
        "a comma inside a call does not cut the right-hand side"
    );
    assert_eq!(
        rhs_text("new Health { Regen = 1, Value = x }", "Value").as_deref(),
        Some("x"),
        "the last in an initializer: up to }}"
    );
    assert_eq!(
        access_of("Parse(s, out stats.Level);", "Level"),
        Access::Write {
            rhs: None,
            compound: false
        },
        "out is a write"
    );
    assert_eq!(
        rhs_text("d.Name = \"a;b\";", "Name").as_deref(),
        Some("\"a;b\""),
        "; in a string does not cut the right-hand side"
    );
    assert_eq!(
        rhs_text(
            "var map = new Dictionary<(Rarity r, Kind k), int>();",
            "map"
        )
        .as_deref(),
        Some("new Dictionary<(Rarity r, Kind k), int>()"),
        "commas in generic arguments do not cut the right-hand side"
    );
    assert_eq!(
        rhs_text("int a = b < c, d = e;", "a").as_deref(),
        Some("b < c"),
        "a comparison is not a generic"
    );
}

fn chains(expr: &str) -> Vec<String> {
    let units = utf16(expr);
    sources(&units, whole(&units))
        .iter()
        .map(|s| format!("{}{}", s.chain, if s.call { "()" } else { "" }))
        .collect()
}

#[test]
fn sources_of_expressions() {
    assert_eq!(
        chains("stats.Damage * mult"),
        ["stats.Damage", "mult"],
        "a chain and a single name"
    );
    assert_eq!(
        chains("Math.Max(a.B, 0)"),
        ["Math.Max()", "a.B"],
        "a call and an argument"
    );
    assert_eq!(
        chains("new Vector3(x, y, 0)"),
        ["Vector3()", "x", "y"],
        "new is not a source, the constructor is a call"
    );
    assert_eq!(
        chains("player?.Stats.Hp ?? 0"),
        ["player.Stats.Hp"],
        "?. is the same chain"
    );
    assert_eq!(chains("\"hp: \" + hp"), ["hp"], "strings are skipped");
    assert_eq!(
        chains("list.Get<int>(i)"),
        ["list.Get()", "i"],
        "a generic call"
    );
    let units = utf16("stats.Damage * mult");
    assert_eq!(
        string(&units, sources(&units, whole(&units))[0].range),
        "Damage",
        "the chain's last link is asked about"
    );
}

#[test]
fn conditions_and_calls() {
    let nested = utf16("c.Pos.x = 1;");
    let pos = first("c.Pos.x = 1;", "Pos");
    assert_eq!(
        access(&nested, pos),
        Access::Write {
            rhs: Some(R::new(10, 1)),
            compound: true
        },
        "a write into a nested field is a compound write of the struct itself"
    );
    assert_eq!(
        access(&utf16("c.Pos.Normalize();"), pos),
        Access::Read,
        "a method call on the nested one is not a write"
    );

    let loop_text = "void OnUpdate() {\n foreach (ref readonly var d in _networkFilter)\n {\n  x.A = d.B;\n }\n y = 1;\n}";
    let u = utf16(loop_text);
    let inside = first(loop_text, "x.A").location;
    assert_eq!(
        text(&u, enclosing_foreach(&u, whole(&u), inside)).as_deref(),
        Some("_networkFilter"),
        "a write inside foreach: its source"
    );
    let outside = first(loop_text, "y = 1").location;
    assert_eq!(
        enclosing_foreach(&u, whole(&u), outside),
        None,
        "after the loop it is not in it"
    );
    let single = utf16("foreach (var e in _filter) _hp.Set(e);");
    assert_eq!(
        text(&single, enclosing_foreach(&single, whole(&single), 30)).as_deref(),
        Some("_filter"),
        "a body without braces"
    );

    let filter =
        utf16("_filter = World.Filter.With<Health>().With<Game.Pawn>().Without<Dead>().Build();");
    let (with, without) = filter_components(&filter, whole(&filter));
    assert!(
        with == ["Health", "Pawn"] && without == ["Dead"],
        "With and Without of the filter"
    );

    let call = utf16("Apply(ref target, amount: dmg * 2, Get<int>(a, b));");
    let apply = R::new(0, 5);
    assert_eq!(
        text(&call, argument(&call, apply, 0)).as_deref(),
        Some("target"),
        "ref removed"
    );
    assert_eq!(
        text(&call, argument(&call, apply, 1)).as_deref(),
        Some("dmg * 2"),
        "the argument's name removed"
    );
    assert_eq!(
        text(&call, argument(&call, apply, 2)).as_deref(),
        Some("Get<int>(a, b)"),
        "commas inside are not a boundary"
    );
    assert_eq!(argument(&call, apply, 3), None, "no such argument");

    let body = utf16("int Damage() { if (crit) return base * 2; return base; }");
    let returns: Vec<String> = returned_expressions(&body, whole(&body))
        .iter()
        .map(|&r| string(&body, r))
        .collect();
    assert_eq!(returns, ["base * 2", "base"], "all returns");
    let arrow = utf16("int Damage => stats.Base + bonus;");
    let returns: Vec<String> = returned_expressions(&arrow, whole(&arrow))
        .iter()
        .map(|&r| string(&arrow, r))
        .collect();
    assert_eq!(returns, ["stats.Base + bonus"], "an expression body");

    let stash = utf16(
        "_health.Set(e, new Health { }); _health.Remove(e); _healthX.Set(a); if (_health.Has(e)) {}",
    );
    let found: Vec<StashCall> = stash_calls(&stash, "_health").iter().map(|c| c.1).collect();
    assert_eq!(
        found,
        [StashCall::Set, StashCall::Remove],
        "Set and Remove, not Has and not another stash"
    );
}

#[test]
fn locals() {
    let body = "void Apply() {\n  var mult = crit ? 2 : 1;\n  int dmg = stats.Damage * mult;\n  hp.Value -= dmg;\n}";
    let units = utf16(body);
    let method = whole(&units);
    let use_at = first(body, "dmg;").location;
    assert_eq!(
        text(&units, local_initializer(&units, "dmg", method, use_at)).as_deref(),
        Some("stats.Damage * mult"),
        "int dmg = … is a declaration"
    );
    assert_eq!(
        text(&units, local_initializer(&units, "mult", method, use_at)).as_deref(),
        Some("crit ? 2 : 1"),
        "var mult = … is a declaration"
    );
    assert_eq!(
        local_initializer(&units, "Value", method, units.len()),
        None,
        "hp.Value -= … is not a declaration"
    );
}

fn all_sources(expr: &str) -> (Vec<u16>, Vec<Source>) {
    let units = utf16(expr);
    let found = sources(&units, whole(&units));
    (units, found)
}

#[test]
fn lambdas_switch_and_members() {
    assert_eq!(
        chains("Load(path, static (s, x) => { if (x) return; s.Done(); }) + bonus"),
        ["Load()", "path", "bonus"],
        "lambda parameters and body are not sources"
    );
    assert_eq!(
        chains("items.Find(i => i.Alive)"),
        ["items.Find()"],
        "a lambda expression without parentheses"
    );
    assert_eq!(
        chains("state switch { State.Idle => idle, _ => busy }"),
        ["state", "idle", "busy"],
        "switch arms are sources, patterns are not"
    );
    assert_eq!(
        chains("this.speed * base.Scale"),
        ["speed", "Scale"],
        "this. and base. dropped"
    );
    assert_eq!(
        chains("TryGet(key, out _) ? hit : _ + miss"),
        ["TryGet()", "key", "hit", "miss"],
        "_ is not a source"
    );
    assert_eq!(
        chains("new Dictionary<(Rarity rarity, int size), int>(capacity)"),
        ["Dictionary()", "capacity"],
        "generic arguments are types, not sources"
    );
    assert_eq!(
        chains("new Health { Value = max, Regen = rate }"),
        ["Health", "max", "rate"],
        "targets in an initializer are not sources"
    );
    assert_eq!(
        chains("Spawn(model: m, radius: alive ? r : 0)"),
        ["Spawn()", "m", "alive", "r"],
        "argument names are not sources, branches of ?: are"
    );
    assert!(
        all_sources("new Vector3(x, 0)").1[0].constructs,
        "new T(…) is marked"
    );
    let (_, member) = all_sources("_hp.Get(e).Value");
    let names: Vec<&str> = member.iter().map(|s| s.chain.as_str()).collect();
    assert!(
        names == ["e", "Value"]
            && member[1].receiver.as_deref() == Some("_hp.Get")
            && member[1].member,
        "a member of a call's result: the call is not a source, it is kept as the receiver"
    );
    let (units, chain) = all_sources("a.b.c");
    assert_eq!(
        text(&units, chain[0].head).as_deref(),
        Some("a"),
        "the chain's head"
    );
}

#[test]
fn parameters_locals_and_properties() {
    let method = "void Apply<T>(int amount, ref Stats s) where T : struct { }";
    let mu = utf16(method);
    assert_eq!(
        text(&mu, parameter_list(&mu, first(method, "Apply"))).as_deref(),
        Some("int amount, ref Stats s"),
        "the parameter list after a generic"
    );
    assert!(
        is_type_parameter(&mu, name(method, "T>", 1, 0)),
        "T in <T> is a type parameter"
    );
    assert!(
        !is_type_parameter(&mu, name(method, "amount", 6, 0)),
        "a parameter is not a type parameter"
    );

    let loop_text = "foreach (ref var hp in _healths) { }";
    let lu = utf16(loop_text);
    assert_eq!(
        text(&lu, foreach_collection(&lu, first(loop_text, "hp"))).as_deref(),
        Some("_healths"),
        "a foreach variable comes from the collection"
    );
    assert_eq!(
        foreach_collection(&utf16("var hp = x;"), first("var hp = x;", "hp")),
        None,
        "not foreach"
    );

    let out = "if (_map.TryGetValue(key, out var found)) { }";
    let ou = utf16(out);
    assert!(
        is_out_argument(&ou, first(out, "found")),
        "out var comes from the call"
    );
    assert_eq!(
        enclosing_call(&ou, first(out, "found").location)
            .map(|s| s.chain)
            .as_deref(),
        Some("_map.TryGetValue"),
        "the call around out"
    );
    assert!(
        !is_out_argument(&utf16("Use(key, found)"), first("Use(key, found)", "found")),
        "not out"
    );

    let lambda = "list.ForEach((a, b) => Sum(a, b)); Apply(x => x.Hp);";
    let lam = utf16(lambda);
    assert!(
        is_lambda_parameter(&lam, name(lambda, "a,", 1, 0)),
        "(a, b) =>"
    );
    assert!(
        is_lambda_parameter(&lam, name(lambda, "x =>", 1, 0)),
        "x =>"
    );
    assert!(
        !is_lambda_parameter(&lam, name(lambda, "a, b)", 1, 24)),
        "an argument is not a parameter"
    );

    let pattern = "if (item.Parameters is not WeaponParameters weapon) return;";
    let pu = utf16(pattern);
    let weapon = first(pattern, "weapon)").intersection(first(pattern, "weapon"));
    assert_eq!(
        text(&pu, pattern_subject(&pu, weapon)).as_deref(),
        Some("item.Parameters"),
        "x is not T name comes from x"
    );
    let pair_loop = "foreach (var (key, count) in _stock) { }";
    let plu = utf16(pair_loop);
    assert_eq!(
        text(&plu, foreach_collection(&plu, first(pair_loop, "count"))).as_deref(),
        Some("_stock"),
        "tuple deconstruction in foreach comes from the collection"
    );
    let local_function =
        "void Run() { void Add(int id, Item item) { Use(item); } Add(1, first); Add(2, second); }";
    let lf = utf16(local_function);
    let parameter = local_function_parameter(
        &lf,
        first(local_function, "item)").intersection(first(local_function, "item")),
    )
    .expect("a local function's parameter: name and number");
    assert!(
        string(&lf, parameter.0) == "Add" && parameter.1 == 1,
        "a local function's parameter: name and number"
    );
    let found: Vec<String> = calls("Add", &lf, whole(&lf), parameter.0.location)
        .iter()
        .filter_map(|&c| argument(&lf, c, 1))
        .map(|r| string(&lf, r))
        .collect();
    assert_eq!(
        found,
        ["first", "second"],
        "the arguments of the local function's calls"
    );
    assert_eq!(
        local_function_parameter(&lf, first(local_function, "first")),
        None,
        "a call argument is not a parameter"
    );

    let optional = "void Update(Model m, List<string> variants = null, int n = Max(1, 2)) { }";
    let ou = utf16(optional);
    let update = first(optional, "Update");
    assert_eq!(
        text(
            &ou,
            argument(&ou, update, 1).and_then(|p| default_value(&ou, p))
        )
        .as_deref(),
        Some("null"),
        "a default value"
    );
    assert_eq!(
        text(
            &ou,
            argument(&ou, update, 2).and_then(|p| default_value(&ou, p))
        )
        .as_deref(),
        Some("Max(1, 2)"),
        "a default with a call"
    );
    assert_eq!(
        argument(&ou, update, 0).and_then(|p| default_value(&ou, p)),
        None,
        "no default"
    );

    let tuple = "var (hp, mana) = LoadStats(id);";
    let tu = utf16(tuple);
    assert_eq!(
        text(&tu, deconstruction(&tu, first(tuple, "mana"))).as_deref(),
        Some("LoadStats(id)"),
        "tuple deconstruction comes from the right-hand side"
    );
    assert_eq!(
        deconstruction(&utf16("Use(hp, mana);"), first("Use(hp, mana);", "mana")),
        None,
        "call arguments are not a deconstruction"
    );

    let arrow = "public int Max => _base * 2;";
    let au = utf16(arrow);
    let found: Vec<String> = getter_expressions(&au, whole(&au), first(arrow, "Max"))
        .iter()
        .map(|&r| string(&au, r))
        .collect();
    assert_eq!(found, ["_base * 2"], "an expression-bodied property");
    let accessors =
        "public int Hp { get { if (dead) return 0; return _hp; } set { _hp = value; } }";
    let acc = utf16(accessors);
    let found: Vec<String> = getter_expressions(&acc, whole(&acc), first(accessors, "Hp"))
        .iter()
        .map(|&r| string(&acc, r))
        .collect();
    assert_eq!(found, ["0", "_hp"], "getter returns");
    let set = setter(&acc, whole(&acc), first(accessors, "Hp")).expect("there is a setter");
    assert!(
        set.contains(first(accessors, "value").location)
            && !set.contains(first(accessors, "dead").location),
        "the setter is only set"
    );
    let auto = "public float Speed { get; private set; } = 5f;";
    let auu = utf16(auto);
    assert_eq!(
        text(
            &auu,
            property_initializer(&auu, whole(&auu), first(auto, "Speed"))
        )
        .as_deref(),
        Some("5f"),
        "an auto-property's initial value"
    );
}

#[test]
fn stashes() {
    let code = "void OnUpdate() {\n    ref var hp = ref _health.Get(e);\n    hp.Value -= damage;\n    var copy = _health.Get(e);\n    copy.Value = 0;\n    _health.Get(other).Value = max;\n    hp.Regen = 1;\n}";
    let units = utf16(code);
    let body = whole(&units);
    let writes = stash_field_writes(&units, "_health", "Value", &mut |_| Some(body));
    let found: Vec<String> = writes
        .iter()
        .map(|w| w.rhs.map(|r| string(&units, r)).unwrap_or_default())
        .collect();
    assert_eq!(
        found,
        ["damage", "max"],
        "through a ref local and straight into Get(); a copy is not a write into the component"
    );
    assert!(writes[0].compound, "-= is compound");
    let use_at = first(code, "hp.Regen").location;
    assert_eq!(
        stash_of_local(&units, "hp", body, use_at).as_deref(),
        Some("_health"),
        "a ref local from a stash"
    );
    assert_eq!(
        stash_of_local(&units, "copy", body, use_at),
        None,
        "a copy is not ref"
    );
}

fn literals(expr: &str) -> Vec<String> {
    let units = utf16(expr);
    literal_alternatives(&units, whole(&units))
        .iter()
        .map(|&r| string(&units, r))
        .collect()
}

#[test]
fn literal_sources() {
    assert!(
        literals("0") == ["0"] && literals("-1.5f") == ["-1.5f"] && literals("1e-3") == ["1e-3"],
        "a number is a literal"
    );
    assert!(
        literals("\"idle\"") == ["\"idle\""] && literals("'x'") == ["'x'"],
        "a string and a character"
    );
    assert_eq!(
        literals("crit ? 2 : 1"),
        ["2", "1"],
        "branches of ?: are possible values, the condition is not"
    );
    assert_eq!(
        literals("a > 0 ? a : 0"),
        ["0"],
        "a branch that is a name is not a literal"
    );
    assert_eq!(
        literals("x ?? 0"),
        ["0"],
        "?? gives the default on the right"
    );
    assert!(
        literals("(int)5") == ["5"] && literals("(float?)null") == ["null"],
        "a cast is removed"
    );
    assert!(
        literals("hp - 1").is_empty() && literals("Mathf.Clamp(x, 0, 1)").is_empty(),
        "a literal in arithmetic or as an argument is not the value"
    );
    assert!(
        literals("(a) - 1").is_empty(),
        "(a) - 1 is a subtraction, not a cast"
    );
    assert_eq!(
        literals("state switch { State.Idle => 1, _ => 2 }"),
        ["1", "2"],
        "switch arms"
    );
    assert!(
        literals("null") == ["null"]
            && literals("default") == ["default"]
            && literals("default(int)") == ["default(int)"],
        "null and default"
    );
    assert!(
        literals("new List<int>()") == ["new List<int>()"] && literals("new()") == ["new()"],
        "new without arguments is a default"
    );
    assert!(
        literals("new Vector3(1, 2, 3)").is_empty(),
        "new with arguments is an object made of them, not a literal"
    );
    assert!(
        literals("$\"hp {hp}\"").is_empty() && literals("$\"hp\"") == ["$\"hp\""],
        "interpolation with a hole is not a literal"
    );
    assert!(
        literals("() => 5").is_empty(),
        "a lambda body is not the expression's value"
    );
    assert!(
        is_default_literal("null") && is_default_literal("new()") && !is_default_literal("0"),
        "a default differs from a literal"
    );
}

#[test]
fn links_and_surrounding_calls() {
    let (units, chain) = all_sources("stats.Damage.ToString()");
    let receiver = chain[0].receiver_chain().expect("present");
    assert!(
        chain[0].links.len() == 3
            && receiver.chain == "stats.Damage"
            && string(&units, receiver.range) == "Damage",
        "the receiver of the last link is the chain without it"
    );
    let (units, nested) = all_sources("Clamp(Get(x), 0, 1)");
    let x = nested.iter().find(|s| s.chain == "x").expect("present");
    let names: Vec<String> = x.calls.iter().map(|&r| string(&units, r)).collect();
    assert_eq!(names, ["Clamp", "Get"], "calls around a name, outside in");
    let (_, constructed) = all_sources("new Vector3(x, 0)");
    assert!(
        constructed
            .iter()
            .find(|s| s.chain == "x")
            .expect("present")
            .calls
            .is_empty(),
        "a constructor argument is the object itself, not a call"
    );
    let (_, plain) = all_sources("(a + b) * c");
    assert!(
        plain.iter().all(|s| s.calls.is_empty()),
        "parentheses of an expression are not a call"
    );
    let receiver = |code: &str, name: &str| -> Option<String> {
        let units = utf16(code);
        let at = code.rfind(name).expect("present");
        let at = R::new(utf16(&code[..at]).len(), utf16(name).len());
        receiver_expression(&units, at).map(|r| string(&units, r))
    };
    assert_eq!(
        receiver("if (player.TryGet(a, out b))", "TryGet").as_deref(),
        Some("player"),
        "a call's receiver is a name"
    );
    assert_eq!(
        receiver("x = GetPlayer(id)?.Stats[0].TryGet(a)", "TryGet").as_deref(),
        Some("GetPlayer(id)?.Stats[0]"),
        "the receiver is a chain with parentheses"
    );
    assert_eq!(
        receiver("TryGet(a)", "TryGet"),
        None,
        "a call without a receiver"
    );
    let element = |code: &str, name: &str| -> Option<String> {
        let units = utf16(code);
        element_write(&units, first(code, name))
            .map(|(value, method)| format!("{method} {}", string(&units, value)))
    };
    assert_eq!(
        element("_map[peer] = player;", "_map").as_deref(),
        Some("[] player"),
        "a write by index"
    );
    assert!(
        element("_map.Add(peer, player);", "_map").as_deref() == Some("Add player")
            && element("_queue.Enqueue(item);", "_queue").as_deref() == Some("Enqueue item"),
        "Add and Enqueue: the last argument"
    );
    assert!(
        element("_map[peer] == player", "_map").is_none()
            && element("_map.Remove(peer);", "_map").is_none()
            && element("var x = _map[peer];", "_map").is_none(),
        "a read and Remove are not an element write"
    );
    let (_, indexed) = all_sources("data[index] + list[i].Value + new[] { a }");
    let keys: Vec<&str> = indexed
        .iter()
        .filter(|s| s.is_index_key)
        .map(|s| s.chain.as_str())
        .collect();
    assert_eq!(
        keys,
        ["index", "i"],
        "an element key is not the value, an array is not an access"
    );
    let lambda =
        |code: &str, name: &str| lambda_call(&utf16(code), first(code, name)).map(|s| s.chain);
    assert_eq!(
        lambda("items.ForEach(x => Use(x));", "x").as_deref(),
        Some("items.ForEach"),
        "the call a lambda was given to"
    );
    assert_eq!(
        lambda("db.QueryAsync(sql, (model, vehicle) => model)", "vehicle").as_deref(),
        Some("db.QueryAsync"),
        "a parameter in a parenthesized list"
    );
    let stash = utf16("_stash.Get(e)");
    assert_eq!(
        super::chain(&stash, R::new(7, 3)),
        "_stash.Get",
        "the chain up to the call's name"
    );
}

#[test]
fn tuple_deconstruction() {
    let body = "void Init() { (x, y) = (1, Get(a, b)); var (p, q) = Pair(); }";
    let units = utf16(body);
    let at = |what: &str| R::new(first(body, what).location, 1);
    assert_eq!(
        text(&units, deconstruction(&units, at("x,"))).as_deref(),
        Some("1"),
        "(x, y) = (1, …): x from its own element"
    );
    assert_eq!(
        text(&units, deconstruction(&units, at("y)"))).as_deref(),
        Some("Get(a, b)"),
        "commas in arguments do not cut the element"
    );
    assert_eq!(
        text(&units, deconstruction(&units, at("p,"))).as_deref(),
        Some("Pair()"),
        "a tuple from a call is the whole call"
    );
}

#[test]
fn collections_and_interpolation() {
    assert_eq!(
        chains("new List<int> { 1, 2, 3 }"),
        ["List"],
        "new without parentheses is a creation, not a name"
    );
    assert!(
        all_sources("new List<int> { 1, 2, 3 }").1[0].constructs,
        "new T {{ … }} is marked"
    );
    assert_eq!(
        chains("new List<int>() { a, b }"),
        ["List()", "a", "b"],
        "elements are sources"
    );
    assert_eq!(
        chains("$\"Player {id} has {hp:F1} of {Max(a, b),8}\""),
        ["id", "hp", "Max()", "a", "b"],
        "holes are sources, format and width are not"
    );
    let literals = |expr: &str| {
        let units = utf16(expr);
        literal_alternatives(&units, whole(&units))
            .into_iter()
            .map(|r| string(&units, r))
            .collect::<Vec<_>>()
    };
    assert_eq!(
        literals("new List<int> { 1, 2, 3 }"),
        ["1", "2", "3"],
        "collection elements are literals"
    );
    assert_eq!(literals("new[] { a, 2 }"), ["2"], "new[] {{ … }}");
    assert_eq!(literals("[4, 5]"), ["4", "5"], "a collection expression");
    assert!(
        literals("new Pawn { Health = 5 }").is_empty(),
        "an object initializer is not a collection"
    );
    assert_eq!(
        literals("2 + 3"),
        ["2 + 3"],
        "literals with operators are one source"
    );
    assert!(literals("b + 1").is_empty(), "b + 1 is a value from b");
}
