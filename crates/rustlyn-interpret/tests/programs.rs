//! Running whole programs, which is the end-to-end check on everything below:
//! the lexer, the parser, the symbols, the binder and the interpreter.

use rustlyn_interpret::run;

/// Runs a body inside `Main` and returns what it printed.
fn output_of(body: &str) -> String {
    let source = format!(
        "using System;\nusing System.Collections.Generic;\n\
         class Program {{ static void Main() {{ {body} }} }}"
    );
    run(&source).unwrap_or_else(|error| panic!("{error}\n--- source ---\n{source}"))
}

/// Runs a whole program and returns what it printed.
fn output_of_program(source: &str) -> String {
    run(source).unwrap_or_else(|error| panic!("{error}"))
}

// -- the basics ------------------------------------------------------------

#[test]
fn hello_world() {
    assert_eq!(
        output_of(r#"Console.WriteLine("hello, world");"#),
        "hello, world\n"
    );
}

#[test]
fn arithmetic_and_printing() {
    assert_eq!(output_of("Console.WriteLine(1 + 2 * 3);"), "7\n");
    assert_eq!(
        output_of("Console.WriteLine(7 / 2);"),
        "3\n",
        "integer division truncates"
    );
    assert_eq!(output_of("Console.WriteLine(7.0 / 2);"), "3.5\n");
    assert_eq!(output_of("Console.WriteLine(7 % 3);"), "1\n");
    assert_eq!(output_of("Console.WriteLine(-3);"), "-3\n");
    assert_eq!(output_of("Console.WriteLine(1 << 4);"), "16\n");
}

#[test]
fn booleans_print_capitalised_as_in_csharp() {
    assert_eq!(output_of("Console.WriteLine(1 < 2);"), "True\n");
    assert_eq!(output_of("Console.WriteLine(1 == 2);"), "False\n");
}

#[test]
fn strings_concatenate_and_interpolate() {
    assert_eq!(output_of(r#"Console.WriteLine("a" + "b");"#), "ab\n");
    assert_eq!(output_of(r#"Console.WriteLine("n=" + 42);"#), "n=42\n");
    assert_eq!(
        output_of(r#"int n = 7; Console.WriteLine($"n is {n}, twice is {n * 2}");"#),
        "n is 7, twice is 14\n"
    );
    assert_eq!(output_of(r#"Console.WriteLine("abc".Length);"#), "3\n");
}

#[test]
fn locals_and_assignment() {
    assert_eq!(
        output_of("var x = 1; x = x + 1; x += 3; Console.WriteLine(x);"),
        "5\n"
    );
    assert_eq!(
        output_of("int i = 0; Console.WriteLine(i++); Console.WriteLine(i);"),
        "0\n1\n"
    );
    assert_eq!(output_of("int i = 0; Console.WriteLine(++i);"), "1\n");
}

// -- control flow ----------------------------------------------------------

#[test]
fn conditionals() {
    assert_eq!(
        output_of(r#"if (1 < 2) { Console.WriteLine("yes"); } else { Console.WriteLine("no"); }"#),
        "yes\n"
    );
    assert_eq!(
        output_of(r#"Console.WriteLine(1 > 2 ? "yes" : "no");"#),
        "no\n"
    );
}

#[test]
fn loops() {
    assert_eq!(
        output_of("for (int i = 0; i < 3; i++) { Console.Write(i); }"),
        "012"
    );
    assert_eq!(
        output_of("int i = 0; while (i < 3) { Console.Write(i); i++; }"),
        "012"
    );
    assert_eq!(
        output_of("int i = 0; do { Console.Write(i); i++; } while (i < 3);"),
        "012"
    );
}

#[test]
fn break_and_continue() {
    assert_eq!(
        output_of("for (int i = 0; i < 10; i++) { if (i == 3) { break; } Console.Write(i); }"),
        "012"
    );
    assert_eq!(
        output_of(
            "for (int i = 0; i < 5; i++) { if (i % 2 == 0) { continue; } Console.Write(i); }"
        ),
        "13"
    );
}

#[test]
fn logical_operators_short_circuit() {
    // If the right side ran, it would divide by zero.
    assert_eq!(
        output_of("int z = 0; if (z != 0 && 10 / z > 1) { } Console.WriteLine(\"survived\");"),
        "survived\n"
    );
    assert_eq!(
        output_of("int z = 0; if (z == 0 || 10 / z > 1) { } Console.WriteLine(\"survived\");"),
        "survived\n"
    );
}

#[test]
fn switch_statements() {
    let body = r#"
        for (int i = 0; i < 4; i++)
        {
            switch (i)
            {
                case 0: Console.Write("zero "); break;
                case 1:
                case 2: Console.Write("small "); break;
                default: Console.Write("big "); break;
            }
        }"#;
    assert_eq!(output_of(body), "zero small small big ");
}

// -- collections -----------------------------------------------------------

#[test]
fn arrays() {
    assert_eq!(
        output_of("int[] a = { 3, 1, 2 }; Console.WriteLine(a.Length); Console.WriteLine(a[0]);"),
        "3\n3\n"
    );
    assert_eq!(
        output_of("var a = new int[3]; a[1] = 7; Console.WriteLine(a[0] + a[1]);"),
        "7\n"
    );
    assert_eq!(
        output_of(
            "int[] a = { 1, 2, 3 }; int sum = 0; foreach (var n in a) { sum += n; } Console.WriteLine(sum);"
        ),
        "6\n"
    );
}

#[test]
fn lists() {
    assert_eq!(
        output_of(
            r#"var list = new List<string>();
               list.Add("a");
               list.Add("b");
               Console.WriteLine(list.Count);
               Console.WriteLine(list[1]);"#
        ),
        "2\nb\n"
    );
}

#[test]
fn strings_are_iterable_and_indexable() {
    assert_eq!(
        output_of(r#"foreach (char c in "abc") { Console.Write(c); }"#),
        "abc"
    );
    assert_eq!(output_of(r#"Console.WriteLine("abc"[1]);"#), "b\n");
}

// -- types -----------------------------------------------------------------

#[test]
fn a_class_with_fields_and_methods() {
    let source = r#"
using System;

class Counter
{
    private int _count;

    public void Increment()
    {
        _count = _count + 1;
    }

    public int Value()
    {
        return _count;
    }
}

class Program
{
    static void Main()
    {
        var counter = new Counter();
        counter.Increment();
        counter.Increment();
        Console.WriteLine(counter.Value());
    }
}"#;
    assert_eq!(output_of_program(source), "2\n");
}

#[test]
fn constructors_and_field_initializers() {
    let source = r#"
using System;

class Point
{
    private int _x = 10;
    private int _y;

    public Point(int y)
    {
        _y = y;
    }

    public int Sum()
    {
        return _x + _y;
    }
}

class Program
{
    static void Main()
    {
        Console.WriteLine(new Point(5).Sum());
    }
}"#;
    assert_eq!(output_of_program(source), "15\n");
}

#[test]
fn automatic_properties_store_and_return() {
    let source = r#"
using System;

class Person
{
    public string Name { get; set; }
    public int Age { get; set; }

    public string Describe()
    {
        return Name + " is " + Age;
    }
}

class Program
{
    static void Main()
    {
        var person = new Person();
        person.Name = "Ada";
        person.Age = 36;
        Console.WriteLine(person.Describe());
    }
}"#;
    assert_eq!(output_of_program(source), "Ada is 36\n");
}

#[test]
fn computed_properties_run_their_body() {
    let source = r#"
using System;

class Box
{
    private int _side = 4;
    public int Area => _side * _side;
    public int Twice { get { return Area * 2; } }
}

class Program
{
    static void Main()
    {
        var box = new Box();
        Console.WriteLine(box.Area);
        Console.WriteLine(box.Twice);
    }
}"#;
    assert_eq!(output_of_program(source), "16\n32\n");
}

#[test]
fn inheritance_dispatches_to_the_override() {
    let source = r#"
using System;
using System.Collections.Generic;

abstract class Animal
{
    public abstract string Sound();

    public virtual string Speak()
    {
        return Sound() + "!";
    }
}

class Dog : Animal
{
    public override string Sound() { return "woof"; }
}

class Cat : Animal
{
    public override string Sound() { return "meow"; }
    public override string Speak() { return "(silence)"; }
}

class Program
{
    static void Main()
    {
        var animals = new List<Animal>();
        animals.Add(new Dog());
        animals.Add(new Cat());
        foreach (var animal in animals)
        {
            Console.WriteLine(animal.Speak());
        }
    }
}"#;
    assert_eq!(output_of_program(source), "woof!\n(silence)\n");
}

#[test]
fn a_base_constructor_runs_first() {
    let source = r#"
using System;

class Base
{
    protected string Label;

    public Base(string label)
    {
        Label = label;
    }
}

class Derived : Base
{
    public Derived() : base("from base") { }

    public string Read() { return Label; }
}

class Program
{
    static void Main()
    {
        Console.WriteLine(new Derived().Read());
    }
}"#;
    assert_eq!(output_of_program(source), "from base\n");
}

#[test]
fn static_fields_are_shared() {
    let source = r#"
using System;

class Counter
{
    public static int Total = 100;

    public static void Add(int amount)
    {
        Total = Total + amount;
    }
}

class Program
{
    static void Main()
    {
        Counter.Add(5);
        Counter.Add(5);
        Console.WriteLine(Counter.Total);
    }
}"#;
    assert_eq!(output_of_program(source), "110\n");
}

// -- methods ---------------------------------------------------------------

#[test]
fn recursion() {
    let source = r#"
using System;

class Program
{
    static int Factorial(int n)
    {
        if (n <= 1) { return 1; }
        return n * Factorial(n - 1);
    }

    static void Main()
    {
        Console.WriteLine(Factorial(10));
    }
}"#;
    assert_eq!(output_of_program(source), "3628800\n");
}

#[test]
fn overloads_pick_by_argument_type() {
    let source = r#"
using System;

class Program
{
    static string Describe(int value) { return "int " + value; }
    static string Describe(string value) { return "string " + value; }

    static void Main()
    {
        Console.WriteLine(Describe(1));
        Console.WriteLine(Describe("x"));
    }
}"#;
    assert_eq!(output_of_program(source), "int 1\nstring x\n");
}

#[test]
fn expression_bodied_members() {
    let source = r#"
using System;

class Program
{
    static int Double(int n) => n * 2;

    static void Main() => Console.WriteLine(Double(21));
}"#;
    assert_eq!(output_of_program(source), "42\n");
}

// -- exceptions ------------------------------------------------------------

#[test]
fn division_by_zero_throws_and_can_be_caught() {
    let body = r#"
        try
        {
            int zero = 0;
            Console.WriteLine(1 / zero);
        }
        catch (Exception e)
        {
            Console.WriteLine("caught " + e);
        }
        finally
        {
            Console.WriteLine("finally");
        }"#;
    assert_eq!(
        output_of(body),
        "caught attempted to divide by zero\nfinally\n"
    );
}

#[test]
fn a_catch_picks_the_exception_type_it_was_written_for() {
    // An exception is a real object rather than its message, which is the only
    // way one `catch` can tell itself from the one beside it.
    assert_eq!(
        output_of(
            r#"try { throw new ArgumentException("bad"); }
               catch (InvalidOperationException e) { Console.WriteLine("wrong " + e.Message); }
               catch (ArgumentException e) { Console.WriteLine("right " + e.Message); }"#
        ),
        "right bad\n"
    );
}

#[test]
fn a_declared_indexer_is_two_methods() {
    assert_eq!(
        output_of_program(
            r#"
using System;
class Bag
{
    private int[] items = new int[4];
    private int writes;
    public int this[int i]
    {
        get { return items[i]; }
        set { items[i] = value; writes = writes + 1; }
    }
    public int Writes { get { return writes; } }
}
class Program
{
    static void Main()
    {
        Bag b = new Bag();
        b[1] = 5;
        b[1] += 3;
        Console.WriteLine(b[1] + " after " + b.Writes + " writes");
    }
}
"#
        ),
        "8 after 2 writes\n"
    );
}

#[test]
fn a_setter_body_sees_the_value_it_was_given() {
    assert_eq!(
        output_of_program(
            r#"
using System;
class Temp
{
    private int celsius;
    public int Celsius
    {
        get { return celsius; }
        set { celsius = value < -273 ? -273 : value; }
    }
}
class Program
{
    static void Main()
    {
        Temp t = new Temp();
        t.Celsius = 40;
        Console.WriteLine(t.Celsius);
        t.Celsius = -400;
        Console.WriteLine(t.Celsius);
    }
}
"#
        ),
        "40\n-273\n"
    );
}

#[test]
fn a_dictionary_is_indexed_by_its_key() {
    assert_eq!(
        output_of(
            r#"Dictionary<string, int> ages = new Dictionary<string, int>();
               ages["ann"] = 30;
               ages["bob"] = 41;
               ages["ann"] += 1;
               Console.WriteLine(ages["ann"] + " " + ages["bob"] + " " + ages.Count);"#
        ),
        "31 41 2\n"
    );
}

#[test]
fn an_uncaught_exception_stops_the_program() {
    let source = "using System;\nclass Program { static void Main() { throw \"boom\"; } }";
    assert_eq!(run(source), Err("unhandled exception: boom".to_string()));
}

#[test]
fn an_index_out_of_range_throws() {
    let body = r#"
        int[] a = { 1 };
        try { Console.WriteLine(a[5]); }
        catch (Exception e) { Console.WriteLine("caught"); }"#;
    assert_eq!(output_of(body), "caught\n");
}

// -- the compiler in front of it -------------------------------------------

#[test]
fn a_program_that_does_not_compile_reports_instead_of_running() {
    let source = "class Program { static void Main() { int x = \"text\"; } }";
    let error = run(source).expect_err("this should not compile");
    assert!(error.contains("CS0029"), "{error}");
}

#[test]
fn a_program_with_a_syntax_error_reports_instead_of_running() {
    let source = "class Program { static void Main() { int x = 1 } }";
    let error = run(source).expect_err("this should not compile");
    assert!(error.contains("CS1002"), "{error}");
}

#[test]
fn a_program_with_no_entry_point_says_so() {
    let error = run("class C { }").expect_err("there is nothing to run");
    assert!(error.contains("no entry point"), "{error}");
}

#[test]
fn runaway_recursion_reports_rather_than_crashing() {
    let source = "class Program { static int F() { return F(); } static void Main() { F(); } }";
    let error = run(source).expect_err("this should not finish");
    assert!(error.contains("too deep"), "{error}");
}

// -- a whole program -------------------------------------------------------

#[test]
fn fizzbuzz() {
    let body = r#"
        for (int i = 1; i <= 15; i++)
        {
            if (i % 15 == 0) { Console.WriteLine("FizzBuzz"); }
            else if (i % 3 == 0) { Console.WriteLine("Fizz"); }
            else if (i % 5 == 0) { Console.WriteLine("Buzz"); }
            else { Console.WriteLine(i); }
        }"#;
    assert_eq!(
        output_of(body),
        "1\n2\nFizz\n4\nBuzz\nFizz\n7\n8\nFizz\nBuzz\n11\nFizz\n13\n14\nFizzBuzz\n"
    );
}

#[test]
fn a_program_using_most_of_the_language() {
    let source = r#"
using System;
using System.Collections.Generic;

abstract class Shape
{
    protected Shape(string name) { Name = name; }

    public string Name { get; set; }

    public abstract double Area();

    public virtual string Describe() => Name + " with area " + Area();
}

class Square : Shape
{
    private readonly double _side;
    public Square(double side) : base("square") { _side = side; }
    public override double Area() { return _side * _side; }
}

class Circle : Shape
{
    private readonly double _radius;
    public Circle(double radius) : base("circle") { _radius = radius; }
    public override double Area() { return 3.0 * _radius * _radius; }
    public override string Describe() { return "a " + Name; }
}

class Program
{
    static int Fibonacci(int n)
    {
        if (n < 2) { return n; }
        return Fibonacci(n - 1) + Fibonacci(n - 2);
    }

    static void Main()
    {
        var shapes = new List<Shape>();
        shapes.Add(new Square(3));
        shapes.Add(new Circle(1));
        foreach (var shape in shapes) { Console.WriteLine(shape.Describe()); }

        int[] numbers = { 5, 3, 8, 1 };
        int best = numbers[0];
        for (int i = 1; i < numbers.Length; i++)
        {
            if (numbers[i] > best) { best = numbers[i]; }
        }
        Console.WriteLine($"largest {best}, fib(10) {Fibonacci(10)}");
    }
}"#;
    assert_eq!(
        output_of_program(source),
        "square with area 9\na circle\nlargest 8, fib(10) 55\n"
    );
}

#[test]
fn foreach_asks_a_collection_for_an_enumerator() {
    // A type that implements nothing: C# looks for the members by name.
    assert_eq!(
        output_of_program(
            r#"
using System;
class Countdown
{
    private int from;
    public Countdown(int from) { this.from = from; }
    public CountdownEnumerator GetEnumerator() { return new CountdownEnumerator(from); }
}
class CountdownEnumerator
{
    private int next;
    public CountdownEnumerator(int from) { next = from + 1; }
    public int Current { get { return next; } }
    public bool MoveNext() { next = next - 1; return next > 0; }
}
class Program
{
    static void Main()
    {
        foreach (int n in new Countdown(4)) { Console.Write(n); }
        Console.WriteLine();
    }
}
"#
        ),
        "4321\n"
    );
}

#[test]
fn foreach_over_a_list_can_be_left_early() {
    assert_eq!(
        output_of(
            r#"List<int> items = new List<int>();
               items.Add(1);
               items.Add(3);
               items.Add(9);
               items.Add(2);
               int total = 0;
               foreach (int item in items)
               {
                   if (item == 3) { continue; }
                   if (item > 5) { break; }
                   total += item;
               }
               Console.WriteLine(total);"#
        ),
        "1\n"
    );
}

#[test]
fn a_method_group_becomes_a_delegate() {
    assert_eq!(
        output_of_program(
            r#"
using System;
delegate int Op(int x);
class Program
{
    static int Dbl(int x) { return x + x; }
    static int Apply(Op f, int x) { return f(x); }
    static void Main()
    {
        Op f = Dbl;
        Console.WriteLine(f(21));
        Console.WriteLine(Apply(Dbl, 5));
        Console.WriteLine(new Op(Dbl)(1));
    }
}
"#
        ),
        "42\n10\n2\n"
    );
}

#[test]
fn a_delegate_over_a_virtual_method_keeps_the_override() {
    // `ldvirtftn` settles the target when the delegate is made, from the
    // receiver it is made with — not from the static type of the variable.
    assert_eq!(
        output_of_program(
            r#"
using System;
delegate string Namer();
class Shape { public virtual string Name() { return "shape"; } }
class Square : Shape { public override string Name() { return "square"; } }
class Program
{
    static void Main()
    {
        Shape s = new Square();
        Namer n = s.Name;
        Console.WriteLine(n());
    }
}
"#
        ),
        "square\n"
    );
}

#[test]
fn a_lambda_becomes_a_delegate_and_closes_over_what_it_reads() {
    assert_eq!(
        output_of_program(
            r#"
using System;
delegate int Op(int x);
delegate void Act();
class Program
{
    static int Apply(Op f, int v) { return f(v); }
    static Op Adder(int by) { return x => x + by; }
    static void Main()
    {
        Console.WriteLine(Apply(x => x + 1, 41));

        // A capture is the variable, not a copy of it: assigning to `factor`
        // after the lambda is made has to be visible inside it.
        int factor = 3;
        Op scale = x => x * factor;
        Console.WriteLine(scale(5));
        factor = 10;
        Console.WriteLine(scale(5));

        // And the lambda can write it back.
        int count = 0;
        Act bump = () => { count = count + 1; };
        bump();
        bump();
        Console.WriteLine(count);

        // A lambda outlives the method that made it.
        Op add7 = Adder(7);
        Console.WriteLine(add7(1));

        Op block = x => { int y = x + 1; return y * y; };
        Console.WriteLine(block(3));
    }
}
"#
        ),
        "42\n15\n50\n2\n8\n16\n"
    );
}

#[test]
fn a_record_gets_its_members_from_the_language() {
    assert_eq!(
        output_of_program(
            r#"
using System;
record Point(int X, int Y);
record Named(string Who, int Age);
class Program
{
    static void Main()
    {
        Point p = new Point(1, 2);
        Console.WriteLine(p.X + " " + p.Y);
        // A record prints what it holds, and is equal to one that holds the
        // same — which is the whole reason to declare one.
        Console.WriteLine(p);
        Console.WriteLine(p == new Point(1, 2));
        Console.WriteLine(p != new Point(1, 3));
        Console.WriteLine(p.Equals(new Point(1, 2)));
        Console.WriteLine(p.GetHashCode() == new Point(1, 2).GetHashCode());
        Console.WriteLine(new Named("ann", 30));
    }
}
"#
        ),
        "1 2\nPoint { X = 1, Y = 2 }\nTrue\nTrue\nTrue\nTrue\nNamed { Who = ann, Age = 30 }\n"
    );
}

#[test]
fn a_type_can_say_what_an_operator_means_on_it() {
    assert_eq!(
        output_of_program(
            r#"
using System;
struct Money
{
    public int Cents;
    public Money(int cents) { Cents = cents; }
    public static Money operator +(Money a, Money b) { return new Money(a.Cents + b.Cents); }
    public static bool operator ==(Money a, Money b) { return a.Cents == b.Cents; }
    public static bool operator !=(Money a, Money b) { return a.Cents != b.Cents; }
    public override string ToString() { return Cents + "c"; }
}
class Program
{
    static void Main()
    {
        Money a = new Money(30);
        Money b = new Money(12);
        Console.WriteLine(a + b);
        Console.WriteLine(a == b);
        Console.WriteLine(a == new Money(30));
    }
}
"#
        ),
        "42c\nFalse\nTrue\n"
    );
}

#[test]
fn ref_and_out_pass_the_variable_rather_than_its_value() {
    assert_eq!(
        output_of_program(
            r#"
using System;
class Holder { public int N; }
class Program
{
    static void Bump(ref int value) { value = value + 1; }
    static void BumpTwice(ref int value) { Bump(ref value); Bump(ref value); }
    static void Split(int total, out int half, out int rest)
    {
        half = total / 2;
        rest = total - half;
    }
    static void Main()
    {
        int n = 5;
        Bump(ref n);
        BumpTwice(ref n);
        Console.WriteLine(n);

        int a;
        int b;
        Split(7, out a, out b);
        Console.WriteLine(a + " " + b);

        Holder h = new Holder();
        h.N = 10;
        Bump(ref h.N);
        Console.WriteLine(h.N);

        int[] values = { 1, 2 };
        Bump(ref values[1]);
        Console.WriteLine(values[1]);

        int parsed;
        Console.WriteLine(Int32.TryParse("42", out parsed) + " " + parsed);
    }
}
"#
        ),
        "8\n3 4\n11\n3\nTrue 42\n"
    );
}

#[test]
fn a_record_hands_its_parts_back() {
    assert_eq!(
        output_of_program(
            r#"
using System;
record Point(int X, int Y);
class Program
{
    static void Main()
    {
        Point p = new Point(3, 4);
        int x;
        int y;
        p.Deconstruct(out x, out y);
        Console.WriteLine(x + " " + y);
    }
}
"#
        ),
        "3 4\n"
    );
}
