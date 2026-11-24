#!/usr/bin/env python3
"""Extracts CompileAndVerify(..., expectedOutput: ...) tests from Roslyn's C# test sources into
standalone programs with expected output, compiled the way the Roslyn test compiles them.

For a test <name> it writes:
  <name>.cs, <name>.part1.cs, ...  the source files of the compilation, in order;
  <name>.expected                  the expected output;
  <name>.args, <name>.exitcode     the program's command-line arguments, one per line, and the
                                   code it has to exit with, where the test gives them;
  <name>.options                   command-line options of `build`, one per line: the language
                                   version, `--optimize`, `--main <type>`, `--define <symbols>`,
                                   `--checked`, `--unsafe` and `--path <k> <path>` (the file path
                                   the test gives source k; the names of file-local types hash it);
  <name>.ref0.cs, <name>.ref1.cs   the C# libraries it references (`references: new[] {
                                   lib.EmitToImageReference() }`), in the order they have to be
                                   built: each may reference the ones before it; a library's other
                                   files are <name>.ref<k>.part1.cs, ... and its own options
                                   <name>.ref<k>.options. A library built from IL (`CompileIL`,
                                   `CreateCompilationWithIL`) is <name>.ref<k>.il, whose first line
                                   `// cav-ilasm: ...` gives ilasm's flags; one referenced under
                                   `extern alias`es starts with `// cav-aliases: A,B`.

What a test compiles is evaluated from the test's C# rather than read off a literal: string
concatenation, constants of the test class and of the test utilities (`IsExternalInitTypeDefinition`),
`Environment.NewLine`, interpolation, helpers that only gate on the runtime (`ExpectedOutput(...)`,
`ExecutionConditionUtil.IsMonoOrCoreClr ? ... : null`), variables assigned before the call, the
compilation a call is given (`var comp = CreateCompilation(source, options: ...)`) and its options,
helpers of the test classes that return an expression, and the rows a theory runs with
(`[InlineData]`, or every combination of the bool parameters of a `[CombinatorialData]` one), less the
calls a row does not make: under an `if` its condition is false for, or the `else` of a true one. IL that is no
string it can evaluate, an expected output of
null (a runtime the test does not run on) or anything it cannot evaluate skips the test.

A call under an `if` a theory's row does not take is not extracted. A helper method with parameters
that holds CompileAndVerify runs once per call of it from a test, its parameters bound to that
call's arguments, and a call in `foreach` loops over lists the test writes out once per iteration.

A test is named <file>_<method>_<k>: k counts the CompileAndVerify calls of the method (and
`<k>_<row>` the rows of a theory; <file>_<test>_<helper><n>_<k> a call of a helper), so a name means
the same test whatever this script learns to extract. Roslyn's sources are read from $CAV_ROSLYN
(default $CAV_HOME/roslyn, $CAV_HOME being /home/user unless set), and the output directory is
$CAV_TESTS (default $CAV_HOME/cav/tests); $CAV_CALL, a regex, names the call to look for instead of
CompileAndVerify."""
import os, re, sys

HOME = os.environ.get('CAV_HOME', '/home/user')
ROSLYN = os.environ.get('CAV_ROSLYN', HOME + '/roslyn') + '/src/Compilers'
ROOT = ROSLYN + '/CSharp/Test'
UTILITIES = [ROSLYN + '/Test/Utilities/CSharp', ROSLYN + '/Test/Utilities/CoreClr', ROSLYN + '/Test/Core',
             ROSLYN + '/Test/Resources/Core/TestResources.cs', ROSLYN + '/Core/Portable/Symbols/WellKnownMemberNames.cs']
RESOURCES = ROSLYN + '/Test/Resources/Core'
OUT = os.environ.get('CAV_TESTS', HOME + '/cav/tests')
VERBOSE = os.environ.get('CAV_VERBOSE')


class Unsupported(Exception):
    """Something the extraction cannot evaluate; the first argument is the kind skipped."""


# ---------------------------------------------------------------------------------------------
# Lexical helpers: literals and comments are skipped as a whole, so that brackets, commas and
# operators are only ever looked at in code.

def literal_end(text, i):
    """If a comment, string or character literal starts at `i`, the index after it, else None."""
    if text.startswith('//', i):
        end = text.find('\n', i)
        return len(text) if end < 0 else end
    if text.startswith('/*', i):
        end = text.find('*/', i + 2)
        return len(text) if end < 0 else end + 2
    ch = text[i]
    if ch == "'":
        j = i + 1
        while j < len(text) and text[j] != "'":
            if text[j] == '\\': j += 1
            if text[j] == '\n': return None
            j += 1
        return j + 1
    if ch not in '$@"': return None
    j = i
    while j < len(text) and text[j] in '$@': j += 1
    if j >= len(text) or text[j] != '"' or j - i > 12: return None
    if i > 0 and (text[i - 1].isalnum() or text[i - 1] == '_') and ch != '"': return None
    try:
        return parse_literal(text, i, None)[1]
    except Unsupported:
        return None


def mask(text):
    """`text` with the contents of every literal and comment replaced by spaces (lengths kept),
    so that regular expressions only find code."""
    out = list(text)
    i = 0
    while i < len(text):
        ch = text[i]
        if ch in '/\'"$@':
            end = literal_end(text, i)
            if end is not None and end > i + 1 or (end is not None and ch == "'"):
                # A comment goes entirely; a literal keeps the characters
                # that open and close it.
                comment = text.startswith(('//', '/*'), i)
                first, last = (i, end) if comment else (i + 1, end - 1)
                for k in range(first, max(last, first)):
                    if out[k] != '\n': out[k] = ' '
                i = end
                continue
        i += 1
    return ''.join(out)


def scan(text, start=0):
    """Yields (index, char, depth) of every code character from `start`, depth counting the
    brackets opened before it."""
    depth = 0
    i = start
    while i < len(text):
        ch = text[i]
        if ch in '/\'"$@':
            end = literal_end(text, i)
            if end is not None and end > i + 1:
                i = end
                continue
        if ch in ')]}': depth -= 1
        yield i, ch, depth
        if ch in '([{': depth += 1
        i += 1


def matching(text, at):
    """The index of the bracket closing the one at `at`."""
    for i, ch, depth in scan(text, at):
        if depth == 0 and ch in ')]}' and i > at: return i
    raise Unsupported('unbalanced')


def split_top(text, sep=','):
    parts, start = [], 0
    for i, ch, depth in scan(text):
        if depth == 0 and ch == sep:
            parts.append(text[start:i]); start = i + 1
    parts.append(text[start:])
    return [p.strip() for p in parts if p.strip()]


def statement_end(text, at):
    """The index of the `;` ending the expression that starts at `at`."""
    for i, ch, depth in scan(text, at):
        if depth < 0: return i
        if depth == 0 and ch == ';': return i
    return len(text)


def strip_comments(expr):
    expr = re.sub(r'(?m)^\s*#\s*(?:region|endregion|pragma)\b.*$', '', expr)
    i = 0
    res = []
    while i < len(expr):
        if expr.startswith('//', i) or expr.startswith('/*', i):
            i = literal_end(expr, i); res.append(' '); continue
        end = literal_end(expr, i) if expr[i] in '\'"$@' else None
        if end is not None and end > i + 1:
            res.append(expr[i:end]); i = end; continue
        res.append(expr[i]); i += 1
    return ''.join(res).strip()


# ---------------------------------------------------------------------------------------------
# Literals.

ESCAPES = {'n': '\n', 'r': '\r', 't': '\t', '"': '"', "'": "'", '\\': '\\', '0': '\0',
           'a': '\a', 'b': '\b', 'f': '\f', 'v': '\v', 'e': '\x1b'}


def unescape(text, i):
    """The character of the escape sequence at `text[i] == '\\'` and the index after it."""
    n = text[i + 1]
    if n in ESCAPES: return ESCAPES[n], i + 2
    if n == 'u': return chr(int(text[i + 2:i + 6], 16)), i + 6
    if n == 'U': return chr(int(text[i + 2:i + 10], 16)), i + 10
    if n == 'x':
        m = re.match(r'[0-9a-fA-F]{1,4}', text[i + 2:])
        return chr(int(m.group(0), 16)), i + 2 + len(m.group(0))
    raise Unsupported('escape')


def parse_literal(text, at, hole):
    """Parses the string literal at `at`: (value, end). `hole` evaluates an interpolation hole's
    expression; without it the holes are skipped (the literal is only being measured)."""
    j = at
    dollars = 0
    verbatim = False
    while text[j] in '$@':
        if text[j] == '$': dollars += 1
        else: verbatim = True
        j += 1
    if text[j] != '"': raise Unsupported('literal')
    out = []

    def interpolate(k, braces):
        # The hole's expression runs to the matching close brace; `,alignment` and `:format`
        # are not evaluated.
        depth = 0
        m = k
        while m < len(text):
            end = literal_end(text, m) if text[m] in '\'"$@' else None
            if end is not None and end > m + 1:
                m = end; continue
            c = text[m]
            if c in '([{': depth += 1
            elif c in ')]': depth -= 1
            elif c == '}':
                if depth == 0: break
                depth -= 1
            m += 1
        expr = text[k:m]
        if hole is not None:
            if any(depth == 0 and c in ',:' for _, c, depth in scan(expr)) and not re.search(r'\?.*:', expr):
                raise Unsupported('formatted hole')
            out.append(to_str(hole(expr)))
        return m + braces

    if not verbatim and text.startswith('"""', j):
        quotes = re.match(r'"{3,}', text[j:]).group(0)
        i = j + len(quotes)
        end = text.find(quotes, i)
        if end < 0: raise Unsupported('literal')
        body = text[i:end]
        close = end + len(quotes)
        if dollars:
            # Holes open with as many braces as the literal has dollars.
            parts = []
            k = 0
            opener = '{' * dollars
            while k < len(body):
                if body.startswith(opener, k) and not body.startswith('{' * (dollars + 1), k):
                    stop = interpolate_raw(body, k + dollars, dollars, hole, parts)
                    k = stop; continue
                parts.append(body[k]); k += 1
            body = ''.join(parts)
        if '\n' in body:
            lines = body.split('\n')
            last = lines[-1]
            indent = len(last) - len(last.lstrip(' \t'))
            lines = lines[1:-1] if lines[0].strip() == '' else lines[:-1]
            body = '\n'.join(l[indent:] if l.startswith(last[:indent]) else l.lstrip(' \t') for l in lines)
        return body, close
    i = j + 1
    while i < len(text):
        c = text[i]
        if verbatim and c == '"':
            if text.startswith('""', i): out.append('"'); i += 2; continue
            break
        if not verbatim and c == '"': break
        if not verbatim and c == '\\':
            ch, i = unescape(text, i); out.append(ch); continue
        if not verbatim and c == '\n': raise Unsupported('literal')
        if dollars and c == '{':
            if text.startswith('{{', i): out.append('{'); i += 2; continue
            i = interpolate(i + 1, 1); continue
        if dollars and text.startswith('}}', i): out.append('}'); i += 2; continue
        out.append(c); i += 1
    if i >= len(text): raise Unsupported('literal')
    end = i + 1
    if text.startswith('u8', end): end += 2
    return ''.join(out), end


def interpolate_raw(body, k, dollars, hole, parts):
    depth = 0
    m = k
    while m < len(body):
        end = literal_end(body, m) if body[m] in '\'"$@' else None
        if end is not None and end > m + 1:
            m = end; continue
        c = body[m]
        if c in '([{': depth += 1
        elif c in ')]': depth -= 1
        elif c == '}':
            if depth == 0: break
            depth -= 1
        m += 1
    if hole is not None:
        expr = body[k:m]
        if any(d == 0 and c in ',:' for _, c, d in scan(expr)) and '?' not in expr:
            raise Unsupported('formatted hole')
        parts.append(to_str(hole(expr)))
    return m + dollars


def to_str(value):
    if isinstance(value, bool): return 'True' if value else 'False'
    if isinstance(value, (int, float)): return str(value)
    if isinstance(value, str): return value
    if value is None: return ''
    raise Unsupported('not a string', repr(value)[:60])


# ---------------------------------------------------------------------------------------------
# Values an expression evaluates to besides strings, numbers and lists.

class Options:
    """Compilation or parse options, as far as the command line of `build` can say them."""

    def __init__(self, **kv):
        self.kv = dict(kv)

    def with_(self, **kv):
        o = Options(**self.kv); o.kv.update(kv); return o


class Tree:
    def __init__(self, text, path='', parse=None):
        self.text, self.path, self.parse = text, path, parse


class Compilation:
    def __init__(self, trees, refs, options, parse):
        self.trees, self.refs, self.options, self.parse = trees, refs, options, parse


class EnumMember:
    def __init__(self, path):
        self.path = path

    def __eq__(self, other):
        return isinstance(other, EnumMember) and other.path == self.path

    def __hash__(self):
        return hash(self.path)


class Token:
    """A token's kind, by its text: `SyntaxFactory.ParseToken("+=").Kind()`."""

    def __init__(self, text):
        self.text = text

    def __eq__(self, other):
        return isinstance(other, Token) and other.text == self.text

    def __hash__(self):
        return hash(self.text)


TOKEN_KINDS = {'PlusToken': '+', 'MinusToken': '-', 'AsteriskToken': '*', 'SlashToken': '/',
               'PercentToken': '%', 'AmpersandToken': '&', 'BarToken': '|', 'CaretToken': '^',
               'LessThanLessThanToken': '<<', 'GreaterThanGreaterThanToken': '>>',
               'GreaterThanGreaterThanGreaterThanToken': '>>>', 'PlusPlusToken': '++',
               'MinusMinusToken': '--', 'PlusEqualsToken': '+=', 'MinusEqualsToken': '-=',
               'AsteriskEqualsToken': '*=', 'SlashEqualsToken': '/=', 'PercentEqualsToken': '%=',
               'AmpersandEqualsToken': '&=', 'BarEqualsToken': '|=', 'CaretEqualsToken': '^=',
               'LessThanLessThanEqualsToken': '<<=', 'GreaterThanGreaterThanEqualsToken': '>>=',
               'GreaterThanGreaterThanGreaterThanEqualsToken': '>>>=', 'ExclamationToken': '!',
               'TildeToken': '~', 'EqualsEqualsToken': '==', 'ExclamationEqualsToken': '!=',
               'LessThanToken': '<', 'GreaterThanToken': '>', 'LessThanEqualsToken': '<=',
               'GreaterThanEqualsToken': '>=', 'TrueKeyword': 'true', 'FalseKeyword': 'false'}

# OperatorFacts: an operator's metadata name, and its checked form's where it has one.
UNARY_OPERATORS = {'+': ['op_UnaryPlus'], '-': ['op_UnaryNegation', 'op_CheckedUnaryNegation'],
                   '!': ['op_LogicalNot'], '~': ['op_OnesComplement'],
                   '++': ['op_Increment', 'op_CheckedIncrement'], '--': ['op_Decrement', 'op_CheckedDecrement'],
                   'true': ['op_True'], 'false': ['op_False']}
BINARY_OPERATORS = {'+': ['op_Addition', 'op_CheckedAddition'], '-': ['op_Subtraction', 'op_CheckedSubtraction'],
                    '*': ['op_Multiply', 'op_CheckedMultiply'], '/': ['op_Division', 'op_CheckedDivision'],
                    '%': ['op_Modulus'], '&': ['op_BitwiseAnd'], '|': ['op_BitwiseOr'], '^': ['op_ExclusiveOr'],
                    '<<': ['op_LeftShift'], '>>': ['op_RightShift'], '>>>': ['op_UnsignedRightShift'],
                    '==': ['op_Equality'], '!=': ['op_Inequality'], '<': ['op_LessThan'], '>': ['op_GreaterThan'],
                    '<=': ['op_LessThanOrEqual'], '>=': ['op_GreaterThanOrEqual']}
COMPOUND_OPERATORS = {'+=': ['op_AdditionAssignment', 'op_CheckedAdditionAssignment'],
                      '-=': ['op_SubtractionAssignment', 'op_CheckedSubtractionAssignment'],
                      '*=': ['op_MultiplicationAssignment', 'op_CheckedMultiplicationAssignment'],
                      '/=': ['op_DivisionAssignment', 'op_CheckedDivisionAssignment'],
                      '%=': ['op_ModulusAssignment'], '^=': ['op_ExclusiveOrAssignment'],
                      '&=': ['op_BitwiseAndAssignment'], '|=': ['op_BitwiseOrAssignment'],
                      '<<=': ['op_LeftShiftAssignment'], '>>=': ['op_RightShiftAssignment'],
                      '>>>=': ['op_UnsignedRightShiftAssignment'],
                      '++': ['op_IncrementAssignment', 'op_CheckedIncrementAssignment'],
                      '--': ['op_DecrementAssignment', 'op_CheckedDecrementAssignment']}


class Reference:
    """A reference to a C# compilation (or, with None, to the framework, or an `IL` library), under
    the `extern alias`es it is given."""

    def __init__(self, compilation, aliases=()):
        self.compilation = compilation
        self.aliases = tuple(aliases)


class IL:
    """A library assembled from IL: its text, whether Roslyn's default header goes in front, and
    whether ilasm may make a base class up (`autoInherit`)."""

    def __init__(self, text, header=True, inherit=True):
        self.text, self.header, self.inherit = text, header, inherit
        self.trees, self.refs = [], []


LANGUAGE_VERSIONS = {'CSharp1': '1', 'CSharp2': '2', 'CSharp3': '3', 'CSharp4': '4', 'CSharp5': '5',
                     'CSharp6': '6', 'CSharp7': '7', 'CSharp7_1': '7.1', 'CSharp7_2': '7.2',
                     'CSharp7_3': '7.3', 'CSharp8': '8', 'CSharp9': '9', 'CSharp10': '10',
                     'CSharp11': '11', 'CSharp12': '12', 'CSharp13': '13', 'CSharp14': '14',
                     'CSharp15': '15', 'Preview': 'preview', 'Latest': 'latest',
                     'LatestMajor': 'latestmajor', 'Default': 'default', 'CSharpNext': 'preview'}

PARSE_OPTIONS = {'Regular': 'default', 'RegularDefault': 'default', 'RegularNext': 'preview',
                 'RegularPreview': 'preview', 'RegularWithDocumentationComments': 'default',
                 'RegularPreviewWithDocumentationComments': 'preview',
                 'RegularWithLegacyStrongName': 'default', 'WithoutImprovedOverloadCandidates': '7.2',
                 'WithCovariantReturns': '9', 'WithoutCovariantReturns': '8',
                 'RegularWithExtendedPartialMethods': 'preview', 'RegularWithFileScopedNamespaces': '10',
                 'ExperimentalParseOptions': 'preview', 'RegularWithoutRecursivePatterns': '7.3',
                 'RegularWithRecursivePatterns': '8', 'RegularWithoutPatternCombinators': '8',
                 'RegularWithPatternCombinators': 'preview', 'RegularWithExtendedPropertyPatterns': 'preview',
                 'RegularWithListPatterns': 'preview'}
for _k, _v in LANGUAGE_VERSIONS.items():
    if _k.startswith('CSharp') and _k[6:7].isdigit():
        PARSE_OPTIONS['Regular' + _k[6:]] = _v

# Conditions on the machine running the test: this one is .NET (Core) on Linux.
CONDITIONS = {'IsMonoOrCoreClr': True, 'IsCoreClr': True, 'IsCoreClrRuntime': True, 'IsDesktop': False,
              'IsWindows': False, 'IsMono': False, 'IsUnix': True, 'IsLinux': True, 'IsMacOS': False,
              'Is64Bit': True, 'Is32Bit': False, 'IsWindowsDesktop': False, 'IsNet9OrLater': True,
              'IsNet10OrLater': True, 'IsNet8OrLater': True, 'IsNet7OrLater': True, 'IsNet6OrLater': True,
              'IsNet5OrLater': True, 'IsNetCore': True, 'IsNetCoreApp': True, 'IsNet11OrLater': False}

# Helpers of the test classes that return their argument on .NET (Core) and null elsewhere, or
# otherwise only reformat it.
IDENTITY = {'ExpectedOutput', 'IncludeExpectedOutput', 'IfSpans', 'TrimExpectedOutput', 'IncludeExpression'}

# References to assemblies the shared framework already has: nothing to build.
FRAMEWORK_REF = re.compile(
    r'^(?:CSharpRef|SystemCoreRef\w*|SystemRef\w*|MscorlibRef\w*|ValueTupleRef|SystemRuntimeFacadeRef|'
    r'LinqAssemblyRef|SystemObjectModelRef|SystemXmlRef|SystemXmlLinqRef|SystemDataRef|SystemThreadingTasksExtensions\.\w+|'
    r'NetStandard20\.\w+|Net\w*\.References\.\w+|s_valueTupleRefs|TargetFrameworkUtil\.\w+|TestMetadata\.Net\w+\.\w+|'
    r'(?:TestMetadata\.)?Net(?:461|Standard20|Core30|50|60|70|80|90|100)\.\w+|RefSafetyRulesAttributeLib)$')
IL_REF = re.compile(r'CompileIL|FromIlSource|IlSource|ILSource|CreateMetadataReferenceFromIl|GetILRef|TestReferences\.|CompileILToReference|ReferenceFromIL')

COMPILATION_CALL = re.compile(r'^(?:Create(?:Empty|Standard)?Compilation\w*|CreateCompilationWith\w+|CompileAndVerify\w*|CreateExperimentalCompilation\w*)$')
# Frameworks a program cannot run against here: a test for .NET Framework or .NET Standard runs
# on .NET as well (the types it needs are there), one for WinRT or a minimal core library does not.
OTHER_FRAMEWORK = re.compile(r'TargetFramework\.(?:WinRT|Empty|Minimal\w*)\b')


# ---------------------------------------------------------------------------------------------
# Constants: every `const string X = ...` / `static readonly string X = ...` / `static string X =>`
# of the test sources and utilities, by file and by name.

MEMBER = re.compile(r"(?:\bconst|\bstatic(?:\s+readonly)?|\breadonly)\s+(?!class\b|struct\b|void\b)[\w.<>\[\]?]+\s+(\w+)\s*(=>|=)(?!=)\s*")


# Symbols the test code itself is compiled with (`#if NET` around a test's expectations).
TEST_SYMBOLS = {'NET', 'NETCOREAPP', 'NET5_0_OR_GREATER', 'NET6_0_OR_GREATER', 'NET7_0_OR_GREATER',
                'NET8_0_OR_GREATER', 'NET9_0_OR_GREATER', 'NET10_0_OR_GREATER', 'true'}


def preprocess(text, masked):
    """Blanks out the lines of the test code (not of the literals in it) that its `#if`s exclude,
    keeping every position."""
    lines = text.split('\n')
    mlines = masked.split('\n')
    stack = []          # (this branch active, some branch taken)
    out = []
    for line, mline in zip(lines, mlines):
        directive = re.match(r'\s*#\s*(if|elif|else|endif)\b(.*)', mline)
        if directive:
            kind, cond = directive.group(1), directive.group(2).split('//')[0].strip()
            def holds(c):
                c = c.replace('!', ' not ').replace('&&', ' and ').replace('||', ' or ')
                c = re.sub(r'[A-Za-z_]\w*', lambda m: m.group(0) if m.group(0) in ('not', 'and', 'or') else str(m.group(0) in TEST_SYMBOLS), c)
                try: return bool(eval(c))
                except Exception: return False
            outer = all(a for a, _ in stack)
            if kind == 'if':
                v = holds(cond); stack.append((v, v))
            elif kind == 'elif' and stack:
                a, taken = stack.pop(); v = not taken and holds(cond); stack.append((v, taken or v))
            elif kind == 'else' and stack:
                a, taken = stack.pop(); stack.append((not taken, True))
            elif kind == 'endif' and stack:
                stack.pop()
            out.append(' ' * len(line))
            continue
        out.append(line if all(a for a, _ in stack) else ' ' * len(line))
    return '\n'.join(out)


# `static string Name(parameters) => expression;` or `{ return expression; }`: helpers of the test
# classes that make a source or an expected output.
HELPER = re.compile(r'\bstatic\s+(?!class\b|void\b)[\w.<>\[\]?]+\s+(\w+)\s*\(')


class Source:
    def __init__(self, path):
        self.path = path
        self.text = open(path, encoding='utf-8-sig').read()
        self.masked = mask(self.text)
        if re.search(r'^\s*#\s*if', self.masked, re.M):
            self.text = preprocess(self.text, self.masked)
            self.masked = mask(self.text)
        # The bodies of the methods: a constant or a local function declared in
        # one is seen only there.
        self.bodies = []
        for m in METHOD.finditer(self.masked):
            try:
                close = matching(self.text, m.end() - 1)
                brace = re.match(r'\s*\{', self.masked[close + 1:])
                if brace:
                    start = close + brace.end()
                    self.bodies.append((start, matching(self.text, start)))
            except Unsupported:
                continue
        self.members = {}
        for m in MEMBER.finditer(self.masked):
            end = statement_end(self.text, m.end())
            self.members.setdefault(m.group(1), []).append(
                (self.text[m.end():end], self.class_at(m.start()), m.start(), self.in_body(m.start())))
        self.helpers = {}
        for m in HELPER.finditer(self.masked):
            try:
                close = matching(self.text, m.end() - 1)
            except Unsupported:
                continue
            rest = self.text[close + 1:]
            body = re.match(r'\s*=>\s*', rest)
            if body:
                at = close + 1 + body.end()
                code = self.text[at:statement_end(self.text, at)]
            else:
                # A block of local declarations and a `return`, kept with
                # its braces.
                body = re.match(r'\s*\{', rest)
                if not body: continue
                brace = close + body.end()
                try:
                    code = self.text[brace:matching(self.text, brace) + 1]
                except Unsupported:
                    continue
            self.helpers.setdefault(m.group(1), []).append(
                (parameters_full(self.text[m.end():close]), code, self.class_at(m.start()), m.start(),
                 self.in_body(m.start())))

    def in_body(self, at):
        return any(start < at < end for start, end in self.bodies)

    def class_at(self, at):
        found = None
        for m in re.finditer(r'\b(?:class|struct)\s+(\w+)', self.masked[:at]):
            found = m.group(1)
        return found


GLOBAL = {}      # name -> [(expr, class, source, position, local)]
HELPERS = {}     # name -> [(parameters, expr, class, source, position, local)]


def visible(candidates, source_at, position_at, local_at, ctx):
    """The definitions of a name code in `ctx` sees: a local one declared within its scope, else
    one of its own file's members, else any member of the name."""
    scoped = [c for c in candidates if c[local_at] and ctx.source is c[source_at]
              and ctx.start is not None and ctx.start <= c[position_at] < ctx.end]
    if scoped: return scoped[-1:]
    members_ = [c for c in candidates if not c[local_at]]
    own = [c for c in members_ if c[source_at] is ctx.source] if ctx.source else []
    return own or members_


def index_constants(sources):
    for s in sources:
        for name, found in s.members.items():
            for expr, cls, at, local in found:
                GLOBAL.setdefault(name, []).append((expr, cls, s, at, local))
        for name, found in s.helpers.items():
            for params, expr, cls, at, local in found:
                HELPERS.setdefault(name, []).append((params, expr, cls, s, at, local))


# Helpers of the test utilities that build a source with statements rather than one expression,
# ported: (parameter names with their defaults, the function).

def interpolated_string_custom_handler_type(name, type, useBoolReturns, includeOneTimeHelpers=True,
                                            includeTrailingOutConstructorParameter=False):
    """CSharpTestBase.GetInterpolatedStringCustomHandlerType."""
    return_type = 'bool' if useBoolReturns else 'void'
    return_statement = 'return true;' if useBoolReturns else 'return;'
    culture = '''
public class CultureInfoNormalizer
{
    private static CultureInfo originalCulture;

    public static void Normalize()
    {
        originalCulture = CultureInfo.CurrentCulture;
        CultureInfo.CurrentCulture = CultureInfo.InvariantCulture;
    }

    public static void Reset()
    {
        CultureInfo.CurrentCulture = originalCulture;
    }
}
'''
    trimmed = name[:name.index('<')] if '<' in name else name
    out = ('using System.Globalization;\n' if includeOneTimeHelpers else '') + '''
using System.Text;
[System.Runtime.CompilerServices.InterpolatedStringHandler]
public ''' + type + ' ' + name + '''
{
    private readonly StringBuilder _builder;
    public ''' + trimmed + '''(int literalLength, int formattedCount''' + (', out bool success' if includeTrailingOutConstructorParameter else '') + ''')
    {
        ''' + ('success = true;' if includeTrailingOutConstructorParameter else '') + '''
        _builder = new();
    }
    public ''' + return_type + ''' AppendLiteral(string literal)
    {
        _builder.AppendLine("literal:" + literal);
        ''' + return_statement + '''
    }
    public ''' + return_type + ''' AppendFormatted(object o, int alignment = 0, string format = null)
    {
        _builder.AppendLine("value:" + o?.ToString());
        _builder.AppendLine("alignment:" + alignment.ToString());
        _builder.AppendLine("format:" + format);
        ''' + return_statement + '''
    }
    public override string ToString() => _builder.ToString();
}
'''
    if includeOneTimeHelpers:
        out += to_str(member('InterpolatedStringHandlerAttribute', None, Context(None, None, None))) + culture
    return out


def interpolated_string_handler_definition(includeSpanOverloads, useDefaultParameters, useBoolReturns,
                                           returnExpression=None, constructorBoolArg=False,
                                           constructorSuccessResult=True):
    """CSharpTestBase.GetInterpolatedStringHandlerDefinition."""
    b = []
    b.append('''
namespace System.Runtime.CompilerServices
{
    using System.Text;
    public ref partial struct DefaultInterpolatedStringHandler
    {
        private readonly StringBuilder _builder;
        public DefaultInterpolatedStringHandler(int literalLength, int formattedCount''' + (', out bool success' if constructorBoolArg else '') + ''')
        {
            _builder = new StringBuilder();
            ''' + (f"success = {'true' if constructorSuccessResult else 'false'};" if constructorBoolArg else '') + '''
        }
        public string ToStringAndClear() => _builder.ToString();''' + '\n')

    def body(value, alignment, format, span):
        if value:
            b.append('''
        {
            _builder.Append("value:");
            _builder.Append(value''' + ('' if span else '?') + '''.ToString());''')
        else:
            b.append('''
        {
            _builder.Append(s);''')
        if alignment:
            b.append('''
            _builder.Append(",alignment:");
            _builder.Append(alignment);''')
        if format:
            b.append('''
            _builder.Append(":format:");
            _builder.Append(format);''')
        b.append('''
            _builder.AppendLine();''')
        if useBoolReturns:
            b.append('''
            return ''' + (returnExpression if returnExpression is not None else 'true') + ';')
        b.append('''
        }''' + '\n')

    def signature(text):
        b.append('''
        public ''' + ('bool' if useBoolReturns else 'void') + ' ' + text)

    def variants(type, generic, span=False):
        generic = generic or ''
        signature(f'AppendFormatted{generic}({type} value)'); body(True, False, False, span)
        signature(f'AppendFormatted{generic}({type} value, int alignment)'); body(True, True, False, span)
        signature(f'AppendFormatted{generic}({type} value, string format)'); body(True, False, True, span)
        signature(f'AppendFormatted{generic}({type} value, int alignment, string format)'); body(True, True, True, span)

    signature('AppendLiteral(string s)'); body(False, False, False, False)
    if useDefaultParameters:
        for t in ('AppendFormatted<T>(T value', 'AppendFormatted(object value', 'AppendFormatted(string value'):
            signature(t + ', int alignment = 0, string format = null)'); body(True, True, True, False)
    else:
        variants('T', '<T>'); variants('object', None); variants('string', None)
    if includeSpanOverloads:
        if useDefaultParameters:
            signature('AppendFormatted(ReadOnlySpan<char> value, int alignment = 0, string format = null)')
            body(True, True, True, True)
        else:
            variants('ReadOnlySpan<char>', None, True)
    b.append('''
    }
}''')
    return ''.join(b)


PORTED = {
    'GetInterpolatedStringCustomHandlerType': interpolated_string_custom_handler_type,
    'GetInterpolatedStringHandlerDefinition': interpolated_string_handler_definition,
}


def ported(name, args, ctx, before):
    import inspect
    function = PORTED[name]
    names = list(inspect.signature(function).parameters)
    values = {}
    for pname, given in bind_arguments(names, args).items():
        values[pname] = evaluate(given, ctx, before)
    try:
        return function(**values)
    except TypeError as error:
        raise Unsupported('call', name, str(error))


def helper(name, cls, args, ctx, before):
    """Calls a helper of the test classes: its parameters bound to the arguments."""
    candidates = HELPERS.get(name, [])
    if cls: candidates = [c for c in candidates if c[2] == cls]
    pick = visible(candidates, 3, 4, 5, ctx)
    if not pick or len({c[1] for c in pick}) > 1: raise Unsupported('call', name)
    params, expr, _, source, at, local = pick[0]
    # A local function sees the other local functions of its method.
    scope = next(((start, end) for start, end in source.bodies if start < at < end), (None, None)) if local else (None, None)
    bindings = {}
    given_by_name = bind_arguments([pname for _, pname, _ in params], args)
    for k, (ptype, pname, default) in enumerate(params):
        given = given_by_name.get(pname)
        if given is None and ptype.startswith('params'):
            bindings[pname] = []; continue
        if given is None:
            if default is None: raise Unsupported('call', name)
            bindings[pname] = evaluate(default, Context(source, None, None), 0)
        else:
            bindings[pname] = evaluate(given, ctx, before)
    ctx = Context(source, scope[0], scope[1], bindings)
    if not expr.startswith('{'):
        return evaluate(expr, ctx, 0)
    # `{ var x = ...; Debug.Assert(...); return ...; }`
    for statement in split_top(expr[1:-1], ';'):
        statement = strip_comments(statement)
        if not statement or statement.startswith('Debug.Assert'): continue
        m = re.match(r'^return\s+(.*)$', statement, re.S)
        if m: return evaluate(m.group(1), ctx, 0)
        m = re.match(r'^(?:var|[\w.]+(?:<[\w.<>, ]+>)?\??(?:\[\])?)\s+(\w+)\s*=(?!=)\s*(.*)$', statement, re.S)
        if not m: raise Unsupported('call', name, 'statement')
        bindings[m.group(1)] = evaluate(m.group(2), ctx, 0)
    raise Unsupported('call', name, 'no return')


# ---------------------------------------------------------------------------------------------
# The evaluator.

class Context:
    def __init__(self, source, scope_start, scope_end, bindings=None, body_start=None):
        self.source = source
        self.start, self.end = scope_start, scope_end
        self.bindings = bindings or {}
        self.body_start = body_start

    def holds(self, condition, before):
        """True or False where `condition` evaluates, None where it does not."""
        try:
            value = evaluate(condition, self, before)
        except (Unsupported, KeyError, IndexError, ValueError, TypeError, AttributeError, RecursionError):
            return None
        return value if isinstance(value, bool) else None

    def reachable(self, at):
        """Whether the statement at `at` runs: True, False, or None where a condition on the way
        cannot be evaluated. `if`s and `else`s with or without braces count, a block before
        that always returns (`if (languageVersion == LanguageVersion.CSharp13) { ...; return; }`),
        and the section of a `switch` statement."""
        if self.body_start is None: return True
        masked = self.source.masked
        text = self.source.text
        unknown = False

        def check(conds, where):
            nonlocal unknown
            for c, polarity in conds:
                held = self.holds(c, where)
                if held is None: unknown = True
                elif held is not polarity: return False
            return True

        # (open brace, conditions that hold inside it, the if-chain it belongs to, switch value)
        stack = []
        chains = {}         # depth -> conditions of the if-chain whose block just closed
        i = self.body_start
        while i < at:
            ch = masked[i]
            if ch == '{':
                header_start = block_header_start(masked, i)
                header = text[header_start:i].strip()
                depth = len(stack)
                m = re.fullmatch(r'(else\s+)?if\s*\((.*)\)', header, re.S)
                sw = re.fullmatch(r'switch\s*\((.*)\)', header, re.S)
                if m:
                    before = chains.get(depth, []) if m.group(1) else []
                    stack.append((i, [(c, False) for c in before] + [(m.group(2), True)], before + [m.group(2)], None))
                elif header == 'else':
                    stack.append((i, [(c, False) for c in chains.get(depth, [])], None, None))
                else:
                    stack.append((i, [], None, sw.group(1) if sw else None))
                chains.pop(depth, None)
            elif ch == '}' and stack:
                start, conds, chain, _ = stack.pop()
                depth = len(stack)
                if chain is not None:
                    chains[depth] = chain
                else:
                    chains.pop(depth, None)
                # A block that always returns ends the method for whoever enters it.
                body = masked[start + 1:i]
                if (conds and re.search(r'(?:^|[;{}])\s*return\s*;\s*$', body)
                        and all(self.holds(c, start) is polarity for c, polarity in conds)):
                    return False
            i += 1
        for start, conds, _, switch in stack:
            if not check(conds, at): return False
            if switch is not None:
                section = self.switch_section(start, at, switch)
                if section is False: return False
                if section is None: unknown = True
        # `if (c) statement;` and `else statement;` without braces.
        statement = max(masked.rfind(';', 0, at), masked.rfind('{', 0, at), masked.rfind('}', 0, at)) + 1
        prefix = text[statement:at]
        m = re.match(r'\s*(else\s+)?if\s*\((.*)\)\s*$', prefix, re.S)
        if m and not check([(m.group(2), True)], at): return False
        if re.match(r'\s*else\s*(?:if\s*\(.*\))?\s*$', prefix, re.S):
            previous = max(masked.rfind(';', 0, statement - 1), masked.rfind('{', 0, statement - 1),
                           masked.rfind('}', 0, statement - 1)) + 1
            p = re.match(r'\s*(?:else\s+)?if\s*\((.*?)\)\s*(?![\s{])', text[previous:statement], re.S)
            if p and not check([(p.group(1), False)], at): return False
        return None if unknown else True

    def switch_section(self, brace, at, switch):
        """Whether the section of the `switch (switch) {` at `brace` holding `at` is the one the
        value takes; None where the value or a label cannot be evaluated."""
        masked = self.source.masked
        text = self.source.text
        try:
            close = matching(text, brace)
        except Unsupported:
            return None
        labels = []     # (position, label expression or None for default)
        depth = 0
        for i in range(brace + 1, close):
            ch = masked[i]
            if ch in '({[': depth += 1
            elif ch in ')}]': depth -= 1
            elif depth == 0:
                m = re.match(r'(?<![\w.])(case\s+([^:]+?)|default)\s*:(?!:)', masked[i:i + 200]) if (i == 0 or not (masked[i - 1].isalnum() or masked[i - 1] == '_')) else None
                if m and (m.group(1) == 'default' or masked[i:i + 4] == 'case'):
                    labels.append((i, None if m.group(1) == 'default' else text[i + 5:i + 5 + len(m.group(2))]))
        before = [l for l in labels if l[0] < at]
        if not before: return None
        # The labels of this section: the last one before `at` and those right before it.
        section = [before[-1]]
        for label in reversed(before[:-1]):
            gap = masked[label[0]:section[0][0]]
            if re.fullmatch(r'(?:case\s+[^:;{}]+|default)\s*:\s*', gap): section.insert(0, label)
            else: break
        try:
            value = evaluate(switch, self, brace)
        except (Unsupported, KeyError, IndexError, ValueError, TypeError, AttributeError, RecursionError):
            return None

        def matches(label):
            try:
                return pattern_matches(value, label, self, brace)
            except (Unsupported, KeyError, IndexError, ValueError, TypeError, AttributeError, RecursionError):
                return None

        results = [matches(l) for _, l in section if l is not None]
        if any(r is True for r in results): return True
        if any(r is None for r in results): return None
        if any(l is None for _, l in section):
            others = [matches(l) for _, l in labels if l is not None]
            if any(r is None for r in others): return None
            return not any(others)
        return False

    def local(self, name, before):
        """The value of local variable `name` at position `before` (absolute): its last
        assignment before it, plus any `+=` after that."""
        masked = self.source.masked
        text = self.source.text
        found = None
        for m in re.finditer(r'(?<![\w.])' + re.escape(name) + r'\s*(\+?=)(?![=>])\s*', masked[self.start:before]):
            reached = self.reachable(self.start + m.start())
            if reached is False: continue
            if m.group(1) == '=': found = [m]
            elif found is not None: found.append(m)
            # An assignment that may or may not run leaves the value unknown.
            if reached is None: found = [None]
        if found is None: return None
        if found[0] is None: raise Unsupported('conditional assignment', name)
        value = None
        for k, m in enumerate(found):
            at = self.start + m.end()
            rhs = text[at:statement_end(text, at)]
            v = evaluate(rhs, self, self.start + m.start())
            value = v if k == 0 else add(value, v)
        return (value,)


def add(a, b):
    if isinstance(a, list) or isinstance(b, list): raise Unsupported('list +')
    if isinstance(a, str) or isinstance(b, str): return to_str(a) + to_str(b)
    if isinstance(a, (int, float)) and isinstance(b, (int, float)) and not isinstance(a, bool): return a + b
    raise Unsupported('+')


class Lazy:
    """An argument of a helper call, evaluated where the helper uses it: a test hands a helper
    diagnostics to verify as well, which say nothing about what it compiles."""

    def __init__(self, expr, ctx, before):
        self.expr, self.ctx, self.before = expr, ctx, before
        self.done = False

    def value(self):
        if not self.done:
            self.result = evaluate(self.expr, self.ctx, self.before)
            self.done = True
        return self.result


def lookup(name, ctx, before):
    if name in ctx.bindings:
        value = ctx.bindings[name]
        return value.value() if isinstance(value, Lazy) else value
    if ctx.start is not None:
        found = ctx.local(name, before)
        if found is not None: return found[0]
    return member(name, None, ctx)


def member(name, cls, ctx):
    """A constant of the test's file, or of any file when that is the only one of the name."""
    candidates = GLOBAL.get(name, [])
    if cls: candidates = [c for c in candidates if c[1] == cls]
    pick = visible(candidates, 2, 3, 4, ctx)
    if not pick: raise Unsupported('unknown name', name)
    if len({c[0] for c in pick}) > 1: raise Unsupported('ambiguous name', name)
    expr, _, source, _, _ = pick[0]
    return evaluate(expr, Context(source, None, None), 0)


def strip_parens(expr):
    while expr.startswith('(') and matching(expr, 0) == len(expr) - 1 and len(split_top(expr[1:-1])) == 1:
        expr = expr[1:-1].strip()
    return expr


def pattern_matches(value, pattern, ctx, before):
    """Whether `value` matches a constant pattern, `_`, `null`, or their `or`/`and`/`not`."""
    pattern = strip_parens(pattern.strip())
    for op in (' or ', ' and '):
        parts, start = [], 0
        for i, ch, depth in scan(pattern):
            if depth == 0 and pattern.startswith(op, i):
                parts.append(pattern[start:i]); start = i + len(op)
        if parts:
            parts.append(pattern[start:])
            results = [pattern_matches(value, p, ctx, before) for p in parts]
            return any(results) if op == ' or ' else all(results)
    if pattern.startswith('not '): return not pattern_matches(value, pattern[4:], ctx, before)
    if pattern in ('_', 'var _'): return True
    if re.match(r'^[<>]=?', pattern):
        m = re.match(r'^([<>]=?)\s*(.*)', pattern)
        other = evaluate(m.group(2), ctx, before)
        return {'<': value < other, '<=': value <= other, '>': value > other, '>=': value >= other}[m.group(1)]
    if re.fullmatch(r'(string|bool|int)', pattern):
        return isinstance(value, {'string': str, 'bool': bool, 'int': int}[pattern])
    return evaluate(pattern, ctx, before) == value


NOT_SWITCH = object()


def switch_expression(expr, ctx, before):
    """`value switch { pattern => result, ... }`, or None when `expr` is not one."""
    at = None
    for i, ch, depth in scan(expr):
        if depth == 0 and re.match(r'switch\s*\{', expr[i:]) and (i == 0 or not (expr[i - 1].isalnum() or expr[i - 1] == '_')):
            at = i
            break
    if at is None: return NOT_SWITCH
    brace = expr.index('{', at)
    close = matching(expr, brace)
    if expr[close + 1:].strip(): raise Unsupported('expression', 'switch')
    value = evaluate(expr[:at], ctx, before)
    for arm in split_top(expr[brace + 1:close]):
        for i, ch, depth in scan(arm):
            if depth == 0 and arm.startswith('=>', i):
                pattern, result = arm[:i], arm[i + 2:]
                break
        else:
            raise Unsupported('expression', 'switch arm')
        if ' when ' in pattern: raise Unsupported('expression', 'switch when')
        if pattern_matches(value, pattern, ctx, before):
            return evaluate(result, ctx, before)
    raise Unsupported('expression', 'switch without a match')


def is_pattern(expr, ctx, before):
    for i, ch, depth in scan(expr):
        if depth == 0 and re.match(r'\sis\s', expr[i:i + 4]):
            return pattern_matches(evaluate(expr[:i], ctx, before), expr[i + 4:], ctx, before)
    return None


def binary_split(expr, ops):
    """The last top-level occurrence of any operator of `ops` that is binary: (left, op, right)."""
    found = None
    for i, ch, depth in scan(expr):
        if depth != 0: continue
        for op in ops:
            if expr.startswith(op, i):
                left = expr[:i].rstrip()
                if not left or left[-1] in '+-*/%=!<>&|^?:(,': continue
                if op == '+' and (expr.startswith('++', i) or expr[i - 1] == '+'): continue
                if op in ('<', '>') and (expr.startswith(op * 2, i) or expr[i - 1] == op or expr.startswith(op + '=', i)): continue
                found = (i, op)
                break
    if found is None: return None
    i, op = found
    return expr[:i].strip(), op, expr[i + len(op):].strip()


def ternary(expr):
    question = None
    depth_colon = 0
    for i, ch, depth in scan(expr):
        if depth != 0: continue
        if ch == '?' and question is None:
            nxt = expr[i + 1:i + 2]
            if nxt in ('.', '?', '[') or expr[i - 1] == '?': continue
            question = i
        elif ch == '?' and question is not None and expr[i + 1:i + 2] not in ('.', '?', '['):
            depth_colon += 1
        elif ch == ':' and question is not None:
            if depth_colon: depth_colon -= 1; continue
            return expr[:question].strip(), expr[question + 1:i].strip(), expr[i + 1:].strip()
    return None


def evaluate(expr, ctx, before):
    expr = strip_parens(strip_comments(expr))
    if not expr: raise Unsupported('empty')
    t = ternary(expr)
    if t:
        return evaluate(t[1] if truth(evaluate(t[0], ctx, before)) else t[2], ctx, before)
    for ops in (('??',), ('||',), ('&&',), ('==', '!='), ('+', '-')):
        b = binary_split(expr, ops)
        if b is None: continue
        left, op, right = b
        if op == '??':
            v = evaluate(left, ctx, before)
            return v if v is not None else evaluate(right, ctx, before)
        if op == '||': return truth(evaluate(left, ctx, before)) or truth(evaluate(right, ctx, before))
        if op == '&&': return truth(evaluate(left, ctx, before)) and truth(evaluate(right, ctx, before))
        lv, rv = evaluate(left, ctx, before), evaluate(right, ctx, before)
        if op == '==': return lv == rv
        if op == '!=': return lv != rv
        if op == '+': return add(lv, rv)
        if op == '-':
            if isinstance(lv, int) and isinstance(rv, int): return lv - rv
            raise Unsupported('-')
    sw = switch_expression(expr, ctx, before)
    if sw is not NOT_SWITCH: return sw
    p = is_pattern(expr, ctx, before)
    if p is not None: return p
    if expr.startswith('!') and not expr.startswith('!='):
        return not truth(evaluate(expr[1:], ctx, before))
    m = re.match(r'^\((char|int|string|object|long|bool|CSharpTestSource|string\[\])\)\s*', expr)
    if m:
        v = evaluate(expr[m.end():], ctx, before)
        if m.group(1) == 'char': return chr(v) if isinstance(v, int) else v
        return v
    return postfix(expr, ctx, before)


def truth(v):
    if isinstance(v, bool): return v
    raise Unsupported('condition', repr(v)[:40])


def primary(expr, ctx, before):
    """Parses the primary expression at the start of `expr`: (value, rest)."""
    if expr[0] in '"$@':
        value, end = parse_literal(expr, 0, lambda e: evaluate(e, ctx, before))
        return value, expr[end:]
    if expr[0] == "'":
        end = literal_end(expr, 0)
        body = expr[1:end - 1]
        return (unescape(body, 0)[0] if body.startswith('\\') else body), expr[end:]
    m = re.match(r'^-?\d+(?:\.\d+)?[LlUuMmDdFf]*', expr)
    if m:
        s = re.sub(r'[LlUuMmDdFf]+$', '', m.group(0))
        return (float(s) if '.' in s else int(s)), expr[m.end():]
    m = re.match(r'^(true|false|null)\b', expr)
    if m: return {'true': True, 'false': False, 'null': None}[m.group(1)], expr[m.end():]
    if expr[0] == '(':
        close = matching(expr, 0)
        inner = expr[1:close]
        parts = split_top(inner)
        if len(parts) == 2 and not re.fullmatch(r'[\w.]+(?:\[\])?', inner.strip()):
            # A tuple: (source, "file.cs").
            return tuple(evaluate(p, ctx, before) for p in parts), expr[close + 1:]
        return evaluate(inner, ctx, before), expr[close + 1:]
    m = re.match(r'^(?:new\s*(?:[\w.]+(?:<[\w.<>, ]+>)?\s*)?(?:\[\s*\])?\s*(?:\(\s*\))?\s*\{|\[)', expr)
    if m and (expr[0] == '[' or m.group(0).startswith('new')):
        close = matching(expr, m.end() - 1)
        items = []
        for element in split_top(expr[m.end():close]):
            if element.startswith('..'):
                v = evaluate(element[2:], ctx, before)
                items.extend(v if isinstance(v, list) else [v])
            else:
                items.append(evaluate(element, ctx, before))
        return items, expr[close + 1:]
    m = re.match(r'^new\s+(\w+(?:\.\w+)*)\s*(?:<[^()]*>)?\s*\(', expr)
    if m:
        close = matching(expr, m.end() - 1)
        args = split_top(expr[m.end():close])
        return construct(m.group(1), args, ctx, before), expr[close + 1:]
    m = re.match(r'^[A-Za-z_]\w*', expr)
    if not m: raise Unsupported('expression', expr[:40])
    return None, expr   # a name: postfix() resolves it with what follows


def postfix(expr, ctx, before):
    value, rest = primary(expr, ctx, before)
    path = None     # a dotted name not yet resolved
    if value is None and rest is expr:
        m = re.match(r'^[A-Za-z_]\w*', expr)
        path = m.group(0); rest = expr[m.end():]
    while True:
        rest = rest.lstrip()
        if rest.startswith('!') and not rest.startswith('!='):
            rest = rest[1:]; continue       # null-forgiving
        m = re.match(r'^\??\.\s*([A-Za-z_]\w*)', rest)
        if m and path is not None:
            path += '.' + m.group(1); rest = rest[m.end():]; continue
        # a generic call: Name<T>(...)
        g = re.match(r'^<[\w.<>, \[\]]*>\s*(?=\()', rest)
        if g and path is not None:
            rest = rest[g.end():]
        if rest.startswith('('):
            close = matching(rest, 0)
            args = split_top(rest[1:close])
            if path is not None:
                value = call(path, None, args, ctx, before); path = None
            else:
                raise Unsupported('call of a value')
            rest = rest[close + 1:]
            continue
        if m:
            if path is not None:
                value = name_value(path, ctx, before); path = None
            name = m.group(1)
            rest = rest[m.end():].lstrip()
            g = re.match(r'^<[\w.<>, \[\]]*>\s*(?=\()', rest)
            if g: rest = rest[g.end():]
            if rest.startswith('('):
                close = matching(rest, 0)
                args = split_top(rest[1:close])
                value = method(value, name, args, ctx, before)
                rest = rest[close + 1:]
            else:
                value = prop(value, name)
            continue
        if rest.startswith('['):
            close = matching(rest, 0)
            index = evaluate(rest[1:close], ctx, before)
            if path is not None: value = name_value(path, ctx, before); path = None
            value = value[index]
            rest = rest[close + 1:]
            continue
        break
    if path is not None: value = name_value(path, ctx, before)
    if rest.strip(): raise Unsupported('expression', rest.strip()[:40])
    return value


def name_value(path, ctx, before):
    parts = path.split('.')
    if path in ('Environment.NewLine', 'System.Environment.NewLine'): return '\n'
    if path in ('string.Empty', 'String.Empty'): return ''
    if parts[0] in ('ExecutionConditionUtil', 'RuntimeUtilities', 'RuntimeInformation') or (len(parts) == 1 and parts[0] in CONDITIONS and parts[0] not in ctx.bindings):
        if parts[-1] in CONDITIONS: return CONDITIONS[parts[-1]]
        raise Unsupported('condition', path)
    if parts[0] == 'TestOptions' and len(parts) == 2: return test_options(parts[1])
    if parts[0] == 'LanguageVersion' and len(parts) == 2:
        if parts[1] in LANGUAGE_VERSIONS: return ('langversion', LANGUAGE_VERSIONS[parts[1]])
        raise Unsupported('language version', path)
    if parts[0] == 'LanguageVersionFacts' and parts[1] == 'CSharpNext': return ('langversion', 'preview')
    if parts[0] in ('OptimizationLevel',): return ('optimization', parts[1])
    if parts[0] == 'SyntaxKind' and len(parts) == 2 and parts[1] in TOKEN_KINDS:
        return Token(TOKEN_KINDS[parts[1]])
    if parts[0] == 'TargetFramework' or parts[0] == 'Verification' or parts[0] == 'OutputKind':
        return (parts[0], parts[1])
    if path == 'CSharpParseOptions.Default': return Options(langversion='default')
    if path in ('DefaultParseOptions',): return Options(langversion='default')
    if FRAMEWORK_REF.match(path): return Reference(None)
    if IL_REF.search(path): raise Unsupported('IL reference')
    if parts[0] == 'TestSources' and len(parts) == 2: return member(parts[1], 'TestSources', ctx)
    if len(parts) == 1: return lookup(parts[0], ctx, before)
    if len(parts) == 2 and (parts[0][0].islower() or parts[0].startswith('_')):
        # a variable's member
        return prop(lookup(parts[0], ctx, before), parts[1])
    # Namespace.Class.Constant
    try:
        return member(parts[-1], parts[-2], ctx)
    except Unsupported:
        # `ConvertMethod.Checked`: a member of an enum of the tests, which is
        # compared and switched on and never printed.
        if len(parts) == 2 and parts[0][:1].isupper() and parts[1][:1].isupper():
            return EnumMember(path)
        raise


def test_options(name):
    if name in PARSE_OPTIONS: return Options(langversion=PARSE_OPTIONS[name])
    if name == 'Script': raise Unsupported('script')
    m = re.fullmatch(r'(Unsafe)?(Release|Debug|ReleaseDebug|SigningRelease|SigningDebug)(Exe|Dll|Module|WinMD)(Throwing)?', name)
    if m:
        return Options(kind=m.group(3), optimize=m.group(2) in ('Release', 'ReleaseDebug', 'SigningRelease'),
                       unsafe=bool(m.group(1)))
    raise Unsupported('options', name)


def prop(value, name):
    if name == 'Length' and isinstance(value, (str, list)): return len(value)
    if isinstance(value, Compilation) and name == 'Compilation': return value
    if isinstance(value, Compilation) and name == 'SyntaxTrees': return value.trees
    if isinstance(value, Compilation) and name == 'Options': return value.options
    if isinstance(value, Tree) and name == 'Options': return value.parse
    raise Unsupported('member', name)


def construct(type_name, args, ctx, before):
    type_name = type_name.split('.')[-1]
    if type_name == 'CSharpCompilationReference':
        return Reference(evaluate(args[0], ctx, before))
    if type_name in ('CSharpTestSource',):
        return evaluate(args[0], ctx, before)
    if type_name in ('List', 'MetadataReference[]'):
        return []
    if type_name == 'CSharpParseOptions':
        o = Options(langversion='default')
        for a in args:
            m = re.match(r'languageVersion\s*:\s*(.*)', a, re.S)
            if m: o = o.with_(langversion=evaluate(m.group(1), ctx, before)[1])
            m = re.match(r'preprocessorSymbols\s*:\s*(.*)', a, re.S)
            if m: o = o.with_(symbols=list(evaluate(m.group(1), ctx, before)))
        return o
    if type_name == 'CSharpCompilationOptions':
        kind = args[0] if args else ''
        return Options(kind='Exe' if 'Console' in kind else 'Dll', optimize=False)
    raise Unsupported('new', type_name)


def named(args, name):
    for a in args:
        m = re.match(name + r'\s*:\s*', a)
        if m: return a[m.end():]
    return None


def bind_arguments(names, args):
    """Parameter name -> argument expression: a named argument by its name, any other by its
    position (which a named argument in its own position keeps, as C# 7.2 allows)."""
    out = {}
    for k, a in enumerate(args):
        m = re.match(r'^(\w+)\s*:(?!:)\s*', a)
        if m and m.group(1) in names:
            out[m.group(1)] = a[m.end():]
        elif k < len(names):
            out[names[k]] = a
    return out


def positional(args):
    return [a for a in args if not re.match(r'^\w+\s*:(?!:)', a)]


def call(path, _, args, ctx, before):
    parts = path.split('.')
    last = parts[-1]
    if last in IDENTITY or path == 'RefFieldTests.IncludeExpectedOutput':
        # IncludeExpression(bool useExpression, string output) and FieldKeywordTests'
        # IncludeExpectedOutput(bool useInit, string output) take a condition first.
        values = [evaluate(a, ctx, before) for a in args]
        if len(values) == 2:
            if last == 'IncludeExpectedOutput': return values[1] if not values[0] else None
            if last == 'IncludeExpression' and values[0] is False and isinstance(values[1], str):
                # ExpressionOptionalAndNamedArgumentsTests' reports a delegate, which prints no
                # expression: each `expression: value` line is `--: value`.
                return ''.join(('--' + line[line.index(':'):] if ':' in line else line) + '\n'
                               for line in values[1].splitlines())
            return values[1]
        return values[0]
    if parts[0] == 'RuntimeAsyncTestHelpers': raise Unsupported('runtime async')
    if path == 'SyntaxFactory.ParseToken':
        return Token(to_str(evaluate(args[0], ctx, before)).strip())
    if parts[0] == 'OperatorFacts':
        kind = evaluate(args[0], ctx, before)
        checked = evaluate(named(args, 'isChecked') or (args[1] if len(args) > 1 else 'false'), ctx, before)
        if not isinstance(kind, Token): raise Unsupported('call', path)
        table = (COMPOUND_OPERATORS if 'CompoundAssignment' in last
                 else UNARY_OPERATORS if 'Unary' in last else BINARY_OPERATORS)
        names = table.get(kind.text)
        if names is None:
            if last.endswith('IfAny'): return None
            raise Unsupported('call', path, kind.text)
        return names[1] if checked and len(names) > 1 else names[0]
    if last == 'GetOrCreateResource':
        # ResourceLoader.GetOrCreateResource(ref s_field, "NetFX.ValueTuple.X.cs"): a file of the
        # test resources, named by its path with dots.
        name = to_str(evaluate(args[-1], ctx, before))
        stem, ext = os.path.splitext(name)
        path = os.path.join(RESOURCES, *stem.split('.')) + ext
        if not os.path.exists(path): raise Unsupported('resource', name)
        return open(path, encoding='utf-8-sig').read()
    if path in ('string.Join', 'String.Join'):
        sep = to_str(evaluate(args[0], ctx, before))
        items = [evaluate(a, ctx, before) for a in args[1:]]
        if len(items) == 1 and isinstance(items[0], list): items = items[0]
        return sep.join(to_str(i) for i in items)
    if path in ('string.Concat', 'String.Concat'):
        items = [evaluate(a, ctx, before) for a in args]
        if len(items) == 1 and isinstance(items[0], list): items = items[0]
        return ''.join(to_str(i) for i in items)
    if path in ('string.Format', 'String.Format'):
        template = to_str(evaluate(args[0], ctx, before))
        values = [to_str(evaluate(a, ctx, before)) for a in args[1:]]
        if re.search(r'\{\d+[,:]', template): raise Unsupported('format')
        out = re.sub(r'\{(\d+)\}', lambda m: values[int(m.group(1))], template.replace('{{', '\0').replace('}}', '\1'))
        return out.replace('\0', '{').replace('\1', '}')
    if last in ('WithNullableEnable', 'WithNullableDisable', 'WithNullable'):
        base = positional(args)
        o = evaluate(base[0], ctx, before) if base and last != 'WithNullable' else Options(kind='Dll', optimize=False)
        return o
    if last in ('Parse', 'ParseSyntaxTree', 'ParseText', 'ParseWithRoundTripCheck'):
        text = to_str(evaluate(positional(args)[0], ctx, before)) if positional(args) else None
        path_arg = named(args, 'path') or named(args, 'filename')
        options_arg = named(args, 'options')
        rest = positional(args)[1:]
        for a in rest:
            v = evaluate(a, ctx, before)
            if isinstance(v, str): path_arg = a
            elif isinstance(v, Options): options_arg = a
        return Tree(text, to_str(evaluate(path_arg, ctx, before)) if path_arg else '',
                    evaluate(options_arg, ctx, before) if options_arg else None)
    if COMPILATION_CALL.match(last):
        return create_compilation(last, args, ctx, before)
    if parts[0] == 'ImmutableArray' and last == 'Create':
        return [evaluate(a, ctx, before) for a in args]
    if parts[0] == 'MetadataReference' and last in ('CreateFromImage', 'CreateFromStream'):
        return evaluate(args[0], ctx, before)
    if parts[0] == 'AssemblyMetadata' and last == 'CreateFromImage':
        return evaluate(args[0], ctx, before)
    if last in ('CompileIL', 'CreateMetadataReferenceFromIlSource'):
        # CompileIL(il, prependDefaultHeader = true, embedInteropTypes = false, autoInherit = true)
        bound = bind_arguments(['ilSource', 'prependDefaultHeader', 'embedInteropTypes', 'autoInherit'], args)
        if 'ilSource' not in bound: raise Unsupported('IL reference', 'no IL')
        text = evaluate(bound['ilSource'], ctx, before)
        if not isinstance(text, str): raise Unsupported('IL reference', 'IL not a string')
        flag = lambda name: evaluate(bound[name], ctx, before) is not False if name in bound else True
        if 'embedInteropTypes' in bound and evaluate(bound['embedInteropTypes'], ctx, before): raise Unsupported('embedded interop types')
        return Reference(IL(text, flag('prependDefaultHeader'), flag('autoInherit')))
    if IL_REF.search(path): raise Unsupported('IL reference')
    if last in PORTED and (len(parts) == 1 or parts[0] == 'CSharpTestBase'):
        return ported(last, args, ctx, before)
    if len(parts) <= 2 and HELPERS.get(last) and (len(parts) == 1 or parts[0][0].isupper()):
        try:
            return helper(last, parts[0] if len(parts) == 2 else None, args, ctx, before)
        except Unsupported:
            if len(parts) == 1: raise
    if len(parts) >= 2:
        return method(name_value('.'.join(parts[:-1]), ctx, before), last, args, ctx, before)
    raise Unsupported('call', path)


def method(value, name, args, ctx, before):
    """`value.name(args)`."""
    if isinstance(value, str):
        if name == 'Replace':
            a, b = (to_str(evaluate(x, ctx, before)) for x in args[:2])
            return value.replace(a, b)
        if name == 'Trim' and not args: return value.strip()
        if name == 'TrimEnd' and not args: return value.rstrip()
        if name == 'TrimStart' and not args: return value.lstrip()
        if name == 'ToString': return value
        if name == 'Substring':
            nums = [evaluate(a, ctx, before) for a in args]
            return value[nums[0]:] if len(nums) == 1 else value[nums[0]:nums[0] + nums[1]]
        if name == 'NormalizeLineEndings': return value.replace('\r\n', '\n')
        if name in ('Contains', 'StartsWith', 'EndsWith'):
            other = to_str(evaluate(args[0], ctx, before))
            return {'Contains': other in value, 'StartsWith': value.startswith(other), 'EndsWith': value.endswith(other)}[name]
        if name in ('ToUpper', 'ToUpperInvariant'): return value.upper()
        if name in ('ToLower', 'ToLowerInvariant'): return value.lower()
    if isinstance(value, (bool, int)) and name == 'ToString': return to_str(value)
    if isinstance(value, Options):
        arg = lambda: evaluate(args[0], ctx, before)
        if name == 'WithLanguageVersion': return value.with_(langversion=arg()[1])
        if name == 'WithPreprocessorSymbols':
            symbols = [evaluate(a, ctx, before) for a in args]
            if len(symbols) == 1 and isinstance(symbols[0], list): symbols = symbols[0]
            return value.with_(symbols=list(value.kv.get('symbols', [])) + [to_str(s) for s in symbols])
        if name == 'WithMainTypeName': return value.with_(main=arg())
        if name == 'WithAllowUnsafe': return value.with_(unsafe=arg())
        if name == 'WithOverflowChecks': return value.with_(checked=arg())
        if name == 'WithOptimizationLevel': return value.with_(optimize=arg()[1] == 'Release')
        if name == 'WithOutputKind': return value.with_(kind='Exe' if 'Console' in arg()[1] else 'Dll')
        if name == 'WithFeature':
            feature = to_str(evaluate(args[0], ctx, before))
            if feature in ('runtime-async',): raise Unsupported('runtime async')
            return value.with_(features=value.kv.get('features', []) + [feature])
        if name == 'WithScriptClassName': raise Unsupported('script')
        # Options that do not change what the program prints.
        return value
    if isinstance(value, Compilation):
        if name in ('EmitToImageReference', 'ToMetadataReference'):
            given = named(args, 'aliases')
            return Reference(value, aliases_of(evaluate(given, ctx, before)) if given else ())
        if name in ('EmitToArray', 'EmitToStream'): return Reference(value)
        if name == 'WithOptions': return Compilation(value.trees, value.refs, evaluate(args[0], ctx, before), value.parse)
        if name in ('VerifyDiagnostics', 'VerifyEmitDiagnostics', 'VerifyTypes', 'VerifyIL'): return value
        if name == 'AddSyntaxTrees':
            trees = [evaluate(a, ctx, before) for a in args]
            return Compilation(value.trees + [t for x in trees for t in (x if isinstance(x, list) else [x])], value.refs, value.options, value.parse)
        if name == 'AddReferences':
            refs = [evaluate(a, ctx, before) for a in args]
            return Compilation(value.trees, value.refs + flatten_refs(refs), value.options, value.parse)
    if isinstance(value, Reference) and name == 'GetReference': return value
    if isinstance(value, Token) and name == 'Kind': return value
    if isinstance(value, Reference) and name == 'WithAliases':
        return Reference(value.compilation, aliases_of([evaluate(a, ctx, before) for a in args]))
    if isinstance(value, list):
        if name in ('ToArray', 'ToList', 'ToImmutableArray', 'AsImmutable', 'ToImmutable'): return value
        if name in ('Concat', 'AddRange', 'Add', 'Append'):
            other = evaluate(args[0], ctx, before)
            return value + (other if isinstance(other, list) else [other])
    raise Unsupported('method', name)


def aliases_of(value):
    """The alias names an `aliases:` argument or a `WithAliases(...)` call gives."""
    out = []
    for v in value if isinstance(value, list) else [value]:
        if isinstance(v, list): out.extend(aliases_of(v))
        elif isinstance(v, str) and re.fullmatch(r'\w+', v): out.append(v)
        else: raise Unsupported('alias', repr(v)[:40])
    return out


def flatten_refs(values):
    out = []
    for v in values if isinstance(values, list) else [values]:
        if isinstance(v, list): out.extend(flatten_refs(v))
        elif isinstance(v, Reference):
            if v.compilation is not None: out.append(v)
        else: raise Unsupported('reference not found', repr(v)[:40])
    return out


def trees_of(value, parse):
    """The source trees a `CSharpTestSource` value makes."""
    if value is None: return []
    if isinstance(value, str): return [Tree(value, '', parse)]
    if isinstance(value, Tree): return [Tree(value.text, value.path, value.parse or parse)]
    if isinstance(value, tuple) and len(value) == 2 and isinstance(value[0], str):
        return [Tree(value[0], to_str(value[1]), parse)]
    if isinstance(value, list):
        return [t for v in value for t in trees_of(v, parse)]
    raise Unsupported('source', repr(value)[:40])


def create_compilation(kind, args, ctx, before):
    """The compilation `kind(args)` makes: CreateCompilation, CompileAndVerify and their kin."""
    if kind == 'CompileAndVerifyFunctionPointers':
        # CodeGenFunctionPointersTests' own: an unsafe executable in the preview language.
        bound = bind_arguments(['sources', 'references', 'symbolValidator', 'expectedOutput',
                                'targetFramework', 'options'], args)
        args = [f'source: {bound["sources"]}', 'parseOptions: TestOptions.RegularPreview',
                'options: ' + bound.get('options', 'TestOptions.UnsafeReleaseExe')]
        args += [f'{n}: {bound[n]}' for n in ('references', 'targetFramework') if n in bound]
        kind = 'CreateCompilation'
    elif kind == 'CompileAndVerifyFunctionPointersWithIl':
        bound = bind_arguments(['source', 'ilStub'], args)
        args = [f'source: {bound["source"]}', f'ilSource: {bound["ilStub"]}',
                'parseOptions: TestOptions.RegularPreview', 'options: TestOptions.UnsafeReleaseExe']
        kind = 'CreateCompilationWithIL'
    fixed = positional(args)
    first = named(args, 'source') or named(args, 'text') or named(args, 'compilation') or (fixed[0] if fixed else None)
    if first is None: raise Unsupported('no source')
    target = named(args, 'targetFramework')
    if target and OTHER_FRAMEWORK.search(target):
        raise Unsupported('other framework')
    il = None
    if 'WithIL' in kind:
        # CreateCompilationWithIL(source, ilSource, targetFramework, references, options,
        # parseOptions, appendDefaultHeader): the IL is one more reference.
        if kind != 'CreateCompilationWithIL': raise Unsupported('IL reference', kind)
        bound = bind_arguments(['source', 'ilSource', 'targetFramework', 'references', 'options',
                                'parseOptions', 'appendDefaultHeader'], args)
        text = evaluate(bound['ilSource'], ctx, before)
        if not isinstance(text, str): raise Unsupported('IL reference', 'IL not a string')
        header = evaluate(bound['appendDefaultHeader'], ctx, before) is not False if 'appendDefaultHeader' in bound else True
        il = Reference(IL(text, header))
        if 'targetFramework' in bound and OTHER_FRAMEWORK.search(bound['targetFramework']):
            raise Unsupported('other framework')
        # The same compilation, its arguments named.
        args = [f'{n}: {bound[n]}' for n in ('source', 'references', 'options', 'parseOptions') if n in bound]
        fixed = []
        kind = 'CreateCompilation'
    source = evaluate(first, ctx, before)
    parse_expr = named(args, 'parseOptions')
    options_expr = named(args, 'options')
    refs_expr = named(args, 'references')
    if refs_expr is None and len(fixed) > 1 and not kind.startswith('CompileAndVerify') or (kind.startswith('CompileAndVerify') and not isinstance(source, Compilation) and len(fixed) > 1 and refs_expr is None):
        refs_expr = fixed[1]
    if not kind.startswith('CompileAndVerify') and len(fixed) > 2 and options_expr is None: options_expr = fixed[2]
    if not kind.startswith('CompileAndVerify') and len(fixed) > 3 and parse_expr is None: parse_expr = fixed[3]
    parse = evaluate(parse_expr, ctx, before) if parse_expr else None
    options = evaluate(options_expr, ctx, before) if options_expr else None
    if parse is not None and not isinstance(parse, Options): raise Unsupported('parse options')
    if options is not None and not isinstance(options, Options): raise Unsupported('options')
    refs = flatten_refs(evaluate(refs_expr, ctx, before)) if refs_expr else []
    if il is not None: refs.append(il)
    if isinstance(source, Compilation):
        return Compilation(source.trees, source.refs + refs, options or source.options, source.parse)
    if kind.startswith('CompileAndVerify') and options is None:
        # CompileAndVerify(source, expectedOutput: ...) makes an optimized executable.
        options = Options(kind='Exe', optimize=True)
    if options is None: options = Options(kind='Dll', optimize=False)
    return Compilation(trees_of(source, parse), refs, options, parse)


# ---------------------------------------------------------------------------------------------
# Writing a test.

def has_entry_point(texts):
    """Whether one of the sources has a Main method or top-level statements."""
    for text in texts:
        if re.search(r'\bMain\s*\(', text): return True
        masked = mask(text)
        depth = 0
        for line in masked.split('\n'):
            stripped = line.strip()
            if depth == 0 and stripped and not stripped.startswith('#'):
                word = re.match(r'^[\w@]+', stripped)
                if word and word.group(0) not in DECLARATION_WORDS and not stripped.startswith(('[', '}', '{', ':', ',', ')', '<')):
                    return True
            for ch in masked_line_code(line):
                if ch in '({[': depth += 1
                elif ch in ')}]': depth -= 1
    return False


def masked_line_code(line):
    return re.sub(r'//.*', '', line)


DECLARATION_WORDS = {'using', 'namespace', 'class', 'struct', 'interface', 'enum', 'record', 'delegate',
                     'public', 'private', 'protected', 'internal', 'static', 'abstract', 'sealed', 'partial',
                     'file', 'readonly', 'ref', 'unsafe', 'extern', 'new', 'where', 'global', 'extension',
                     'virtual', 'override', 'async', 'const', 'volatile', 'implicit', 'explicit', 'operator'}


def options_lines(options, parse, trees):
    lines = []
    lang = parse.kv.get('langversion') if parse else None
    if lang and lang != 'default': lines += ['--langversion', lang]
    symbols = parse.kv.get('symbols') if parse else None
    if symbols: lines += ['--define', ';'.join(symbols)]
    if options:
        if options.kv.get('optimize'): lines.append('--optimize')
        if options.kv.get('main'): lines += ['--main', to_str(options.kv['main'])]
        if options.kv.get('checked'): lines.append('--checked')
        if options.kv.get('unsafe'): lines.append('--unsafe')
    # The name of a file-local type hashes the path of its file, which is
    # empty unless the test gives one.
    file_types = any(re.search(FILE_TYPE, tree.text) for tree in trees)
    for k, tree in enumerate(trees):
        if tree.path or file_types: lines += ['--path', str(k), tree.path]
    return lines


FILE_TYPE = r'(?m)^\s*(?:\w+\s+)*file\s+(?:\w+\s+)*(?:class|struct|interface|enum|record|delegate)\b'


def tree_parse(compilation):
    parses = {id(t.parse): t.parse for t in compilation.trees if t.parse is not None}
    if len(parses) > 1:
        versions = {p.kv.get('langversion') for p in parses.values()}
        if len(versions) > 1: raise Unsupported('mixed parse options')
    return next(iter(parses.values()), None) or compilation.parse


def libraries(compilation, seen=None):
    """The libraries (C# compilations or `IL`) `compilation` references, directly or not, in build
    order, each with the `extern alias`es it is referenced under. The same library under other
    aliases is another reference."""
    out = [] if seen is None else seen
    for ref in compilation.refs:
        lib = ref.compilation
        libraries(lib, out)
        if all(lib is not other or ref.aliases != aliases for other, aliases in out):
            out.append((lib, ref.aliases))
    return out


def il_file(il, assembly):
    """The `.il` an IL library is written as, for an assembly of this name. run.sh reads how to
    call ilasm from its first line."""
    text = il.text
    if il.header:
        text = (f".assembly '{assembly}' {{}}\n\n.assembly extern mscorlib\n{{\n"
                "  .publickeytoken = (B7 7A 5C 56 19 34 E0 89)\n  .ver 4:0:0:0\n}\n\n" + text)
    else:
        text = text.replace('<<GeneratedFileName>>', assembly)
    return ('// cav-ilasm: -noautoinherit\n' if not il.inherit else '// cav-ilasm:\n') + text


ALIASES_MARK = '// cav-aliases: '


def write(base, compilation, expected, run_args=(), code=None):
    if not compilation.trees: raise Unsupported('no source')
    texts = [t.text for t in compilation.trees]
    if any(not isinstance(t, str) for t in texts): raise Unsupported('source')
    if compilation.options and compilation.options.kv.get('kind') in ('Dll', 'Module', 'WinMD') and not has_entry_point(texts):
        raise Unsupported('no Main')
    if not has_entry_point(texts): raise Unsupported('no Main')
    libs = libraries(compilation)
    for lib, _ in libs:
        if not lib.trees and not isinstance(lib, IL): raise Unsupported('reference not found')
    files = {}
    for k, tree in enumerate(compilation.trees):
        files[f'{base}.cs' if k == 0 else f'{base}.part{k}.cs'] = tree.text
    files[base + '.expected'] = expected
    if run_args: files[base + '.args'] = ''.join(a + '\n' for a in run_args)
    if code is not None: files[base + '.exitcode'] = f'{code}\n'
    lines = options_lines(compilation.options, tree_parse(compilation), compilation.trees)
    if lines: files[base + '.options'] = '\n'.join(lines) + '\n'
    for k, (lib, aliases) in enumerate(libs):
        if isinstance(lib, IL):
            files[f'{base}.ref{k}.il'] = il_file(lib, f'{base}.ref{k}')
            continue
        for j, tree in enumerate(lib.trees):
            # A library referenced under `extern alias`es says so on its first line, which
            # run.sh passes on as `--reference A,B=lib.dll`.
            marked = ALIASES_MARK + ','.join(aliases) + '\n' if aliases and j == 0 else ''
            files[f'{base}.ref{k}.cs' if j == 0 else f'{base}.ref{k}.part{j}.cs'] = marked + tree.text
        lines = options_lines(lib.options, tree_parse(lib), lib.trees)
        lines = [l for l in lines if l != '--optimize']
        if lines: files[f'{base}.ref{k}.options'] = '\n'.join(lines) + '\n'
    for name, content in files.items():
        with open(os.path.join(OUT, name), 'w') as f: f.write(content)
    return bool(libs)


# ---------------------------------------------------------------------------------------------
# Test methods, theories and the calls in them.

# $CAV_CALL replaces the call looked for: CodeGenFunctionPointersTests go through their own
# `CompileAndVerifyFunctionPointers`.
CALL = re.compile(r'\b(' + os.environ['CAV_CALL'] + r')\s*(?:<\w+>)?\s*\(') if os.environ.get('CAV_CALL') else re.compile(r'\b(CompileAndVerify(?:WithMscorlib\d+|WithCSharp|WithMscorlib40|WithMscorlib46|Experimental|WithWinRt|WithIndexAndRange|OnCoreClr|WithTasksExtensions)?)\s*(?:<\w+>)?\s*\(')
METHOD = re.compile(r'\b(?:public|internal|private)\s+(?:async\s+)?(?:void|Task)\s+(\w+)\s*\(')


def block_header_start(masked, brace):
    """Where the statement a block at `brace` belongs to starts: `if (x is { } y) {` is one
    header however many braces its condition has."""
    j = brace - 1
    while j >= 0 and masked[j].isspace(): j -= 1
    if j >= 0 and masked[j] == ')':
        depth = 0
        while j >= 0:
            if masked[j] == ')': depth += 1
            elif masked[j] == '(':
                depth -= 1
                if depth == 0: break
            j -= 1
        k = j - 1
        while k >= 0 and masked[k].isspace(): k -= 1
        word = re.search(r'(?:else\s+)?(?:if|foreach|for|while|switch|using|lock|fixed|await\s+foreach|catch)\s*$', masked[max(0, k - 20):k + 1])
        if word:
            return max(0, k - 20) + word.start()
    return max(masked.rfind(';', 0, brace), masked.rfind('{', 0, brace), masked.rfind('}', 0, brace)) + 1


def enclosing_loops(source, body_start, at):
    """The `foreach (var x in collection)` loops around `at`, outermost first: (variable,
    collection expression, position)."""
    masked, text = source.masked, source.text
    stack = []
    for i in range(body_start, at):
        ch = masked[i]
        if ch == '{':
            header_start = block_header_start(masked, i)
            m = re.fullmatch(r'foreach\s*\(\s*(?:var|[\w.<>\[\]?]+)\s+(\w+)\s+in\s+(.*)\)', text[header_start:i].strip(), re.S)
            stack.append((m.group(1), m.group(2), header_start) if m else None)
        elif ch == '}' and stack:
            stack.pop()
    return [loop for loop in stack if loop is not None]


def inline_rows(source, attrs_start, method_start):
    """The argument lists of the method's [InlineData(...)] attributes."""
    region = source.text[attrs_start:method_start]
    rows = []
    masked = source.masked[attrs_start:method_start]
    for m in re.finditer(r'InlineData\s*\(', masked):
        close = matching(region, m.end() - 1)
        rows.append(split_top(region[m.end():close]))
    return rows


def parameters(text):
    return [name for _, name, _ in parameters_full(text)]


def parameters_full(text):
    """(type, name, default) of each parameter; the type keeps any attributes before it."""
    out = []
    # Generic types have commas of their own: `Func<int, string> f = null`.
    parts, start, angle = [], 0, 0
    for i, ch, depth in scan(text):
        if ch == '<': angle += 1
        elif ch == '>' and angle: angle -= 1
        elif ch == ',' and depth == 0 and angle == 0:
            parts.append(text[start:i]); start = i + 1
    parts.append(text[start:])
    for p in (p.strip() for p in parts if p.strip()):
        default = None
        for i, ch, depth in scan(p):
            if depth == 0 and ch == '=' and p[i + 1:i + 2] != '=' and p[i - 1] not in '=!<>':
                default = p[i + 1:].strip(); p = p[:i].strip(); break
        m = re.search(r'(\w+)$', p)
        if m: out.append((p[:m.start()].strip(), m.group(1), default))
    return out


def combinatorial_rows(source, text, attrs_start, method_start):
    """The rows of a [CombinatorialData] theory: every combination of its bool parameters and the
    values its [CombinatorialValues(...)] parameters list, the first parameter varying slowest."""
    if not re.search(r'\bCombinatorialData\b', source.masked[attrs_start:method_start]): return None
    choices = []
    for ptype, pname, _ in parameters_full(text):
        values = re.match(r'\[\s*CombinatorialValues\s*\(', ptype)
        if values:
            close = matching(ptype, values.end() - 1)
            choices.append(split_top(ptype[values.end():close]))
        elif re.sub(r'\[.*\]\s*', '', ptype) in ('bool',):
            choices.append(['false', 'true'])
        else:
            raise Unsupported('theory arguments')
    rows = [[]]
    for c in choices:
        rows = [r + [v] for r in rows for v in c]
    return rows


def main():
    os.makedirs(OUT, exist_ok=True)
    tests = []
    for dirpath, dirs, files in os.walk(ROOT):
        dirs.sort()
        for f in sorted(files):
            if f.endswith('.cs'): tests.append(os.path.join(dirpath, f))
    utilities = []
    for root in UTILITIES:
        if root.endswith('.cs'): utilities.append(root)
        for dirpath, dirs, files in os.walk(root):
            dirs.sort()
            for f in sorted(files):
                if f.endswith('.cs'): utilities.append(os.path.join(dirpath, f))
    sources = [Source(p) for p in tests + utilities]
    index_constants(sources)
    total = written = with_refs = with_options = with_parts = 0
    skipped = {}
    names = set()

    def skip(kind, base, detail=()):
        skipped[kind] = skipped.get(kind, 0) + 1
        if VERBOSE: print(f'{base}: skipped, {kind} {detail}')

    def extract(base, source, c, body_start, ctx):
        """Writes the test of the CompileAndVerify call `c` (a match in the method body starting at
        `body_start`) as `base`, its names evaluated in `ctx`; once per iteration where the call is
        in `foreach` loops over lists the test writes out (`_<k>` for the k-th)."""
        loops = enclosing_loops(source, body_start, body_start + c.start())
        if not loops:
            return extract_one(base, source, c, body_start, ctx)
        rows = [{}]
        try:
            for variable, collection, at in loops:
                row_ctx = Context(ctx.source, ctx.start, ctx.end, dict(ctx.bindings), ctx.body_start)
                expanded = []
                for row in rows:
                    row_ctx.bindings.update(row)
                    items = evaluate(collection, row_ctx, at)
                    if not isinstance(items, list): raise Unsupported('loop')
                    expanded += [dict(row, **{variable: item}) for item in items]
                rows = expanded
        except (Unsupported, KeyError, IndexError, ValueError, TypeError, AttributeError, RecursionError):
            # A loop over what cannot be listed here: the call is the same
            # test each time, unless it names the loop's variable — and then
            # it cannot be evaluated either.
            return extract_one(base, source, c, body_start, ctx)
        for k, row in enumerate(rows, 1):
            bindings = dict(ctx.bindings)
            bindings.update(row)
            extract_one(f'{base}_{k}', source, c, body_start,
                        Context(ctx.source, ctx.start, ctx.end, bindings, ctx.body_start))

    def extract_one(base, source, c, body_start, ctx):
        nonlocal written, with_refs
        text = source.text
        call_at = body_start + c.start()
        open_at = body_start + c.end() - 1
        if base in names:
            n = 2
            while f'{base}_{n}' in names: n += 1
            base = f'{base}_{n}'
        try:
            if ctx.reachable(call_at) is False: raise Unsupported('not reached')
            close = matching(text, open_at)
            args = split_top(text[open_at + 1:close])
            eo = named(args, 'expectedOutput')
            if eo is None: raise Unsupported('no expectedOutput')
            expected = evaluate(eo, ctx, call_at)
            if expected is None: raise Unsupported('expectedOutput null')
            if not isinstance(expected, str): raise Unsupported('expectedOutput not a string')
            run_args = named(args, 'args')
            run_args = evaluate(run_args, ctx, call_at) if run_args is not None else []
            if not isinstance(run_args, list) or not all(isinstance(a, str) for a in run_args):
                raise Unsupported('command-line arguments')
            code = named(args, 'expectedReturnCode')
            code = evaluate(code, ctx, call_at) if code is not None else None
            if code is not None and not isinstance(code, int): raise Unsupported('return code')
            compilation = create_compilation(c.group(1), args, ctx, call_at)
            refs = write(base, compilation, expected, run_args, code)
        except Unsupported as reason:
            skip(reason.args[0], base, reason.args[1:])
            return
        except RecursionError:
            skip('recursion', base)
            return
        except (KeyError, IndexError, ValueError, TypeError, AttributeError) as error:
            # C# this evaluator reads wrongly: a test it cannot extract rather than a
            # reason to stop.
            skip('unevaluated', base, (repr(error),))
            return
        names.add(base)
        written += 1
        with_refs += refs

    only = os.environ.get('CAV_ONLY')
    for source in sources[:len(tests)]:
        text, masked = source.text, source.masked
        stem = os.path.splitext(os.path.basename(source.path))[0]
        if only and not re.fullmatch(only, stem): continue
        methods = []
        found = list(METHOD.finditer(masked))
        for k, m in enumerate(found):
            open_paren = m.end() - 1
            try:
                close_paren = matching(text, open_paren)
            except Unsupported:
                continue
            end = found[k + 1].start() if k + 1 < len(found) else len(text)
            # The method's attributes: what follows the member before it.
            attrs_start = max(masked.rfind('}', 0, m.start()), masked.rfind(';', 0, m.start()),
                              masked.rfind('{', 0, m.start())) + 1
            params = parameters_full(text[open_paren + 1:close_paren])
            is_test = bool(re.search(r'\[\s*(?:\w+\s*,\s*)*(?:Conditional)?(?:Fact|Theory)\b|\b(?:Fact|Theory)\s*[,\]]',
                                     masked[attrs_start:m.start()]))
            calls = list(CALL.finditer(masked[close_paren + 1:end]))
            methods.append(dict(name=m.group(1), start=m.start(), open=open_paren, close=close_paren,
                                end=end, attrs=attrs_start, params=params, test=is_test, calls=calls))
        # A helper with parameters holding CompileAndVerify runs once per call of it from a test.
        helpers = {}
        for h in methods:
            if h['params'] and not h['test'] and h['calls']:
                helpers.setdefault(h['name'], []).append(h)

        def overload(candidates, args, ctx, at):
            """The one helper of the name that the arguments fit, by their count and names, and
            where that leaves more than one, by whether each argument is a string."""
            fits = []
            for h in candidates:
                names_ = [name for _, name, _ in h['params']]
                given = bind_arguments(names_, args)
                named_ok = all(not re.match(r'^(\w+)\s*:(?!:)', a) or re.match(r'^(\w+)', a).group(1) in names_ for a in args)
                variadic = any(t.startswith('params') for t, _, _ in h['params'])
                required = all(n in given or d is not None or t.startswith('params') for t, n, d in h['params'])
                if named_ok and required and (len(args) <= len(names_) or variadic):
                    fits.append(h)
            if len(fits) > 1:
                def typed(h):
                    names_ = [name for _, name, _ in h['params']]
                    types = {name: re.sub(r'\[.*?\]\s*', '', t) for t, name, _ in h['params']}
                    for pname, expr in bind_arguments(names_, args).items():
                        try:
                            value = evaluate(expr, ctx, at)
                        except (Unsupported, KeyError, IndexError, ValueError, TypeError, AttributeError, RecursionError):
                            value = Unsupported
                        stringly = types[pname].rstrip('?') in ('string', 'String', 'object', 'CSharpTestSource')
                        if isinstance(value, str) and not stringly: return False
                        if value is not Unsupported and value is not None and not isinstance(value, str) and types[pname].rstrip('?') in ('string', 'String'):
                            return False
                        if value is Unsupported and types[pname].rstrip('?') in ('string', 'String'):
                            return False
                    return True
                fits = [h for h in fits if typed(h)]
            return fits[0] if len(fits) == 1 else None

        for method in methods:
            params = [name for _, name, _ in method['params']]
            body_start = method['close'] + 1
            if params and not method['test'] and method['calls']:
                continue
            rows = [None]
            if params:
                try:
                    rows = (inline_rows(source, method['attrs'], method['start'])
                            or combinatorial_rows(source, text[method['open'] + 1:method['close']], method['attrs'], method['start'])
                            or [None])
                except Unsupported:
                    rows = [None]
            contexts = []
            for row_index, row in enumerate(rows, 1):
                suffix = '' if row is None else f'_{row_index}'
                bindings = {}
                try:
                    if row is not None:
                        if len(row) != len(params): raise Unsupported('theory arguments')
                        empty = Context(source, None, None)
                        for p, a in zip(params, row):
                            bindings[p] = evaluate(a, empty, 0)
                except Unsupported as reason:
                    for ordinal, _ in enumerate(method['calls'], 1):
                        total += 1
                        skip(reason.args[0], f"{stem}_{method['name']}_{ordinal}{suffix}", reason.args[1:])
                    continue
                contexts.append((suffix, Context(source, method['attrs'], method['end'], bindings, body_start)))
            for ordinal, c in enumerate(method['calls'], 1):
                total += 1
                for suffix, ctx in contexts:
                    extract(f"{stem}_{method['name']}_{ordinal}{suffix}", source, c, body_start, ctx)
            # The helpers this method calls.
            if not helpers: continue
            site_ordinal = {}
            for site in re.finditer(r'(?<![\w.])(' + '|'.join(map(re.escape, helpers)) + r')\s*\(', masked[body_start:method['end']]):
                site_at = body_start + site.start()
                site_ordinal[site.group(1)] = site_ordinal.get(site.group(1), 0) + 1
                paren = body_start + site.end() - 1
                try:
                    site_args = split_top(text[paren + 1:matching(text, paren)])
                except Unsupported:
                    continue
                helper_method = overload(helpers[site.group(1)], site_args, contexts[0][1] if contexts else None, site_at)
                if helper_method is None:
                    skip('helper overload', f"{stem}_{method['name']}_{site.group(1)}{site_ordinal[site.group(1)]}")
                    continue
                helper_names = [name for _, name, _ in helper_method['params']]
                given = bind_arguments(helper_names, site_args)
                for suffix, ctx in contexts:
                    base_prefix = f"{stem}_{method['name']}_{site.group(1)}{site_ordinal[site.group(1)]}"
                    helper_bindings = {}
                    try:
                        if ctx.reachable(site_at) is False: raise Unsupported('not reached')
                        for ptype, pname, default in helper_method['params']:
                            if pname in given:
                                helper_bindings[pname] = Lazy(given[pname], ctx, site_at)
                            elif default is not None:
                                helper_bindings[pname] = evaluate(default, Context(source, None, None), 0)
                            elif ptype.startswith('params'):
                                helper_bindings[pname] = []
                            else:
                                raise Unsupported('helper arguments')
                    except Unsupported as reason:
                        for ordinal, _ in enumerate(helper_method['calls'], 1):
                            total += 1
                            skip(reason.args[0], f'{base_prefix}_{ordinal}{suffix}', reason.args[1:])
                        continue
                    except (KeyError, IndexError, ValueError, TypeError, AttributeError, RecursionError) as error:
                        skip('unevaluated', base_prefix, (repr(error),))
                        continue
                    helper_ctx = Context(source, helper_method['attrs'], helper_method['end'], helper_bindings,
                                         helper_method['close'] + 1)
                    for ordinal, c in enumerate(helper_method['calls'], 1):
                        total += 1
                        extract(f'{base_prefix}_{ordinal}{suffix}', source, c, helper_method['close'] + 1, helper_ctx)
    print(f'calls: {total}, extracted: {written} ({with_refs} with references)')
    for kind, count in sorted(skipped.items(), key=lambda kv: -kv[1]):
        print(f'  skipped {kind}: {count}')


if __name__ == '__main__':
    sys.setrecursionlimit(3000)
    main()
