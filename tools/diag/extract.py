#!/usr/bin/env python3
"""Extracts diagnostics tests from Roslyn's C# test sources: a compilation made from one source
text and the diagnostics Roslyn is expected to report for it,

    CreateCompilation(source[, options: ...]).VerifyDiagnostics(
        // (6,13): error CS0165: Use of unassigned local variable 'x'
        Diagnostic(ErrorCode.ERR_UseDefViolation, "x").WithArguments("x").WithLocation(6, 13));

into <name>.cs and <name>.diag. The .diag file starts with `# key: value` lines (where the test
came from, the options it was compiled with) and then lists one expected diagnostic per line,
tab-separated: severity, code (CS0165), line, column (both 1-based, 0 when the test gives no
location) and the text the diagnostic points at (JSON-quoted). `VerifyDiagnostics()` with no
arguments is a test too: a program that has to compile without any diagnostic.

Only what can be reproduced against the current framework is taken: a single source text (a
literal, or a variable holding one), no references beyond the framework, the latest language
version, and options that say no more than exe/dll, unsafe and nullable. Everything else is
counted as skipped, by reason. Names are numbered over every call found, so a name means the
same test whatever this script learns to extract.

The output directory is $DIAG_TESTS (default /home/user/diag/tests)."""
import hashlib, json, os, re, sys

ROSLYN = os.environ.get('ROSLYN', '/home/user/roslyn')
ROOT = os.path.join(ROSLYN, 'src/Compilers/CSharp/Test')
ERROR_CODES = os.path.join(ROSLYN, 'src/Compilers/CSharp/Portable/Errors/ErrorCode.cs')
OUT = os.environ.get('DIAG_TESTS', '/home/user/diag/tests')


def error_codes():
    """ErrorCode member name -> number, from Roslyn's own enum."""
    codes = {}
    for m in re.finditer(r'^\s*(\w+)\s*=\s*(\d+)\s*,', open(ERROR_CODES, encoding='utf-8-sig').read(), re.M):
        codes[m.group(1)] = int(m.group(2))
    return codes


def parse_string_literal(text, at):
    """Parses a C# string literal starting at `at`; returns (value, end) or None."""
    if text.startswith('null', at):
        return None
    if text.startswith('@"', at):
        i = at + 2
        out = []
        while i < len(text):
            c = text[i]
            if c == '"':
                if i + 1 < len(text) and text[i + 1] == '"':
                    out.append('"'); i += 2; continue
                return ''.join(out), i + 1
            out.append(c); i += 1
        return None
    if text.startswith('"""', at):
        m = re.match(r'"{3,}', text[at:])
        quotes = m.group(0)
        i = at + len(quotes)
        end = text.find(quotes, i)
        if end < 0: return None
        body = text[i:end]
        # A multi-line raw string loses the indentation of its closing line.
        if '\n' in body:
            lines = body.split('\n')
            last = lines[-1]
            indent = len(last) - len(last.lstrip(' '))
            lines = lines[1:-1] if lines[0].strip() == '' else lines[:-1]
            body = '\n'.join(l[indent:] if l.startswith(' ' * indent) else l.lstrip(' ') for l in lines)
        return body, end + len(quotes)
    if text.startswith('"', at):
        i = at + 1
        out = []
        while i < len(text):
            c = text[i]
            if c == '\\':
                n = text[i + 1]
                simple = {'n': '\n', 'r': '\r', 't': '\t', '"': '"', '\\': '\\', '0': '\0', "'": "'"}
                if n in simple: out.append(simple[n])
                elif n == 'u':
                    out.append(chr(int(text[i + 2:i + 6], 16))); i += 6; continue
                else: return None
                i += 2; continue
            if c == '"':
                return ''.join(out), i + 1
            if c == '\n': return None
            out.append(c); i += 1
        return None
    return None


def skip_literal(text, i):
    """The end of a string or char literal starting at `i`, or None when there is none there."""
    ch = text[i]
    if ch == '"' or text.startswith('@"', i):
        p = parse_string_literal(text, i)
        if p is None: raise Unsupported('unparsed literal')
        return p[1]
    if ch == "'":
        m = re.match(r"'(?:\\.|[^'\\])+'", text[i:i + 12])
        if m: return i + m.end()
    if text.startswith('//', i):
        end = text.find('\n', i)
        return len(text) if end < 0 else end
    return None


class Unsupported(Exception):
    """A test this extraction cannot reproduce; the message is the reason."""


def matching(text, at):
    """The index of the bracket closing the one at `at` (literals skipped), or None."""
    pairs = {'(': ')', '[': ']', '{': '}'}
    stack = []
    i = at
    while i < len(text):
        end = skip_literal(text, i)
        if end is not None:
            i = end; continue
        ch = text[i]
        if ch in pairs: stack.append(pairs[ch])
        elif ch in ')]}':
            if not stack or stack.pop() != ch: return None
            if not stack: return i
        i += 1
    return None


def split_top(text):
    """Splits on the commas outside any brackets and literals; comments dropped."""
    parts, depth, start, i = [], 0, 0, 0
    while i < len(text):
        end = skip_literal(text, i)
        if end is not None:
            i = end; continue
        ch = text[i]
        if ch in '([{': depth += 1
        elif ch in ')]}': depth -= 1
        elif ch == ',' and depth == 0:
            parts.append(text[start:i]); start = i + 1
        i += 1
    parts.append(text[start:])
    parts = [re.sub(r'^\s*(//[^\n]*\n\s*)*', '', p).strip() for p in parts]
    return [p for p in parts if p and not p.startswith('//')]


def named(args, name):
    for a in args:
        m = re.match(name + r'\s*:\s*', a)
        if m: return a[m.end():]
    return None


def assignment(body, name, before):
    """The right-hand side of the last `name = ...;` before `before`, and where it starts."""
    found = None
    for m in re.finditer(r'(?<![\w.])' + re.escape(name) + r'\s*=(?![=>])\s*', body[:before]):
        found = m
    if not found: return None
    i = found.end(); depth = 0
    while i < len(body):
        end = skip_literal(body, i)
        if end is not None:
            i = end; continue
        ch = body[i]
        if ch in '([{': depth += 1
        elif ch in ')]}': depth -= 1
        elif ch == ';' and depth == 0: return body[found.end():i].strip(), found.start()
        i += 1
    return None


# Sources Roslyn's tests add for types that netstandard lacks and .NET 10 has:
# against .NET 10 they declare nothing new, so the test is the one file beside
# them.
FRAMEWORK_SOURCES = {
    'CompilerFeatureRequiredAttribute', 'IsExternalInitTypeDefinition',
    'InterpolatedStringHandlerArgumentAttribute', 'InterpolatedStringHandlerAttribute',
    'UnscopedRefAttributeDefinition', 'MaybeNullAttributeDefinition', 'AllowNullAttributeDefinition',
    'NotNullAttributeDefinition', 'DisallowNullAttributeDefinition', 'NotNullIfNotNullAttributeDefinition',
    'MaybeNullWhenAttributeDefinition', 'NotNullWhenAttributeDefinition', 'MemberNotNullAttributeDefinition',
    'MemberNotNullWhenAttributeDefinition', 'DoesNotReturnAttributeDefinition', 'DoesNotReturnIfAttributeDefinition',
    'OverloadResolutionPriorityAttributeDefinition', 'TestSources.Index', 'TestSources.Range',
    'TestSources.GetSubArray', 'IAsyncDisposableDefinition', 'AsyncStreamsTypes',
    'CollectionBuilderAttributeDefinition', 'EnumeratorCancellationAttributeType',
    'RequiresLocationAttributeDefinition', 'RequiredMemberAttribute', 'SetsRequiredMembersAttribute',
    'LockTypeDefinition', 'UnmanagedCallersOnlyAttributeDefinition',
}


def split_plus(text):
    """Splits on the `+` outside any brackets and literals."""
    parts, depth, start, i = [], 0, 0, 0
    while i < len(text):
        end = skip_literal(text, i)
        if end is not None:
            i = end; continue
        ch = text[i]
        if ch in '([{': depth += 1
        elif ch in ')]}': depth -= 1
        elif ch == '+' and depth == 0:
            parts.append(text[start:i]); start = i + 1
        i += 1
    parts.append(text[start:])
    return [p.strip() for p in parts if p.strip()]


def source_of(expr, body, before, depth=0):
    """The C# source text an expression names: a literal or a variable holding one."""
    expr = expr.strip()
    p = parse_string_literal(expr, 0)
    if p and p[1] == len(expr): return p[0]
    # `new[] { source }` and `[source]` with one element are one file, and
    # so are they with the framework's own types beside it.
    m = re.fullmatch(r'(?:new\s*(?:string)?\s*\[\s*\]\s*\{(.*)\}|\[(.*)\])', expr, re.S)
    if m:
        elements = split_top(m.group(1) if m.group(1) is not None else m.group(2))
        elements = [e for e in elements if e not in FRAMEWORK_SOURCES]
        if len(elements) != 1: raise Unsupported('several files')
        return source_of(elements[0], body, before, depth)
    if re.fullmatch(r'\w+', expr) and depth < 4:
        rhs = assignment(body, expr, before)
        if rhs: return source_of(rhs[0], body, rhs[1], depth + 1)
    # `source + IsExternalInitTypeDefinition` appends what .NET 10 has.
    parts = split_plus(expr)
    if len(parts) > 1:
        kept = [part for part in parts if part not in FRAMEWORK_SOURCES]
        if len(kept) == 1 and parts[0] == kept[0]:
            return source_of(kept[0], body, before, depth)
        raise Unsupported('source built from parts')
    raise Unsupported('source not found')


# The compilations taken, with the options each implies. The helpers that add
# a piece of framework (Span, Index, required members) need nothing more
# against .NET 10, which has all of it.
COMPILATION_CALL = re.compile(
    r'\b(CreateCompilation(?:WithMscorlib46|WithMscorlib461|WithSpan|WithMscorlibAndSpan|WithSpanAndMemoryExtensions'
    r'|WithTasksExtensions|WithIndex|WithIndexAndRange|WithIndexAndRangeAndSpan|WithRequiredMembers'
    r'|WithFunctionPointers|WithAsyncIterator|WithCovariantReturns)?'
    r'|CreateCompilation\w+|CreateEmptyCompilation|CreateStandardCompilation|CompileAndVerify\w*)\s*\(')
ACCEPTED_CALL = re.compile(
    r'^(?:CreateCompilation(?:WithMscorlib46|WithMscorlib461|WithSpan|WithMscorlibAndSpan|WithSpanAndMemoryExtensions'
    r'|WithTasksExtensions|WithIndex|WithIndexAndRange|WithIndexAndRangeAndSpan|WithRequiredMembers'
    r'|WithFunctionPointers|WithAsyncIterator|WithCovariantReturns)?|CompileAndVerify)$')

# Parse options at the latest language version (the parser needs nothing else).
PARSE_OPTIONS = re.compile(
    r'^(?:TestOptions\.(?:Regular|RegularDefault|RegularPreview|RegularNext|Regular1[2-5]|RegularWithFileScopedNamespaces'
    r'|RegularWithExtendedPartialMethods)|TestOptions\.RegularPreview\.WithNoRefSafetyRulesAttribute\(\)'
    r'|TestOptions\.Regular\.WithNoRefSafetyRulesAttribute\(\))$')

# Compilation options: which of exe, unsafe and nullable they say.
OPTIONS = re.compile(
    r'^(?:TestOptions\.(?P<unsafe>Unsafe)?(?:Release|Debug)(?P<kind>Dll|Exe)(?:WithNullableEnable)?|WithNullableEnable\(\)'
    r'|WithNullableDisable\(\))'
    r'(?P<rest>(?:\.WithNullableContextOptions\(NullableContextOptions\.\w+\)|\.WithAllowUnsafe\(true\))*)$')

TARGET_FRAMEWORK = re.compile(r'^TargetFramework\.(?:Net\w*|Standard\w*|NetCoreApp\w*|NetLatest|Mscorlib46\w*|Mscorlib461\w*)$')


def compilation(expr, body, before, depth=0):
    """(source, flags) of the compilation an expression names."""
    expr = expr.strip()
    if depth > 6: raise Unsupported('compilation not found')
    if re.fullmatch(r'\w+', expr):
        rhs = assignment(body, expr, before)
        if not rhs: raise Unsupported('compilation not found')
        return compilation(rhs[0], body, rhs[1], depth + 1)
    m = COMPILATION_CALL.match(expr)
    if not m: raise Unsupported('compilation not found')
    close = matching(expr, m.end() - 1)
    if close is None: raise Unsupported('unparsed call')
    # `CreateCompilation(...).VerifyDiagnostics(...)` is the compilation it verified.
    rest = expr[close + 1:].strip()
    if rest and not re.match(r'^\.Verify(?:Emit)?Diagnostics\s*\(', rest):
        raise Unsupported('compilation changed after it was made')
    return call_compilation(m.group(1), expr[m.end():close], body, before)


def call_compilation(helper, args_text, body, before):
    if not ACCEPTED_CALL.match(helper): raise Unsupported(f'helper {helper}')
    args = split_top(args_text)
    if not args: raise Unsupported('no source')
    first = args[0]
    if re.match(r'\w+\s*:', first):
        first = named(args, 'source') or named(args, 'sources') or ''
    flags = {}
    made = assignment(body, first, before) if re.fullmatch(r'\w+', first) else None
    if helper == 'CompileAndVerify' and made and COMPILATION_CALL.match(made[0]):
        # `CompileAndVerify(comp, ...)` verifies a compilation made before.
        source, flags = compilation(made[0], body, made[1])
    else:
        source = source_of(first, body, before)
    positional = [a for a in args[1:] if not re.match(r'\w+\s*:', a)]
    if positional: raise Unsupported('positional arguments')
    for a in args[1:]:
        key, value = re.match(r'(\w+)\s*:\s*(.*)', a, re.S).groups()
        value = value.strip()
        if key == 'parseOptions':
            if not PARSE_OPTIONS.match(value): raise Unsupported('parse options')
            # Roslyn's tests parse at the preview version unless told
            # otherwise; `Regular` is the latest release, C# 15.
            version = re.match(r'TestOptions\.Regular(\d*)', value).group(1)
            if 'Preview' in value or 'Next' in value or 'ExtendedPartial' in value:
                version = 'preview'
            flags['langversion'] = version or ('10' if 'FileScoped' in value else '15')
        elif key == 'options':
            o = OPTIONS.match(value)
            if not o: raise Unsupported('options')
            if o.group('kind') == 'Exe': flags['kind'] = 'exe'
            if o.group('unsafe') or 'WithAllowUnsafe' in (o.group('rest') or ''): flags['unsafe'] = 'true'
            if 'NullableEnable' in value or 'NullableContextOptions.Enable' in value: flags['nullable'] = 'enable'
        elif key == 'targetFramework':
            if not TARGET_FRAMEWORK.match(value): raise Unsupported('target framework')
        elif key == 'references':
            if not re.fullmatch(r'(?:new\s*\[\s*\]\s*\{\s*(?:\w+\.)*(?:SystemCoreRef|CSharpRef|SystemRef|ValueTupleRef|LinqAssemblyRef)\w*\s*\}|\[\s*\])', value):
                raise Unsupported('references')
        elif key in ('expectedOutput', 'verify', 'assemblyName', 'sourceFileName', 'skipUsesIsNullable', 'symbolValidator', 'sourceSymbolValidator', 'emitOptions', 'expectedSignatures'):
            pass
        else:
            raise Unsupported(f'argument {key}')
    return source, flags


DIAGNOSTIC = re.compile(r'^Diagnostic\s*\(\s*ErrorCode\.(\w+)\s*(?:,\s*)?')


def expected_diagnostics(args, body, before, codes, depth=0):
    """The expected (severity, number, line, column, text) of a Verify call's arguments."""
    out = []
    for a in args:
        a = a.strip()
        if re.fullmatch(r'\w+', a) and depth < 3:
            # `comp.VerifyDiagnostics(expected)` with `var expected = new[] { ... }`.
            rhs = assignment(body, a, before)
            if not rhs: raise Unsupported('diagnostics not found')
            m = re.fullmatch(r'(?:new\s*(?:DiagnosticDescription)?\s*\[\s*\]\s*\{(.*)\}|\[(.*)\])', rhs[0], re.S)
            if not m: raise Unsupported('diagnostics not found')
            inner = m.group(1) if m.group(1) is not None else m.group(2)
            out += expected_diagnostics(split_top(inner), body, rhs[1], codes, depth + 1)
            continue
        m = DIAGNOSTIC.match(a)
        if not m: raise Unsupported('unparsed diagnostic')
        name = m.group(1)
        if name not in codes: raise Unsupported('unknown error code')
        open_at = a.index('(')
        close = matching(a, open_at)
        if close is None: raise Unsupported('unparsed diagnostic')
        inner = split_top(a[open_at + 1:close])
        text = None
        if len(inner) > 1:
            if inner[1] == 'null': text = None
            else:
                p = parse_string_literal(inner[1], 0)
                if not p or p[1] != len(inner[1]): raise Unsupported('unparsed diagnostic')
                text = p[0]
        if len(inner) > 2: raise Unsupported('unparsed diagnostic')
        severity = {'ERR': 'error', 'WRN': 'warning', 'HDN': 'hidden', 'INF': 'info', 'FTL': 'error'}.get(name.split('_')[0])
        if severity is None: raise Unsupported('unknown error code')
        line = column = 0
        rest = a[close + 1:]
        i = 0
        while i < len(rest):
            call = re.match(r'\s*\.(\w+)\s*\(', rest[i:])
            if not call:
                if rest[i:].strip(): raise Unsupported('unparsed diagnostic')
                break
            open_at = i + call.end() - 1
            end = matching(rest, open_at)
            if end is None: raise Unsupported('unparsed diagnostic')
            method, arguments = call.group(1), rest[open_at + 1:end]
            if method == 'WithLocation':
                loc = re.fullmatch(r'\s*(\d+)\s*,\s*(\d+)\s*', arguments)
                if not loc: raise Unsupported('location in another file')
                line, column = int(loc.group(1)), int(loc.group(2))
            elif method == 'WithWarningAsError':
                if arguments.strip() == 'true': severity = 'error'
            elif method not in ('WithArguments', 'WithArgumentsAnyOrder'):
                raise Unsupported(f'diagnostic {method}')
            i = end + 1
        out.append((severity, codes[name], line, column, text))
    return out


def test_methods(text):
    """(name, start, end) of each test method: a `public void Name(` after an attribute line."""
    heads = []
    for m in re.finditer(r'^[ \t]*(?:public|internal|private)\s+(?:async\s+)?(?:void|Task)\s+(\w+)\s*\(', text, re.M):
        before = text[:m.start()].rstrip()
        last = before[before.rfind('\n') + 1:].strip()
        if last.startswith('[') and last.endswith(']'):
            heads.append(m)
    for k, m in enumerate(heads):
        yield m.group(1), m.start(), heads[k + 1].start() if k + 1 < len(heads) else len(text)


VERIFY = re.compile(r'\.(?:Verify(?:Emit)?Diagnostics|GetDiagnostics\(\)\s*\.Verify|GetEmitDiagnostics\(\)\s*\.Verify)\s*\(')


def main():
    codes = error_codes()
    os.makedirs(OUT, exist_ok=True)
    for old in os.listdir(OUT):
        os.remove(os.path.join(OUT, old))
    total = written = index = 0
    skipped = {}
    seen = set()
    for dirpath, _, files in sorted(os.walk(ROOT)):
        for f in sorted(files):
            if not f.endswith('.cs'): continue
            path = os.path.join(dirpath, f)
            text = open(path, encoding='utf-8-sig').read().replace('\r\n', '\n')
            for method, start, end in test_methods(text):
                body = text[start:end]
                for v in VERIFY.finditer(body):
                    total += 1
                    index += 1
                    base = f'{os.path.splitext(f)[0]}_{method}_{index}'
                    try:
                        close = matching(body, v.end() - 1)
                        if close is None: raise Unsupported('unparsed call')
                        expected = expected_diagnostics(split_top(body[v.end():close]), body, v.start(), codes)
                        # The receiver: a variable, or the call right before the dot.
                        head = body[:v.start()].rstrip()
                        var = re.search(r'(?<![\w.])(\w+)$', head)
                        if var:
                            if var.group(1) in ('this', 'base'): raise Unsupported('compilation not found')
                            # `comp.MakeMemberMissing(...)` takes a member out
                            # of the framework, which no reference set here can.
                            if re.search(r'\b' + var.group(1) + r'\.Make(?:Member|Type)Missing\s*\(', body[:v.start()]):
                                raise Unsupported('compilation changed after it was made')
                            source, flags = compilation(var.group(1), body, v.start())
                        elif head.endswith(')'):
                            candidates = [m for m in COMPILATION_CALL.finditer(head)
                                          if matching(head, m.end() - 1) == len(head) - 1]
                            if not candidates: raise Unsupported('compilation not found')
                            m = candidates[-1]
                            if head[m.start() - 1:m.start()] == '.': raise Unsupported('compilation not found')
                            source, flags = call_compilation(m.group(1), head[m.end():-1], body, m.start())
                        else:
                            raise Unsupported('compilation not found')
                    except Unsupported as reason:
                        skipped[reason.args[0]] = skipped.get(reason.args[0], 0) + 1
                        if os.environ.get('DIAG_VERBOSE') == reason.args[0]:
                            print(f'{base}: {os.path.relpath(path, ROOT)}:{text.count(chr(10), 0, start + v.start()) + 1}')
                        continue
                    except (IndexError, ValueError):
                        skipped['unparsed'] = skipped.get('unparsed', 0) + 1
                        continue
                    # The same program expecting the same diagnostics at another language
                    # version is the same test.
                    same = sorted((k, v) for k, v in flags.items() if k != 'langversion')
                    key = hashlib.sha1(json.dumps([source, same, expected]).encode()).hexdigest()
                    if key in seen:
                        skipped['duplicate'] = skipped.get('duplicate', 0) + 1
                        continue
                    seen.add(key)
                    written += 1
                    open(os.path.join(OUT, base + '.cs'), 'w').write(source)
                    with open(os.path.join(OUT, base + '.diag'), 'w') as out:
                        out.write(f'# from: {os.path.relpath(path, ROOT)}:{text.count(chr(10), 0, start + v.start()) + 1}\n')
                        for k, value in sorted(flags.items()):
                            out.write(f'# {k}: {value}\n')
                        for severity, number, line, column, squiggle in expected:
                            out.write(f'{severity}\tCS{number:04}\t{line}\t{column}\t{json.dumps(squiggle)}\n')
    print(f'verify calls: {total}, extracted: {written}')
    for k, v in sorted(skipped.items(), key=lambda kv: -kv[1]):
        print(f'  skipped {k}: {v}')


if __name__ == '__main__':
    main()
