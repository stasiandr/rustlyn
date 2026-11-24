#!/usr/bin/env python3
"""A broader extraction of CompileAndVerify tests from chosen test files, for
looking for failures in one area rather than for the shared benchmark
(extract.py stays what the baseline is measured with).

It understands more of how a test writes its program: sources given as
arrays (`[source, s_collectionExtensions]`, `new[] { a, b }`) or joined with
`+`, sources held in constants of the test class or of CSharpTestBase
(`UnionAttributeSource`), raw and interpolated strings without holes,
`CreateCompilation(...)` assigned to a variable, and expected output wrapped
in `IncludeExpectedOutput(...)`. Several sources become one file, their
`using`s gathered at the top and the one with top-level statements first.
A test compiled against anything but the framework is skipped.

usage: extract_more.py '**/CollectionExpressionTests*.cs' '**/UnionsTests.cs' ...
Roslyn is read from $CAV_ROSLYN (default $CAV_HOME/roslyn, $CAV_HOME being
/home/user unless set). Output: $CAV_TESTS (default $CAV_HOME/cav-more/tests);
run.sh takes the same variable."""
import os, re, sys, glob

HOME = os.environ.get('CAV_HOME', '/home/user')
ROSLYN = os.environ.get('CAV_ROSLYN', HOME + '/roslyn')
ROOT = ROSLYN + '/src/Compilers/CSharp/Test'
OUT = os.environ.get('CAV_TESTS', HOME + '/cav-more/tests')
os.makedirs(OUT, exist_ok=True)
BASE = open(ROSLYN + '/src/Compilers/Test/Utilities/CSharp/CSharpTestBase.cs', encoding='utf-8-sig').read()
PATTERNS = sys.argv[1:] or ['**/CollectionExpressionTests*.cs']


FRAMEWORK_REF = re.compile(
    r'^(?:null|CSharpRef|SystemCoreRef\w*|SystemRef\w*|MscorlibRef\w*|ValueTupleRef|SystemRuntimeFacadeRef|'
    r'LinqAssemblyRef|SystemObjectModelRef|SystemXmlRef|SystemXmlLinqRef|SystemDataRef|'
    r'NetStandard20\.\w+|Net\w*\.References\.\w+|s_valueTupleRefs|TargetFrameworkUtil\.StandardCSharpReference|TestMetadata\.Net\w+\.\w+)$')


class Skip(Exception):
    pass


def parse_string_literal(text, at):
    """(value, end) of the C# string literal at `at`, or None. Interpolated
    strings are accepted only without holes."""
    prefix = re.match(r'(\$*)(@?)(\$*)', text[at:])
    dollars = len(prefix.group(1)) + len(prefix.group(3))
    verbatim = bool(prefix.group(2))
    i = at + prefix.end()
    if not text.startswith('"', i):
        return None
    if text.startswith('"""', i) and not verbatim:
        quotes = re.match(r'"{3,}', text[i:]).group(0)
        j = i + len(quotes)
        end = text.find(quotes, j)
        if end < 0:
            return None
        body = text[j:end]
        if '\n' in body:
            lines = body.split('\n')
            last = lines[-1]
            indent = len(last) - len(last.lstrip(' '))
            lines = lines[1:-1] if lines[0].strip() == '' else lines[:-1]
            body = '\n'.join(l[indent:] if l.startswith(' ' * indent) else l.lstrip(' ') for l in lines)
        if dollars:
            hole = '{' * dollars
            if hole in body:
                return None
        return body, end + len(quotes)
    if verbatim:
        j = i + 1
        out = []
        while j < len(text):
            c = text[j]
            if c == '"':
                if j + 1 < len(text) and text[j + 1] == '"':
                    out.append('"'); j += 2; continue
                break
            out.append(c); j += 1
        else:
            return None
        value = ''.join(out)
        if dollars:
            if re.search(r'(?<!\{)\{(?!\{)', value):
                return None
            value = value.replace('{{', '{').replace('}}', '}')
        return value, j + 1
    j = i + 1
    out = []
    while j < len(text):
        c = text[j]
        if c == '\\':
            n = text[j + 1]
            simple = {'n': '\n', 'r': '\r', 't': '\t', '"': '"', '\\': '\\', '0': '\0', "'": "'", 'a': '\a', 'b': '\b', 'f': '\f', 'v': '\v', 'e': '\x1b'}
            if n in simple:
                out.append(simple[n]); j += 2; continue
            if n == 'u':
                out.append(chr(int(text[j + 2:j + 6], 16))); j += 6; continue
            if n == 'U':
                out.append(chr(int(text[j + 2:j + 10], 16))); j += 10; continue
            if n == 'x':
                m = re.match(r'[0-9a-fA-F]{1,4}', text[j + 2:])
                out.append(chr(int(m.group(0), 16))); j += 2 + len(m.group(0)); continue
            return None
        if c == '"':
            value = ''.join(out)
            if dollars:
                if re.search(r'(?<!\{)\{(?!\{)', value):
                    return None
                value = value.replace('{{', '{').replace('}}', '}')
            return value, j + 1
        if c == '\n':
            return None
        out.append(c); j += 1
    return None


def skip_literal(text, i):
    """If a string or char literal starts at i, its end; else None."""
    m = re.match(r'\$*@?\$*"', text[i:])
    if m and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] == '_')):
        # find end regardless of holes
        j = i + m.end() - 1
        dollars = m.group(0).count('$')
        verbatim = '@' in m.group(0)
        if text.startswith('"""', j) and not verbatim:
            quotes = re.match(r'"{3,}', text[j:]).group(0)
            end = text.find(quotes, j + len(quotes))
            return None if end < 0 else end + len(quotes)
        k = j + 1
        depth = 0
        while k < len(text):
            c = text[k]
            if not verbatim and c == '\\':
                k += 2; continue
            if c == '"':
                if verbatim and k + 1 < len(text) and text[k + 1] == '"':
                    k += 2; continue
                if depth == 0:
                    return k + 1
            if dollars and c == '{':
                if text.startswith('{{', k) and dollars == 1:
                    k += 2; continue
                depth += 1
            elif dollars and c == '}' and depth > 0:
                depth -= 1
            k += 1
        return None
    if text[i] == "'":
        m = re.match(r"'(?:\\.|[^'\\])+'", text[i:])
        if m:
            return i + m.end()
    return None


def matching(text, at):
    pairs = {'(': ')', '[': ']', '{': '}'}
    stack = []
    i = at
    while i < len(text):
        end = skip_literal(text, i)
        if end is not None:
            i = end; continue
        ch = text[i]
        if text.startswith('//', i):
            nl = text.find('\n', i)
            i = len(text) if nl < 0 else nl
            continue
        if ch in pairs:
            stack.append(pairs[ch])
        elif ch in ')]}':
            if not stack or stack.pop() != ch:
                return None
            if not stack:
                return i
        i += 1
    return None


def split_top(text, sep=','):
    parts, depth, start, i = [], 0, 0, 0
    while i < len(text):
        end = skip_literal(text, i)
        if end is not None:
            i = end; continue
        ch = text[i]
        if ch in '([{':
            depth += 1
        elif ch in ')]}':
            depth -= 1
        elif text.startswith(sep, i) and depth == 0:
            parts.append(text[start:i]); start = i + len(sep); i += len(sep); continue
        i += 1
    parts.append(text[start:])
    return [p.strip() for p in parts if p.strip()]


def named(args, name):
    for a in args:
        m = re.match(name + r'\s*:\s*', a)
        if m:
            return a[m.end():]
    return None


def positional(args):
    return [a for a in args if not re.match(r'\w+\s*:(?!:)', a)]


class Context:
    def __init__(self, text, body, before):
        self.text = text
        self.body = body
        self.before = before

    def assignment(self, name, before):
        """The last `name = <expr>;` in the body before `before`: (expr, at)."""
        found = None
        for m in re.finditer(r'(?<![\w.])' + re.escape(name) + r'\s*=(?![=>])\s*', self.body[:before]):
            found = m
        if not found:
            return None
        i = found.end()
        depth = 0
        while i < len(self.body):
            end = skip_literal(self.body, i)
            if end is not None:
                i = end; continue
            ch = self.body[i]
            if ch in '([{':
                depth += 1
            elif ch in ')]}':
                depth -= 1
            elif ch == ';' and depth == 0:
                return self.body[found.end():i].strip(), found.start()
            i += 1
        return None

    def class_constant(self, name):
        found = self.class_constant_in(self.text, name)
        if found is None:
            found = self.class_constant_in(BASE, name)
        return found

    def class_constant_in(self, text, name):
        self_text = self.text
        self.text = text
        try:
            return self.class_constant_here(name)
        finally:
            self.text = self_text

    def class_constant_here(self, name):
        for pattern in (r'(?:const|static\s+readonly|static)\s+string\s+' + re.escape(name) + r'\s*=\s*',
                        r'string\s+' + re.escape(name) + r'\s*=>\s*'):
            m = re.search(pattern, self.text)
            if m:
                i = m.end()
                depth = 0
                while i < len(self.text):
                    end = skip_literal(self.text, i)
                    if end is not None:
                        i = end; continue
                    ch = self.text[i]
                    if ch in '([{':
                        depth += 1
                    elif ch in ')]}':
                        depth -= 1
                    elif ch == ';' and depth == 0:
                        return self.text[m.end():i].strip()
                    i += 1
        return None

    def string(self, expr, before, depth=0):
        """The string an expression evaluates to."""
        expr = expr.strip()
        if depth > 8:
            raise Skip('deep')
        while expr.startswith('(') and matching(expr, 0) == len(expr) - 1:
            expr = expr[1:-1].strip()
        p = parse_string_literal(expr, 0) if re.match(r'\$*@?\$*"', expr) else None
        if p and p[1] == len(expr):
            return p[0]
        parts = split_top(expr, '+')
        if len(parts) > 1:
            return ''.join(self.string(part, before, depth + 1) for part in parts)
        if re.fullmatch(r'\w+', expr):
            found = self.assignment(expr, before)
            if found:
                return self.string(found[0], found[1], depth + 1)
            constant = self.class_constant(expr)
            if constant is not None:
                return self.string(constant, 0, depth + 1)
        raise Skip('string ' + expr[:40])

    def sources(self, expr, before, depth=0):
        """The sources a compilation argument names."""
        expr = expr.strip()
        if depth > 8:
            raise Skip('deep')
        m = re.match(r'^(?:new\s*(?:string)?\s*\[\s*\]\s*\{|\[)', expr)
        if m:
            close = matching(expr, m.end() - 1)
            if close != len(expr) - 1:
                raise Skip('array')
            items = split_top(expr[m.end():close])
            out = []
            for item in items:
                out.extend(self.sources(item, before, depth + 1))
            return out
        if re.fullmatch(r'\w+', expr):
            found = self.assignment(expr, before)
            if found and re.match(r'(?:Create\w*Compilation\w*|CSharpCompilation\.Create)\s*\(', found[0]):
                return self.compilation(found[0], found[1], depth + 1)
            if found and re.match(r'(?:new\s*(?:string)?\s*\[\s*\]\s*\{|\[)', found[0]):
                return self.sources(found[0], found[1], depth + 1)
        if re.match(r'Create\w*Compilation\w*\s*\(', expr):
            return self.compilation(expr, before, depth + 1)
        return [self.string(expr, before, depth + 1)]

    def compilation(self, expr, before, depth):
        m = re.match(r'(Create\w*Compilation\w*)\s*\(', expr)
        if not m or 'WithIL' in m.group(1) or 'Metadata' in m.group(1):
            raise Skip('compilation kind')
        close = matching(expr, m.end() - 1)
        if close is None:
            raise Skip('unbalanced')
        args = split_top(expr[m.end():close])
        check_args(args)
        first = named(args, 'source') or (positional(args) or [None])[0]
        if first is None:
            raise Skip('no source')
        return self.sources(first, before, depth + 1)


def check_args(args):
    references = named(args, 'references')
    if references:
        m = re.fullmatch(r'(?:new\s*(?:\w+\s*)?\[\s*\]\s*\{|\[)(.*?)(?:\}|\])', references.strip(), re.S)
        items = split_top(m.group(1)) if m else [references.strip()]
        if not all(FRAMEWORK_REF.match(item) for item in items):
            raise Skip('references')
    pos = positional(args)
    if len(pos) > 1:
        raise Skip('positional references')
    framework = named(args, 'targetFramework')
    if framework and not re.search(r'Net(?:Core|Latest|80|90|100)\b|NetCoreApp|Net70', framework):
        raise Skip('framework')


def expected_of(ctx, expr, before):
    expr = expr.strip()
    m = re.match(r'(?:IncludeExpectedOutput|ExpectedOutput)\s*\(', expr)
    if m:
        close = matching(expr, m.end() - 1)
        inner = split_top(expr[m.end():close])
        return ctx.string(inner[0], before)
    if re.search(r'\?.*:', expr) and not re.match(r'\$*@?\$*"', expr):
        raise Skip('conditional expected')
    return ctx.string(expr, before)


USING = re.compile(r'^\s*(?:global\s+)?using\s+(?!\()(?:static\s+)?[\w.]+(?:\s*=\s*[\w.<>, ]+)?\s*;\s*$')
DECLARATION = re.compile(r'^(?:\s*$|\s*//|\s*/\*|\s*\*|\s*#|\s*\[|\s*[{}]|\s*(?:public|internal|private|protected|static|abstract|sealed|partial|file|readonly|ref|unsafe|namespace|class|struct|record|interface|enum|delegate|extension|union|using|global|extern|new|override|virtual)\b)')


def combine(sources):
    usings, bodies = [], []
    for source in sources:
        if re.search(r'^\s*namespace\s+[\w.]+\s*;', source, re.M):
            if len(sources) > 1:
                raise Skip('file-scoped namespace')
        lines = source.split('\n')
        kept = []
        head = True
        for line in lines:
            if head and USING.match(line):
                if line.strip() not in usings:
                    usings.append(line.strip())
                continue
            if head and (not line.strip() or line.strip().startswith('//') or line.strip().startswith('#nullable')):
                kept.append(line); continue
            head = False
            kept.append(line)
        bodies.append('\n'.join(kept))
    # top-level statements first
    def statements(body):
        for line in body.split('\n'):
            if line and not line[0].isspace() and not DECLARATION.match(line):
                return True
        return False
    ordered = sorted(bodies, key=lambda b: 0 if statements(b) else 1)
    if sum(1 for b in bodies if statements(b)) > 1:
        raise Skip('two files of statements')
    text = '\n'.join(usings) + ('\n' if usings else '') + '\n'.join(ordered)
    has_entry = 'Main(' in text or any(statements(b) for b in bodies)
    if not has_entry:
        raise Skip('no entry')
    return text


call_re = re.compile(r'(?<![\w.])CompileAndVerify(?:Experimental)?\s*\(')
written = 0
skipped = {}
files = []
for pattern in PATTERNS:
    files.extend(sorted(glob.glob(os.path.join(ROOT, pattern), recursive=True)))
for path in files:
    text = open(path, encoding='utf-8-sig').read()
    stem = os.path.splitext(os.path.basename(path))[0]
    methods = list(re.finditer(r'\n\s*public\s+(?:async\s+)?(?:void|Task)\s+(\w+)\s*\(', text))
    index = 0
    for k, m in enumerate(methods):
        start = m.end()
        end = methods[k + 1].start() if k + 1 < len(methods) else len(text)
        body = text[start:end]
        for c in call_re.finditer(body):
            index += 1
            name = f'{stem}_{m.group(1)}_{index}'
            try:
                close = matching(body, c.end() - 1)
                if close is None:
                    raise Skip('unbalanced')
                args = split_top(body[c.end():close])
                if not args:
                    raise Skip('no args')
                check_args(args)
                expected = named(args, 'expectedOutput')
                if expected is None:
                    raise Skip('no expectedOutput')
                if re.search(r'Verification\.Fails|emitOptions', body[c.end():close]):
                    pass
                ctx = Context(text, body, c.start())
                expected = expected_of(ctx, expected, c.start())
                first = named(args, 'source') or named(args, 'compilation') or positional(args)[0]
                sources = ctx.sources(first, c.start())
                source = combine(sources)
            except Skip as reason:
                kind = reason.args[0].split(' ')[0]
                skipped[kind] = skipped.get(kind, 0) + 1
                if os.environ.get('CAV_VERBOSE'):
                    print(name, reason.args[0])
                continue
            except Exception as error:
                skipped['error'] = skipped.get('error', 0) + 1
                continue
            open(os.path.join(OUT, name + '.cs'), 'w').write(source)
            open(os.path.join(OUT, name + '.expected'), 'w').write(expected)
            written += 1
print(f'extracted {written}')
for k, v in sorted(skipped.items(), key=lambda kv: -kv[1]):
    print(f'  skipped {k}: {v}')
