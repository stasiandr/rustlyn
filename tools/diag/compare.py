#!/usr/bin/env python3
"""Compares what rustlyn reported for each diagnostics test with what Roslyn is expected to report.

usage: compare.py <tests> <out> <results> [glob]

Errors come first and warnings second, each measured two ways: exactly (the same codes at the same
places, as a multiset) and loosely (the same set of codes). A diagnostic the test gives no location
for is matched by its code and the text it points at. Writes to <results>:

  errors.txt, warnings.txt   one line per test: name, status (pass, spurious, missing, wrong,
                             crash), and for a loose pass `codes`
  summary.txt                the counts, and which codes are most often missing or spurious"""
import collections, fnmatch, json, os, sys

tests, out, results = sys.argv[1:4]
pattern = sys.argv[4] if len(sys.argv) > 4 else '*'


def parse(path):
    found = []
    if not os.path.exists(path): return found
    for line in open(path, encoding='utf-8', errors='replace'):
        if line.startswith('#') or not line.strip(): continue
        parts = line.rstrip('\n').split('\t')
        if len(parts) < 5: continue
        severity, code, row, column, text = parts[:5]
        try:
            text = json.loads(text)
        except ValueError:
            text = None
        found.append((severity, code, int(row), int(column), text))
    return found


def match(expected, actual):
    """(missing, spurious): what is expected and not reported, and reported and not expected."""
    left = list(actual)
    missing = []
    # Located expectations first, so that one without a location cannot take
    # the diagnostic a located one needs.
    for e in sorted(expected, key=lambda e: e[2] == 0):
        if e[2]:
            hit = next((a for a in left if a[1] == e[1] and a[2] == e[2] and a[3] == e[3]), None)
        else:
            hit = next((a for a in left if a[1] == e[1] and (e[4] is None or a[4] == e[4])), None)
        if hit is None: missing.append(e)
        else: left.remove(hit)
    return missing, left


def status(expected, actual, crashed):
    missing, spurious = match(expected, actual)
    if crashed: return 'crash', missing, spurious
    if not missing and not spurious: return 'pass', missing, spurious
    loose = {e[1] for e in expected} == {a[1] for a in actual}
    if not expected: kind = 'spurious'
    elif not actual: kind = 'missing'
    else: kind = 'wrong'
    return (kind + ' codes' if loose else kind), missing, spurious


os.makedirs(results, exist_ok=True)
names = sorted(f[:-5] for f in os.listdir(tests) if f.endswith('.diag') and fnmatch.fnmatch(f[:-5], pattern))
counts = {'errors': collections.Counter(), 'warnings': collections.Counter()}
missing_codes = {'errors': collections.Counter(), 'warnings': collections.Counter()}
spurious_codes = {'errors': collections.Counter(), 'warnings': collections.Counter()}
lines = {'errors': [], 'warnings': []}
for name in names:
    expected = parse(os.path.join(tests, name + '.diag'))
    actual = parse(os.path.join(out, name + '.actual'))
    crashed = os.path.exists(os.path.join(out, name + '.crash'))
    for kind, severity in (('errors', 'error'), ('warnings', 'warning')):
        e = [d for d in expected if d[0] == severity]
        a = [d for d in actual if d[0] == severity]
        s, missing, spurious = status(e, a, crashed)
        counts[kind][s] += 1
        # Each test counts a code once: the question is how many tests a
        # code breaks, not how often it repeats in one of them.
        for code in {d[1] for d in missing}: missing_codes[kind][code] += 1
        for code in {d[1] for d in spurious}: spurious_codes[kind][code] += 1
        lines[kind].append(f'{name} {s}')

with open(os.path.join(results, 'summary.txt'), 'w') as summary:
    def say(text=''):
        print(text)
        summary.write(text + '\n')
    total = len(names)
    for kind in ('errors', 'warnings'):
        c = counts[kind]
        exact = c['pass']
        loose = exact + sum(v for k, v in c.items() if k.endswith(' codes'))
        say(f'{kind}: {exact}/{total} exact ({100 * exact / max(total, 1):.1f}%), '
            f'{loose}/{total} same codes ({100 * loose / max(total, 1):.1f}%)')
        say('  ' + ', '.join(f'{k}: {v}' for k, v in sorted(c.items(), key=lambda kv: -kv[1])))
    for kind in ('errors', 'warnings'):
        say(f'\n{kind} most often missing (tests):')
        say('  ' + ', '.join(f'{k} {v}' for k, v in missing_codes[kind].most_common(30)))
        say(f'{kind} most often spurious (tests):')
        say('  ' + ', '.join(f'{k} {v}' for k, v in spurious_codes[kind].most_common(30)))
for kind in ('errors', 'warnings'):
    with open(os.path.join(results, kind + '.txt'), 'w') as f:
        f.write('\n'.join(lines[kind]) + '\n')
