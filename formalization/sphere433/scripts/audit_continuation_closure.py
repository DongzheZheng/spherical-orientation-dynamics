#!/usr/bin/env python3
"""Lexical audit of this package and its pinned native geometry dependency.
Comments and strings are stripped before token checks. Kernel axiom prints
provide the separate, decisive audit of actual theorem dependencies.
"""
import argparse, hashlib, json, pathlib, re

parser = argparse.ArgumentParser()
parser.add_argument('--upstream', required=True)
parser.add_argument('--output', default='verification/continuation/source-closure.json')
a = parser.parse_args()
package = pathlib.Path(__file__).resolve().parent.parent
upstream = pathlib.Path(a.upstream).resolve()


def code_only(s):
    out = []; i = 0; depth = 0; string = False
    while i < len(s):
        pair = s[i:i+2]
        if depth:
            if pair == '/-': depth += 1; i += 2
            elif pair == '-/': depth -= 1; i += 2
            else: out.append('\n' if s[i] == '\n' else ' '); i += 1
        elif string:
            if s[i] == '\\': out.extend('  '); i += 2
            elif s[i] == '"': string = False; out.append(' '); i += 1
            else: out.append('\n' if s[i] == '\n' else ' '); i += 1
        elif pair == '/-': depth = 1; out.extend('  '); i += 2
        elif pair == '--':
            j = s.find('\n', i)
            if j == -1: break
            out.append('\n'); i = j + 1
        elif s[i] == '"': string = True; out.append(' '); i += 1
        else: out.append(s[i]); i += 1
    return ''.join(out)


def module_path(m):
    if m == 'DFLSphere433' or m.startswith('DFLSphere433.'):
        return package / (m.replace('.', '/') + '.lean')
    if m == 'continuation' or m.startswith('continuation.'):
        return package / (m.replace('.', '/') + '.lean')
    if m.startswith('DifferentialGeometry.'):
        return upstream / (m.replace('.', '/') + '.lean')
    return None

seen = {}; missing = []; ignored = set(); forbidden = []
stack = ['DFLSphere433']
while stack:
    m = stack.pop()
    if m in seen: continue
    p = module_path(m)
    if p is None: ignored.add(m); continue
    if not p.exists(): missing.append(m); continue
    raw = p.read_text(); code = code_only(raw)
    seen[m] = {'sha256': hashlib.sha256(raw.encode()).hexdigest()}
    for token in re.finditer(r'\b(?:sorry|admit|axiom|sorryAx|native_decide)\b', code):
        forbidden.append({'module': m, 'line': code[:token.start()].count('\n')+1, 'token': token.group()})
    for line in code.splitlines():
        match = re.match(r'^\s*(?:public\s+)?import\s+(.+)$', line)
        if match: stack.extend(match.group(1).split())
report = {
    'scope': 'Own source plus transitive DifferentialGeometry native source; Mathlib and Lean imports separately pinned by lake-manifest.json',
    'native_module_count': sum(m.startswith('DifferentialGeometry.') for m in seen),
    'own_module_count': sum(m == 'DFLSphere433' or m.startswith('DFLSphere433.') or m == 'continuation' or m.startswith('continuation.') for m in seen),
    'continuation_module_count': sum(m == 'continuation' or m.startswith('continuation.') for m in seen),
    'own_sources': sorted(str(module_path(m).relative_to(package)) for m in seen if m == 'DFLSphere433' or m.startswith('DFLSphere433.') or m == 'continuation' or m.startswith('continuation.')),
    'missing': sorted(missing), 'forbidden_tokens': forbidden,
    'external_imports': sorted(ignored), 'modules': dict(sorted(seen.items()))}
out = package / a.output; out.parent.mkdir(parents=True, exist_ok=True)
out.write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({k:v for k,v in report.items() if k not in ['modules','external_imports']}, indent=2))
raise SystemExit(bool(missing or forbidden))
