#!/usr/bin/env bash
# Reproduce the pinned Lean build, strict compilation, and dependency audits.
set -euo pipefail

if [[ $# -ne 1 || ( "$1" != "dfl2015" && "$1" != "sphere433" ) ]]; then
  printf 'Usage: bash scripts/verify_formalization.sh dfl2015|sphere433\n' >&2
  exit 2
fi
for task_command in python3 git lean lake; do
  if ! command -v "$task_command" >/dev/null 2>&1; then
    printf 'Missing dependency: %s\n' "$task_command" >&2
    exit 3
  fi
done

task_release_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
python3 - "$task_release_root" "$1" <<'PY'
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import hashlib
import getpass
import json
import os
from pathlib import Path
import platform
import re
import shutil
import socket
import subprocess
import sys

release = Path(sys.argv[1])
project_name = sys.argv[2]
project = release / 'formalization' / project_name
mapping = json.loads((release / 'formalization/source_mapping.json').read_text())
rows = [row for row in mapping['entries']
        if row['project'] == project_name and row['status'] == 'retained_byte_for_byte']
sources = sorted(str(Path(row['release_relative_path']).relative_to(
    Path('formalization') / project_name)) for row in rows
    if row['release_relative_path'].endswith('.lean'))
expected_version = {'dfl2015': '4.29.0', 'sphere433': '4.33.1'}[project_name]
expected_sources = {'dfl2015': 178, 'sphere433': 147}[project_name]
allowed_axioms = {'propext', 'Classical.choice', 'Quot.sound'}
stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')
out = release / 'verification-results' / project_name / stamp
out.mkdir(parents=True, exist_ok=False)
status = {'project': project_name, 'started_utc': stamp, 'status': 'running'}
home_paths = sorted({str(Path.home()), str(Path.home().resolve())}, key=len, reverse=True)
hostname_values = {socket.gethostname(), platform.node()}
hostname_values |= {name.split('.', 1)[0] for name in hostname_values if name}
hostname_values = sorted((name for name in hostname_values if name), key=len, reverse=True)
try:
    username = getpass.getuser()
except (KeyError, OSError):
    username = ''


def write_status():
    (out / 'verification.json').write_text(json.dumps(status, indent=2) + '\n')


def normalize_log(text):
    text = text.replace(str(project), '<PROJECT_ROOT>').replace(str(release), '<RELEASE_ROOT>')
    for home_path in home_paths:
        if home_path != '/':
            text = text.replace(home_path, '<USER_HOME>')
    for hostname in hostname_values:
        text = re.sub(r'(?<![A-Za-z0-9_.-])' + re.escape(hostname) + r'(?![A-Za-z0-9_.-])',
                      '<HOSTNAME>', text, flags=re.IGNORECASE)
    if username:
        # Limit replacements to account/path contexts rather than mathematical words.
        account = re.escape(username)
        text = re.sub(r'(?<=/)' + account + r'(?=/)', '<USERNAME>', text)
        text = re.sub(r'(?<![A-Za-z0-9_.-])' + account + r'(?=@)', '<USERNAME>', text)
        text = re.sub(r'(\b(?:user|username|login|account)\s*[:=]\s*)' + account + r'\b',
                      r'\1<USERNAME>', text, flags=re.IGNORECASE)
    return text


def run(command, log):
    result = subprocess.run(command, cwd=project, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (out / log).parent.mkdir(parents=True, exist_ok=True)
    (out / log).write_text(normalize_log(result.stdout))
    if result.returncode:
        raise RuntimeError(f'Command failed ({result.returncode}); see '
                           f'{(out / log).relative_to(release)}')
    return result.stdout


def check_sources():
    for row in rows:
        path = release / row['release_relative_path']
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != row['original_sha256']:
            raise RuntimeError('Source digest mismatch: ' + row['release_relative_path'])
    if len(sources) != expected_sources:
        raise RuntimeError('Unexpected own source count in source_mapping.json')


def code_only(text):
    result = []
    i = 0
    comment_depth = 0
    in_string = False
    while i < len(text):
        pair = text[i:i + 2]
        if comment_depth:
            if pair == '/-':
                comment_depth += 1
                i += 2
            elif pair == '-/':
                comment_depth -= 1
                i += 2
            else:
                result.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif in_string:
            if text[i] == '\\':
                result.extend('  ')
                i += 2
            elif text[i] == '"':
                in_string = False
                result.append(' ')
                i += 1
            else:
                result.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif pair == '/-':
            comment_depth = 1
            result.extend('  ')
            i += 2
        elif pair == '--':
            end = text.find('\n', i)
            if end == -1:
                break
            result.append('\n')
            i = end + 1
        elif text[i] == '"':
            in_string = True
            result.append(' ')
            i += 1
        else:
            result.append(text[i])
            i += 1
    return ''.join(result)


def check_kernel_audits(logs):
    reports = []
    for log in logs:
        content = (out / log).read_text()
        if project_name == 'dfl2015':
            parsed = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", content, re.S)
        else:
            parsed = re.findall(r'OWNDECL (.+?) KERNEL \[([^\]]*)\]', content, re.S)
        for declaration, dependencies in parsed:
            axioms = {item.strip() for item in dependencies.split(',') if item.strip()}
            if not axioms <= allowed_axioms:
                raise RuntimeError('Unexpected kernel dependency for ' + declaration)
            reports.append({'declaration': declaration, 'axioms': sorted(axioms)})
    expected = 140 if project_name == 'dfl2015' else 2108
    if len(reports) != expected:
        raise RuntimeError(f'Unexpected kernel report count: {len(reports)}; expected {expected}')
    if project_name == 'sphere433':
        content = (out / logs[0]).read_text()
        count = re.search(r'OWNDECL_COUNT (\d+)', content)
        if not count or int(count.group(1)) != expected:
            raise RuntimeError('Missing or inconsistent full declaration audit count')
    (out / 'kernel_audit_summary.json').write_text(json.dumps({
        'allowed_standard_axioms': sorted(allowed_axioms),
        'report_count': len(reports), 'all_dependencies_standard': True,
        'reports': reports}, indent=2) + '\n')
    return len(reports)


write_status()
try:
    print(f'[{project_name}] Checking source hashes.', flush=True)
    check_sources()
    expected_toolchain = 'leanprover/lean4:v' + expected_version
    if (project / 'lean-toolchain').read_text().strip() != expected_toolchain:
        raise RuntimeError('Unexpected lean-toolchain declaration')
    lean_version = run(['lean', '--version'], 'lean-version.log')
    if not re.search(r'\bversion ' + re.escape(expected_version) + r'\b', lean_version):
        raise RuntimeError('Active Lean does not match the pinned project toolchain')
    lake_version = run(['lake', '--version'], 'lake-version.log')
    if not re.search(r'\bLean version ' + re.escape(expected_version) + r'\b', lake_version):
        raise RuntimeError('Active Lake does not match the pinned Lean toolchain')

    # Lake resolves the existing pinned manifest; no dependency update is requested.
    print(f'[{project_name}] Resolving locked dependencies.', flush=True)
    run(['lake', 'env', 'lean', '--version'], 'dependency-resolution.log')
    check_sources()
    manifest = json.loads((project / 'lake-manifest.json').read_text())
    revisions = []
    for package in manifest['packages']:
        if package['type'] != 'git':
            raise RuntimeError('Unsupported unlocked dependency type')
        package_dir = project / manifest['packagesDir'] / package['name']
        actual = subprocess.check_output(['git', '-C', str(package_dir), 'rev-parse', 'HEAD'],
                                         text=True, stderr=subprocess.STDOUT).strip()
        if actual != package['rev']:
            raise RuntimeError('Dependency revision mismatch: ' + package['name'])
        diff = subprocess.run(['git', '-C', str(package_dir), 'diff', '--exit-code'],
                              text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        if diff.returncode:
            raise RuntimeError('Tracked dependency files changed: ' + package['name'])
        revisions.append({'name': package['name'], 'revision': actual, 'tracked_diff': 'empty'})
    (out / 'dependency_revisions.json').write_text(json.dumps(revisions, indent=2) + '\n')
    if os.environ.get('DFL_FETCH_CACHE', '0') == '1':
        print(f'[{project_name}] Fetching the pinned mathlib build cache.', flush=True)
        run(['lake', 'exe', 'cache', 'get'], 'cache-download.log')

    print(f'[{project_name}] Building the complete source set.', flush=True)
    if project_name == 'dfl2015':
        modules = [source[:-5].replace('/', '.') for source in sources if source.startswith('DFL/')]
        run(['lake', 'build', 'DFL'] + modules, 'build.log')
        flags = ['-DwarningAsError=true']
    else:
        run(['lake', '--wfail', 'build', 'DFLSphere433'], 'build.log')
        flags = ['-DwarningAsError=true', '-DautoImplicit=false', '-DmaxSynthPendingDepth=3',
                 '-Dweak.linter.mathlibStandardSet=true', '-Dlinter.style.header=false',
                 '-Dlinter.style.longLine=false', '-Dlinter.style.whitespace=false',
                 '-Dlinter.style.setOption=false']
        run(['python3', 'scripts/audit_continuation_closure.py',
             '--upstream', '.lake/packages/DifferentialGeometry',
             '--output', str(out / 'source-closure.json')], 'source-closure-summary.log')
        closure = json.loads((out / 'source-closure.json').read_text())
        if sorted(closure['own_sources']) != sources:
            raise RuntimeError('Own import closure differs from the source manifest')
        if closure['missing'] or closure['forbidden_tokens']:
            raise RuntimeError('Source closure audit failed')

    forbidden = []
    for source in sources:
        content = code_only((project / source).read_text())
        for token in re.finditer(r'\b(?:sorry|admit|axiom|sorryAx|native_decide)\b', content):
            forbidden.append({'source': source, 'line': content[:token.start()].count('\n') + 1,
                              'token': token.group()})
    if forbidden:
        raise RuntimeError('Forbidden proof token in own sources: ' + json.dumps(forbidden))
    (out / 'own_source_audit.json').write_text(json.dumps({
        'own_source_count': len(sources), 'forbidden_tokens': forbidden}, indent=2) + '\n')

    print(f'[{project_name}] Strictly compiling {len(sources)} own Lean files.', flush=True)
    workers = max(1, min(16, int(os.environ.get('DFL_VERIFY_WORKERS', '4'))))

    def strict_compile(source):
        log = 'strict-sources/' + source.replace('/', '__') + '.log'
        run(['lake', 'env', 'lean'] + flags + [source], log)
        return source, log

    with ThreadPoolExecutor(max_workers=workers) as pool:
        strict_results = list(pool.map(strict_compile, sources))
    (out / 'strict-sources.txt').write_text('\n'.join(sources) + '\n')
    with (out / 'strict.log').open('w') as combined:
        for source, log in strict_results:
            combined.write('SOURCE ' + source + '\n')
            combined.write((out / log).read_text())
    if project_name == 'dfl2015':
        kernel_logs = ['declaration-audit.log', 'continuation-audit.log']
        for source, log in [('verification/Audit.lean', kernel_logs[0]),
                            ('verification/AuditContinuation.lean', kernel_logs[1])]:
            shutil.copyfile(out / ('strict-sources/' + source.replace('/', '__') + '.log'), out / log)
    else:
        kernel_logs = ['public-kernel-dependencies.log']
        source = 'DFLSphere433/ContinuationVerification.lean'
        shutil.copyfile(out / ('strict-sources/' + source.replace('/', '__') + '.log'), out / kernel_logs[0])
    report_count = check_kernel_audits(kernel_logs)
    check_sources()
    (out / 'SHA256SUMS').write_text(''.join(
        row['original_sha256'] + '  ' + row['release_relative_path'] + '\n' for row in rows))
    status.update(status='passed', lean=expected_version, build='passed', strict='passed',
                  kernel_dependencies='standard_only', kernel_report_count=report_count,
                  own_lean_source_count=len(sources), retained_source_hashes='all_matched',
                  strict_parallel_workers=workers, forbidden_tokens=[],
                  completed_utc=datetime.now(timezone.utc).isoformat())
    write_status()
    print(f'[{project_name}] Verification passed. Results: {out.relative_to(release)}', flush=True)
except Exception as error:
    status.update(status='failed', reason=normalize_log(str(error)),
                  completed_utc=datetime.now(timezone.utc).isoformat())
    write_status()
    print(normalize_log(str(error)), file=sys.stderr)
    sys.exit(1)
PY
