#!/usr/bin/env python3
"""Build DynamicalCStarAlgebras and audit the declarations registered in its coverage inventory."""

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tomllib


def lean_code(text):
    """Remove nested block comments, line comments and strings for a keyword scan."""
    out = []
    i = 0
    depth = 0
    string = False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1
                i += 2
            elif text.startswith('-/', i):
                depth -= 1
                i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif string:
            if text[i] == '\\':
                i += 2
            elif text[i] == '"':
                string = False
                i += 1
            else:
                out.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif text.startswith('/-', i):
            depth = 1
            out.append(' ')
            i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            string = True
            out.append(' ')
            i += 1
        else:
            out.append(text[i])
            i += 1
    return ''.join(out)


def fail(message):
    raise RuntimeError(message)


def validate_dependency_pins(root):
    """Check the reviewed toolchain and immutable dependency lockfile."""
    if (root / 'lean-toolchain').read_text().strip() != 'leanprover/lean4:v4.33.1':
        fail('Unexpected Lean toolchain; review the verification scope before upgrading.')
    config = tomllib.loads((root / 'lakefile.toml').read_text())
    requirements = config.get('require', [])
    if len(requirements) != 1 or requirements[0] != dict(
            name='mathlib', git='https://github.com/leanprover-community/mathlib4.git',
            rev='v4.33.1'):
        fail('Unexpected Mathlib requirement; preserve the reviewed dependency pins.')
    packages = json.loads((root / 'lake-manifest.json').read_text())['packages']
    mathlib = [p for p in packages if p.get('name') == 'mathlib']
    if len(mathlib) != 1 or mathlib[0].get('rev') != '0df444a360eaa60ab8c11dca51a86af692955474':
        fail('Mathlib lockfile revision differs from the reviewed version.')
    for package in packages:
        if package.get('type') != 'git' or not re.fullmatch(r'[0-9a-f]{40}', package.get('rev', '')):
            fail('Dependency lacks an immutable Git revision: ' + str(package.get('name')))



def validate_terminal_scope(coverage, items):
    """Require nonempty, fully proved coverage without external assumptions."""
    unfinished = [item['id'] for item in items if item['status'] != 'verified']
    if coverage.get('verification_scope') != 'unconditional':
        fail('Only unconditional verification is supported.')
    if coverage.get('inventory_complete') is not True or unfinished or not items:
        fail('Formalization is incomplete. Complete the inventory and verify every entry. '
             'Open entries: ' + ', '.join(unfinished))
    names = {item.get('declaration') for item in items}
    roots = coverage.get('paper_roots', [])
    if not roots or not set(roots) <= names:
        fail('Terminal coverage requires registered manuscript roots.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--terminal', action='store_true', help='require complete coverage and proofs')
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    validate_dependency_pins(root)
    coverage = json.loads((root / 'lean/coverage.json').read_text())
    if coverage.get('source') != 'paper/main.tex':
        fail('Unexpected manuscript path.')
    digest = hashlib.sha256((root / coverage['source']).read_bytes()).hexdigest()
    if coverage.get('source_sha256') != digest:
        fail('Manuscript changed: review coverage and update its source_sha256.')
    if coverage.get('verification_scope') != 'unconditional':
        fail('Only unconditional verification is supported.')
    items = coverage.get('items', [])
    if not isinstance(items, list):
        fail('The coverage inventory is empty or malformed.')
    ids = [item['id'] for item in items]
    if len(set(ids)) != len(ids):
        fail('Coverage IDs must be unique.')
    names = []
    for item in items:
        if item['status'] not in {'not_started', 'in_progress', 'verified'}:
            fail('Invalid status for ' + item['id'])
        name = item.get('declaration')
        if name:
            # Prevent newline or Lean-command injection in generated audit commands.
            if not isinstance(name, str) or re.search(r'[\s;`"\\]', name):
                fail('Expected a plain qualified declaration name for ' + item['id'])
            names.append(name)
        elif item['status'] == 'verified':
            fail('Verified entry has no declaration: ' + item['id'])
    names = list(dict.fromkeys(names))
    if args.terminal:
        validate_terminal_scope(coverage, items)
        if not names:
            fail('No declarations registered for terminal audit.')

    holes = []
    for path in sorted((root / 'lean').rglob('*.lean')):
        code = lean_code(path.read_text())
        for number, line in enumerate(code.splitlines(), 1):
            if re.search(r'\baxiom\b', line):
                fail(f'Project axiom declaration: {path.relative_to(root)}:{number}')
            if re.search(r'\b(sorry|admit|sorryAx)\b', line):
                holes.append(f'{path.relative_to(root)}:{number}')
    if holes:
        print('Unfinished proof terms: ' + ', '.join(holes), flush=True)
        fail('Proof placeholders remain.')

    if shutil.which('lake') is None:
        fail('Lake is unavailable. Run sh scripts/setup.sh first.')
    subprocess.run(['lake', 'build'], cwd=root, check=True)
    if args.terminal:
        subprocess.run([sys.executable, 'scripts/check_dependencies.py'], cwd=root, check=True)
    audit = 'import DynamicalCStarAlgebras\n\n'
    audit += '-- Generated by scripts/audit.py from lean/coverage.json. Do not edit by hand.\n'
    if names:
        audit += '\n'.join('#print axioms ' + name for name in names) + '\n'
    else:
        audit += '-- No declarations have been registered yet; this is not a proof certificate.\n'
    audit_path = root / '.lake/audit/Audit.lean'
    audit_path.parent.mkdir(parents=True, exist_ok=True)
    audit_path.write_text(audit)
    result = subprocess.run(['lake', 'env', 'lean', str(audit_path)], cwd=root,
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    print(result.stdout, end='', flush=True)
    if result.returncode:
        fail('Lean could not check the generated audit.')
    if not names:
        print('Build checked; no mathematical declarations are registered. Formalization not started.')
        return

    reports = {}
    for match in re.finditer(r"'([^\n]+)'\s+depends on axioms:\s*\[([^\]]*)\]", result.stdout):
        reports[match[1]] = {s.strip() for s in match[2].split(',') if s.strip()}
    for match in re.finditer(r"'([^\n]+)'\s+does not depend on any axioms", result.stdout):
        reports[match[1]] = set()
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    for name in names:
        if name not in reports:
            fail('Missing or unrecognized axiom report for ' + name)
        unexpected = reports[name] - allowed
        if unexpected:
            fail('Unexpected axioms for ' + name + ': ' + ', '.join(sorted(unexpected)))
    if args.terminal:
        print('Terminal mechanical audit passed. Source-to-statement review is also required.')
    else:
        print('Intermediate audit passed. This is not a completed-paper certificate.')


if __name__ == '__main__':
    try:
        main()
    except (RuntimeError, KeyError, ValueError, OSError, subprocess.CalledProcessError) as error:
        print('Audit failed: ' + str(error), file=sys.stderr)
        sys.exit(1)
