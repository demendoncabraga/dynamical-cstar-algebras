#!/usr/bin/env python3
"""Check that each source declaration supports the final manuscript's results.

Use both kernel dependencies and Lean's source-reference index: a rewrite or simp
lemma may be needed to elaborate a proof even when it disappears from its term.
Run after lake build. Mathlib dependencies are outside this project-only check.
"""
import json
from pathlib import Path
import subprocess


def check(root):
    result = subprocess.run(['lake', 'env', 'lean', 'scripts/DependencyAudit.lean'],
                            cwd=root, check=True, capture_output=True, text=True)
    kernel = json.loads(result.stdout)
    declarations, indices = {}, {}
    sources = list((root / 'lean/DynamicalCStarAlgebras').rglob('*.lean'))
    entry = root / 'lean/DynamicalCStarAlgebras.lean'
    if entry.exists():
        sources.append(entry)
    for path in sorted(sources):
        module = '.'.join(path.relative_to(root / 'lean').with_suffix('').parts)
        index = root / '.lake/build/lib/lean' / Path(*module.split('.')).with_suffix('.ilean')
        data = json.loads(index.read_text())
        if data['decls']:
            indices[module] = data
        for name, loc in data['decls'].items():
            declarations[name] = (module, loc)

    def owner(name):
        while name:
            if name in declarations:
                return name
            name = name.rpartition('.')[0]
        return None

    edges = {name: set() for name in declarations}
    commands = {}
    for name, (module, loc) in declarations.items():
        commands.setdefault((module, *loc[:4]), set()).add(name)
    for names in commands.values():
        for name in names:
            edges[name].update(names)
    for data in indices.values():
        for encoded, reference in data['references'].items():
            constant = json.loads(encoded).get('c')
            if not constant:
                continue
            target = owner(constant['n'])
            if not target:
                continue
            for usage in reference['usages']:
                source = owner(usage[4]) if len(usage) > 4 and usage[4] else None
                if source:
                    edges[source].add(target)
    needed = set()
    for row in kernel['declarations']:
        source = owner(row['name'])
        if source is None:
            raise RuntimeError('Kernel dependency has no source declaration: ' + row['name'])
        needed.add(source)
        edges[source].update(owner(n) for n in row['deps'] if owner(n))
    pending = list(needed)
    while pending:
        source = pending.pop()
        for target in edges[source] - needed:
            needed.add(target)
            pending.append(target)
    unused = set(declarations) - needed
    if unused:
        raise RuntimeError('Source declarations outside the final proof dependencies: ' +
                           ', '.join(sorted(unused)))
    modules = {declarations[n][0] for n in needed}
    if modules != set(indices):
        raise RuntimeError('Unused source modules: ' + ', '.join(sorted(set(indices) - modules)))
    inventory = json.loads((root / 'lean/coverage.json').read_text())
    registered = {item['declaration'] for item in inventory['items'] if item.get('declaration')}
    if registered != set(declarations):
        raise RuntimeError('Inventory/source mismatch. Missing: ' +
                           ', '.join(sorted(set(declarations) - registered)) +
                           '; stale: ' + ', '.join(sorted(registered - set(declarations))))
    if set(inventory['paper_roots']) != set(kernel['roots']):
        raise RuntimeError('Paper roots differ between inventory and dependency audit.')
    print(f'Dependency audit passed: {len(needed)} source declarations in {len(modules)} modules, '
          f'all supporting {len(kernel["roots"])} manuscript statements.')


if __name__ == '__main__':
    check(Path(__file__).resolve().parent.parent)
