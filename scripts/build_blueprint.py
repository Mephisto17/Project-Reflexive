"""Build a browsable blueprint from local Lean declaration references.

This is a conservative source index, not an extraction of elaborated proof terms.
It resolves explicit names within namespaces and imported local modules. Mathlib,
tactic-generated dependencies, and unresolved method notation are omitted.
"""
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PROJECTS = [
    ('kahn-kalai', 'Kahn-Kalai', ['KahnKalai', 'Solution.lean', 'Paper.lean'], 'ParkPhamPaper.theorem_1_1_increasing'),
    ('selector', 'talagrand-conjecture-5-7', ['TalagrandSelector'], 'TalagrandSelector.conjecture_5_7_finite_expectation'),
    ('five', 'talagrand-five-conjectures', ['TalagrandConjectures'], 'TalagrandConjectures.conjecture_9_1'),
    ('smallness', 'small-vs-weakly-small-and-discrete-convexity', ['TalagrandIntegral', 'TalagrandConjectures'], 'TalagrandIntegral.comparison_theorem_1_1'),
]
COMMAND = re.compile(r'^\s*(?:(?P<scope>namespace|section|end)\b\s*(?P<scope_name>[^\s\n]*)|(?:@\[[^\n]*?\]\s*)?(?P<modifiers>(?:(?:private|protected|noncomputable|unsafe)\s+)*)(?P<kind>theorem|lemma|def|abbrev|structure|inductive|class)\s+(?P<name>[^\s(:{\[=]+))', re.M)
IDENTIFIER = re.compile(r"[A-Za-z_\u00c0-\uffff][A-Za-z_0-9\u00c0-\uffff'₀-₉]*(?:\.[A-Za-z_\u00c0-\uffff][A-Za-z_0-9\u00c0-\uffff'₀-₉]*)*")


def without_comments(source):
    chars = list(source)
    index = 0
    depth = 0
    in_string = False
    while index < len(source):
        if not depth and source[index] == '"' and (index == 0 or source[index - 1] != '\\'):
            in_string = not in_string
        if not in_string and source[index:index + 2] == '/-':
            depth += 1
            chars[index:index + 2] = [' ', ' ']
            index += 2
            continue
        if depth and source[index:index + 2] == '-/':
            depth -= 1
            chars[index:index + 2] = [' ', ' ']
            index += 2
            continue
        if not depth and not in_string and source[index:index + 2] == '--':
            stop = source.find('\n', index)
            stop = len(source) if stop < 0 else stop
            chars[index:stop] = [' '] * (stop - index)
            index = stop
            continue
        if depth or in_string:
            if source[index] != '\n':
                chars[index] = ' '
        index += 1
    return ''.join(chars)


def project_data(project_id, directory, paths, default):
    project = ROOT / directory
    files = []
    for relative in paths:
        target = project / relative
        files.extend([target] if target.is_file() else sorted(target.glob('*.lean')))
    nodes = []
    modules = {}
    audit_files = list((project / 'verification').glob('axioms*'))
    reports = {str(file.relative_to(ROOT)).replace('\\', '/'): file.read_text(encoding='utf-8', errors='replace') for file in audit_files}

    for file in files:
        if file.stem == 'Audit':
            continue
        original = file.read_text(encoding='utf-8')
        source = without_comments(original)
        module = '.'.join(file.relative_to(project).with_suffix('').parts)
        modules[module] = re.findall(r'^import\s+(\S+)', source, re.M)
        commands = list(COMMAND.finditer(source))
        stack = []
        for index, command in enumerate(commands):
            if command.group('scope'):
                scope, name = command.group('scope'), command.group('scope_name')
                if scope in ['namespace', 'section']:
                    stack.append((scope, name))
                elif stack:
                    stack.pop()
                continue
            namespace = '.'.join(name for kind, name in stack if kind == 'namespace' and name)
            name = command.group('name')
            full_name = f'{namespace}.{name}' if namespace else name
            stop = commands[index + 1].start() if index + 1 < len(commands) else len(source)
            start = command.start()
            body = source[start:stop].strip()
            raw = original[start:stop].strip()
            header_stop = re.search(r':=|\bwhere\b', body)
            # Preserve the original signature, including any mathematical comments.
            statement = body[:header_stop.start()].strip() if header_stop else body
            preceding = original[:start].rstrip()
            doc = ''
            if preceding.endswith('-/'):
                doc_start = preceding.rfind('/--')
                if doc_start >= 0:
                    possible = preceding[doc_start + 3:-2]
                    if '-/' not in possible:
                        doc = re.sub(r'\s+', ' ', possible).strip()
            line = original[:start].count('\n') + 1
            while line <= len(original.splitlines()) and not original.splitlines()[line - 1].strip():
                line += 1
            audit = next((path for path, report in reports.items() if full_name in report), None)
            node = {
                'id': f'{project_id}:{full_name}', 'name': full_name, 'shortName': name,
                'kind': command.group('kind'), 'module': module, 'namespace': namespace,
                'source': str(file.relative_to(ROOT)).replace('\\', '/'), 'line': line,
                'statement': statement, 'documentation': doc,
                'auditSource': audit, 'dependsOn': [],
                '_body': body, '_private': 'private' in command.group('modifiers'),
                '_opens': re.findall(r'^\s*open\s+([^\n]+)', source[:start], re.M),
            }
            nodes.append(node)

    by_name = {node['name']: node for node in nodes}
    assert len(by_name) == len(nodes), f'Duplicate declarations in {project_id}'

    def reachable(module, visited=None):
        visited = set() if visited is None else visited
        if module in visited:
            return visited
        visited.add(module)
        for dependency in modules.get(module, []):
            if dependency in modules:
                reachable(dependency, visited)
            else:
                # Root aggregation files such as TalagrandIntegral.lean are not
                # graph nodes, but their local imports still establish reachability.
                aggregation = project / Path(*dependency.split('.')).with_suffix('.lean')
                if aggregation.exists():
                    imports = re.findall(r'^import\s+(\S+)', without_comments(aggregation.read_text(encoding='utf-8')), re.M)
                    for imported in imports:
                        if imported in modules:
                            reachable(imported, visited)
        return visited

    reachable_by_module = {module: reachable(module) for module in modules}
    for node in nodes:
        namespace_parts = node['namespace'].split('.') if node['namespace'] else []
        namespaces = ['.'.join(namespace_parts[:index]) for index in range(len(namespace_parts), 0, -1)]
        opens = [item for opened in node['_opens'] for item in opened.split() if re.fullmatch(r'[\w.]+', item)]
        dependencies = set()
        for token in set(IDENTIFIER.findall(node['_body'])):
            candidates = [f'{namespace}.{token}' for namespace in namespaces] + [token] + [f'{opened}.{token}' for opened in opens]
            for name in candidates:
                other = by_name.get(name)
                if not other or other is node or other['module'] not in reachable_by_module[node['module']]:
                    continue
                if other['_private'] and other['module'] != node['module']:
                    continue
                if other['module'] == node['module'] and other['line'] >= node['line']:
                    continue
                dependencies.add(other['id'])
                break
        node['dependsOn'] = sorted(dependencies)
    for node in nodes:
        for key in ['_body', '_private', '_opens']:
            del node[key]

    assert default in by_name, f'Default declaration missing: {default}'
    identifiers = {node['id'] for node in nodes}
    assert all(dependency in identifiers for node in nodes for dependency in node['dependsOn'])
    return {'id': project_id, 'defaultNode': f'{project_id}:{default}', 'nodes': nodes}


if __name__ == '__main__':
    projects = [project_data(*config) for config in PROJECTS]
    data = {'version': 1, 'method': 'Static explicit declaration references, restricted to local imported modules and resolvable namespaces. Not elaborated kernel dependencies.', 'projects': projects}
    output = ROOT / 'web' / 'blueprint-data.json'
    output.write_text(json.dumps(data, ensure_ascii=False, separators=(',', ':')), encoding='utf-8')
    sources = sorted({node['source'] for project in projects for node in project['nodes']})
    source_data = {'version': 1, 'files': {path: (ROOT / path).read_text(encoding='utf-8') for path in sources}}
    (ROOT / 'web' / 'lean-sources.json').write_text(json.dumps(source_data, ensure_ascii=False, separators=(',', ':')), encoding='utf-8')
    for project in projects:
        print(f"{project['id']}: {len(project['nodes'])} declarations, {sum(len(node['dependsOn']) for node in project['nodes'])} source-reference edges")
    print('Wrote web/blueprint-data.json')
    print(f'Wrote web/lean-sources.json ({len(sources)} unchanged local Lean files)')
