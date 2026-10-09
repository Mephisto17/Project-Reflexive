// Graph navigation is independent of the DOM and the Lean source indexer.
export function indexProject(project) {
  const byId = new Map(project.nodes.map(node => [node.id, node]));
  const usedBy = new Map(project.nodes.map(node => [node.id, []]));
  for (const node of project.nodes) {
    for (const dependency of node.dependsOn) {
      if (!byId.has(dependency)) throw new Error(`Unknown prerequisite: ${dependency}`);
      usedBy.get(dependency).push(node.id);
    }
  }
  return { ...project, byId, usedBy };
}

export function visibleDeclarations(project, selected, scope) {
  if (!project.byId.has(selected)) throw new Error(`Unknown declaration: ${selected}`);
  if (scope === 'all') return project.nodes;
  const visible = new Set([selected]);
  if (scope === 'neighbors') {
    project.byId.get(selected).dependsOn.forEach(id => visible.add(id));
    project.usedBy.get(selected).forEach(id => visible.add(id));
  } else {
    const visit = id => {
      for (const parent of project.byId.get(id).dependsOn) {
        if (!visible.has(parent)) { visible.add(parent); visit(parent); }
      }
    };
    visit(selected);
  }
  return project.nodes.filter(node => visible.has(node.id));
}

export function layoutDeclarations(nodes) {
  const byId = new Map(nodes.map(node => [node.id, node]));
  const ranks = new Map();
  const active = new Set();
  const rank = id => {
    if (ranks.has(id)) return ranks.get(id);
    if (active.has(id)) throw new Error('A cycle was found in the declaration index.');
    active.add(id);
    const parents = byId.get(id).dependsOn.filter(parent => byId.has(parent));
    const value = parents.length ? Math.max(...parents.map(rank)) + 1 : 0;
    active.delete(id);
    ranks.set(id, value);
    return value;
  };
  nodes.forEach(node => rank(node.id));
  const layers = [];
  for (const node of nodes) (layers[ranks.get(node.id)] ??= []).push(node);
  layers.forEach(layer => layer.sort((a, b) => `${a.module}.${a.name}`.localeCompare(`${b.module}.${b.name}`)));
  // Barycentric passes keep related declarations close within each layer.
  for (let pass = 0; pass < 4; pass++) {
    const order = new Map();
    layers.forEach(layer => layer.forEach((node, index) => order.set(node.id, index)));
    for (let index = 1; index < layers.length; index++) {
      const score = node => {
        const parents = node.dependsOn.filter(id => byId.has(id));
        return parents.length ? parents.reduce((sum, id) => sum + order.get(id), 0) / parents.length : order.get(node.id);
      };
      layers[index].sort((a, b) => score(a) - score(b) || a.name.localeCompare(b.name));
    }
  }
  const nodeWidth = 208, nodeHeight = 62, gapX = 80, gapY = 20, padding = 40;
  const height = Math.max(1, ...layers.map(layer => layer.length)) * (nodeHeight + gapY) - gapY + padding * 2;
  const width = Math.max(1, layers.length) * (nodeWidth + gapX) - gapX + padding * 2;
  const positions = new Map();
  layers.forEach((layer, depth) => {
    const layerHeight = layer.length * (nodeHeight + gapY) - gapY;
    layer.forEach((node, index) => positions.set(node.id, {
      x: padding + depth * (nodeWidth + gapX), y: (height - layerHeight) / 2 + index * (nodeHeight + gapY),
    }));
  });
  const edges = nodes.flatMap(node => node.dependsOn.filter(id => byId.has(id)).map(id => ({ from: id, to: node.id })));
  return { positions, edges, width, height, nodeWidth, nodeHeight };
}
