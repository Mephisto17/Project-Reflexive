import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { indexProject, visibleDeclarations, layoutDeclarations } from './blueprint-graph.js';

const data = JSON.parse(await readFile(new URL('./blueprint-data.json', import.meta.url), 'utf8'));

test('every collection has closed, acyclic references and correctly directed layers', () => {
  for (const collection of data.projects) {
    const project = indexProject(collection);
    assert.ok(project.byId.has(project.defaultNode));
    assert.equal(project.byId.size, project.nodes.length, 'names are unique within each collection');
    const layout = layoutDeclarations(project.nodes);
    assert.equal(layout.positions.size, project.nodes.length);
    for (const edge of layout.edges) {
      assert.ok(layout.positions.get(edge.from).x < layout.positions.get(edge.to).x, `${edge.from} precedes ${edge.to}`);
      assert.ok(project.usedBy.get(edge.from).includes(edge.to));
    }
    for (const position of layout.positions.values()) {
      assert.ok(position.x >= 0 && position.x + layout.nodeWidth <= layout.width);
      assert.ok(position.y >= 0 && position.y + layout.nodeHeight <= layout.height);
    }
  }
});

test('prerequisite views contain the full transitive closure without unrelated declarations', () => {
  const project = indexProject({ nodes: [
    { id: 'a', dependsOn: [] }, { id: 'b', dependsOn: ['a'] },
    { id: 'c', dependsOn: ['b'] }, { id: 'd', dependsOn: ['c'] }, { id: 'e', dependsOn: [] },
  ] });
  assert.deepEqual(visibleDeclarations(project, 'c', 'ancestors').map(node => node.id), ['a', 'b', 'c']);
  assert.deepEqual(visibleDeclarations(project, 'c', 'neighbors').map(node => node.id), ['b', 'c', 'd']);
  assert.equal(visibleDeclarations(project, 'c', 'all').length, 5);
  assert.throws(() => visibleDeclarations(project, 'missing', 'all'), /Unknown declaration/);
});

test('broken source indexes fail instead of presenting invented graph edges', () => {
  assert.throws(() => indexProject({ nodes: [{ id: 'a', dependsOn: ['missing'] }] }), /Unknown prerequisite/);
  assert.throws(() => layoutDeclarations([
    { id: 'a', name: 'a', module: 'M', dependsOn: ['b'] },
    { id: 'b', name: 'b', module: 'M', dependsOn: ['a'] },
  ]), /cycle/);
});
