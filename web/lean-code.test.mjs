import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { leanTokens, highlightedLeanLines } from './lean-code.js';

const snapshot = JSON.parse(await readFile(new URL('./lean-sources.json', import.meta.url), 'utf8'));

test('the displayed source snapshot equals the original local Lean files', async () => {
  for (const [path, source] of Object.entries(snapshot.files)) {
    const original = await readFile(new URL(`../${path}`, import.meta.url), 'utf8');
    assert.equal(source, original.replaceAll('\r\n', '\n'), path);
    assert.equal(leanTokens(source).map(token => token.text).join(''), source, 'coloring preserves every character');
    assert.equal(highlightedLeanLines(source).length, source.split('\n').length, 'line numbers correspond to source');
  }
});

test('Lean nested comments and strings stay intact and HTML is escaped', () => {
  const source = '/- outer /- theorem 42 -/ comment -/\ntheorem x := "-- <script>"\n-- example <b>\n';
  const tokens = leanTokens(source);
  assert.equal(tokens[0].kind, 'comment');
  assert.equal(tokens[0].text, '/- outer /- theorem 42 -/ comment -/');
  assert.ok(tokens.some(token => token.kind === 'string' && token.text === '"-- <script>"'));
  const highlighted = highlightedLeanLines(source).join('\n');
  assert.ok(highlighted.includes('&lt;script&gt;'));
  assert.ok(!highlighted.includes('<script>'));
});
