import test from 'node:test';
import assert from 'node:assert/strict';
import { binomialTail, makeSamples } from './math.js';

test('the eight-element illustration has the correct exact probability', () => {
  assert.equal(binomialTail(8, 4, 0), 0);
  assert.equal(binomialTail(8, 4, 1), 1);
  assert.equal(binomialTail(8, 4, 0.5), 163 / 256);
  assert.ok(Math.abs(binomialTail(8, 4, 0.35) - 0.2936005638671875) < 1e-12);
});

test('the probability increases with density and remains in [0, 1]', () => {
  let previous = 0;
  for (let i = 0; i <= 100; i++) {
    const probability = binomialTail(8, 4, i / 100);
    assert.ok(probability >= previous - 1e-12 && probability <= 1 + 1e-12);
    previous = probability;
  }
});

test('sample dimensions and injected randomness are preserved', () => {
  const samples = makeSamples(12, 8, () => 0.25);
  assert.equal(samples.length, 12);
  assert.ok(samples.every(sample => sample.length === 8 && sample.every(value => value === 0.25)));
});
