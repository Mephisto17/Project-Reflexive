/** Exact probability for at least `minimum` successes in `n` independent trials. */
export function binomialTail(n, minimum, p) {
  let total = 0;
  let coefficient = 1;
  for (let k = 0; k <= n; k++) {
    if (k >= minimum) total += coefficient * p ** k * (1 - p) ** (n - k);
    coefficient *= (n - k) / (k + 1);
  }
  return total;
}

/** A sample is deliberately kept separate from the exact probability. */
export function makeSamples(count = 12, size = 8, random = Math.random) {
  return Array.from({ length: count }, () => Array.from({ length: size }, random));
}
