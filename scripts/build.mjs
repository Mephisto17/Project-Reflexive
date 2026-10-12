import { mkdir, copyFile, cp, writeFile, rm } from 'node:fs/promises';
import { fileURLToPath } from 'node:url';
import path from 'node:path';

const root = fileURLToPath(new URL('../', import.meta.url));
const output = path.join(root, 'dist');
await rm(output, { recursive: true, force: true });
await mkdir(output, { recursive: true });
await copyFile(path.join(root, 'index.html'), path.join(output, 'index.html'));
await cp(path.join(root, 'web'), path.join(output, 'web'), {
  recursive: true,
  filter: (source) => !source.endsWith('.test.mjs'),
});
await writeFile(path.join(output, '.nojekyll'), '');
console.log('Built static site in dist/ — ready for any static host.');
