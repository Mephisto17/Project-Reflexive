import http from 'node:http';
import { readFile } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const args = process.argv.slice(2);
const portIndex = args.indexOf('--port');
const port = Number(portIndex >= 0 ? args[portIndex + 1] : process.env.PORT || 5173);
const root = path.resolve(fileURLToPath(new URL(args.includes('--dist') ? '../dist/' : '../', import.meta.url)));
const types = { '.html': 'text/html; charset=utf-8', '.css': 'text/css; charset=utf-8', '.js': 'text/javascript; charset=utf-8', '.svg': 'image/svg+xml', '.jpg': 'image/jpeg', '.bib': 'text/plain; charset=utf-8', '.mjs': 'text/javascript; charset=utf-8', '.json': 'application/json; charset=utf-8' };

http.createServer(async (req, res) => {
  try {
    const pathname = decodeURIComponent(new URL(req.url, 'http://localhost').pathname);
    if (pathname === '/fang-xuan') {
      res.writeHead(301, { Location: './fang-xuan/' }).end();
      return;
    }
    const relative = pathname === '/' ? 'index.html' : pathname === '/fang-xuan/' ? 'fang-xuan/index.html' : pathname.slice(1);
    const target = path.resolve(root, relative);
    const publicPath = path.relative(root, target).split(path.sep).join('/');
    if (!target.startsWith(root + path.sep) || (publicPath !== 'index.html' && !publicPath.startsWith('web/') && !publicPath.startsWith('fang-xuan/')) || publicPath.endsWith('.test.mjs') || publicPath.endsWith('README.md')) {
      res.writeHead(404).end('Not found');
      return;
    }
    const body = await readFile(target);
    res.writeHead(200, { 'Content-Type': types[path.extname(target)] || 'application/octet-stream', 'Cache-Control': 'no-cache', 'X-Content-Type-Options': 'nosniff' });
    res.end(body);
  } catch {
    res.writeHead(404).end('Not found');
  }
}).listen(port, '127.0.0.1', () => console.log(`Project Reflexive → http://localhost:${port}`));
