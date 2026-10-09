import { messages, sourceRoot } from './data.js';
import { highlightedLeanLines } from './lean-code.js';

export function createSourceReader({ getLanguage }) {
  const $ = selector => document.querySelector(selector);
  const t = key => messages[key]?.[getLanguage() === 'zh' ? 1 : 0] ?? key;
  const dialog = $('#lean-source-dialog');
  const scroller = $('#lean-source-scroll');
  let sourcePromise, current, source = '', lineCount = 1, version = 0, statusKey = '';

  function status(key) {
    statusKey = key;
    $('#lean-source-status').hidden = !key;
    $('#lean-source-status').textContent = key ? t(key) : '';
  }

  function sourceData() {
    if (!sourcePromise) {
      sourcePromise = fetch(new URL('./lean-sources.json', import.meta.url)).then(response => {
        if (!response.ok) throw new Error(`Source HTTP ${response.status}`);
        return response.json();
      }).catch(error => { sourcePromise = null; throw error; });
    }
    return sourcePromise;
  }

  function setLanguage() {
    if (!current) return;
    $('#lean-source-path').textContent = `${current.path} · ${t('sourceLine')} ${current.line}`;
    scroller.setAttribute('aria-label', `${t('sourcePanel')}: ${current.path}`);
    $('#source-line-input').setAttribute('aria-label', t('sourceLine'));
    status(statusKey);
  }

  function goToLine(line) {
    if (!source) return;
    const number = Math.max(1, Math.min(lineCount, Math.round(Number(line) || 1)));
    $('#source-line-input').value = number;
    const target = $(`#lean-source-code [data-line="${number}"]`);
    document.querySelectorAll('.source-line.is-location').forEach(element => element.classList.remove('is-location'));
    target.classList.add('is-location');
    scroller.scrollTop = target.offsetTop - scroller.offsetTop - Math.min(100, scroller.clientHeight / 3);
    scroller.scrollLeft = 0;
  }

  async function open({ path, line = 1, length = 1 }) {
    const request = ++version;
    current = { path, line: Math.max(1, Number(line) || 1), length: Math.max(1, Number(length) || 1) };
    source = '';
    $('#lean-source-title').textContent = path.split('/').at(-1);
    $('#source-github').href = `${sourceRoot}${path}#L${current.line}`;
    $('#source-copy').disabled = true;
    $('#source-copy').textContent = t('sourceCopy');
    $('#source-declaration').disabled = true;
    $('#source-go').disabled = true;
    $('#source-line-input').value = current.line;
    $('#lean-source-code').innerHTML = '';
    setLanguage();
    status('sourceLoading');
    if (!dialog.open) dialog.showModal();
    document.body.style.overflow = 'hidden';
    try {
      const data = await sourceData();
      if (request !== version) return;
      if (!Object.hasOwn(data.files, path)) throw new Error('Source is not part of the local snapshot.');
      source = data.files[path];
      const lines = highlightedLeanLines(source);
      lineCount = lines.length;
      $('#source-line-input').max = lineCount;
      $('#lean-source-code').innerHTML = lines.map((content, index) => `<span class="source-line ${index + 1 >= current.line && index + 1 < current.line + current.length ? 'is-highlighted' : ''}" data-line="${index + 1}"><span class="source-line-number" aria-hidden="true">${index + 1}</span><code>${content || ' '}</code></span>`).join('');
      status('');
      $('#source-copy').disabled = false;
      $('#source-declaration').disabled = false;
      $('#source-go').disabled = false;
      goToLine(current.line);
    } catch {
      if (request === version) status('sourceError');
    }
  }

  document.addEventListener('click', event => {
    const link = event.target.closest('[data-lean-source]');
    if (!link) return;
    event.preventDefault();
    open({ path: link.dataset.leanSource, line: link.dataset.leanLine, length: link.dataset.leanLength });
  });
  $('#lean-source-close').addEventListener('click', () => dialog.close());
  dialog.addEventListener('close', () => {
    document.body.style.overflow = document.querySelector('dialog[open]') ? 'hidden' : '';
  });
  dialog.addEventListener('click', event => {
    if (event.target !== dialog) return;
    const rect = dialog.getBoundingClientRect();
    if (event.clientX < rect.left || event.clientX > rect.right || event.clientY < rect.top || event.clientY > rect.bottom) dialog.close();
  });
  $('#source-go').addEventListener('click', () => goToLine($('#source-line-input').value));
  $('#source-line-input').addEventListener('keydown', event => { if (event.key === 'Enter') goToLine(event.target.value); });
  $('#source-declaration').addEventListener('click', () => goToLine(current.line));
  $('#source-copy').addEventListener('click', async () => {
    if (!source) return;
    try { await navigator.clipboard.writeText(source); $('#source-copy').textContent = t('sourceCopied'); }
    catch { $('#source-copy').textContent = t('sourceCopyError'); }
  });
  return { open, setLanguage };
}
