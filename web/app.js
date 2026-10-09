import { messages, nodes, results, references, art, sourceRoot } from './data.js';
import { binomialTail, makeSamples } from './math.js';
import { createBlueprint } from './blueprint.js';
import { createSourceReader } from './source-reader.js';

const $ = (selector) => document.querySelector(selector);
const $$ = (selector) => [...document.querySelectorAll(selector)];
let language = 'en';
try { language = localStorage.getItem('reflexive-language') === 'zh' ? 'zh' : 'en'; } catch { /* Storage is optional. */ }
let mode = 'intuition';
let selectedNode = 'comparison';
let activeFilter = 'all';
let openResult = null;
let samples = makeSamples();

const t = (key) => messages[key]?.[language === 'zh' ? 1 : 0] ?? key;
const local = (value) => typeof value === 'string' ? value : value[language];
const escape = (value) => String(value).replace(/[&<>"']/g, (character) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' })[character]);

function applyLanguage() {
  document.documentElement.lang = language === 'zh' ? 'zh-CN' : 'en';
  document.title = language === 'zh' ? 'Project Reflexive — 看见思路，信任证明。' : 'Project Reflexive — Follow the idea. Trust the proof.';
  $$('[data-i18n]').forEach(element => { element.innerHTML = t(element.dataset.i18n); });
  $$('[data-i18n-aria]').forEach(element => element.setAttribute('aria-label', t(element.dataset.i18nAria)));
  $$('[data-i18n-placeholder]').forEach(element => { element.placeholder = t(element.dataset.i18nPlaceholder); });
  $$('[data-language]').forEach(button => button.setAttribute('aria-pressed', String(button.dataset.language === language)));
  renderNode();
  renderResults();
  renderExperiment();
  blueprint.setLanguage();
  sourceReader.setLanguage();
  if (openResult) renderDialog(openResult);
}

function renderNode() {
  const node = nodes[selectedNode];
  $('#detail-kind').textContent = t(node.kind);
  $('#detail-title').textContent = local(node.title);
  $('#detail-description').textContent = local(mode === 'formal' ? node.formal : node.description);
  $('#detail-source').href = sourceRoot + node.source;
  const [path, fragment] = node.source.split('#L');
  $('#detail-source').dataset.leanSource = path;
  $('#detail-source').dataset.leanLine = fragment || 1;
  $('#detail-source').setAttribute('aria-haspopup', 'dialog');
  $('#detail-source').removeAttribute('target');
  $('#detail-code').hidden = mode !== 'formal';
  $('#detail-code').textContent = node.code;
  $$('[data-node]').forEach(button => {
    const selected = button.dataset.node === selectedNode;
    button.classList.toggle('is-selected', selected);
    button.setAttribute('aria-pressed', String(selected));
  });
  $$('[data-edge]').forEach(edge => edge.classList.toggle('is-active', edge.dataset.edge.split('-').includes(selectedNode)));
  $$('[data-mode]').forEach(button => button.setAttribute('aria-pressed', String(button.dataset.mode === mode)));
}

function renderResults() {
  const query = $('#search').value.toLocaleLowerCase().trim();
  const visible = results.filter(result => {
    const allText = [result.title.en, result.title.zh, result.summary.en, result.summary.zh, result.byline.en, result.byline.zh, result.declaration, result.credit.en, ...result.tags].join(' ').toLocaleLowerCase();
    return (activeFilter === 'all' || result.tags.includes(activeFilter)) && (!query || allText.includes(query));
  });
  $('#result-grid').innerHTML = visible.map(result => `<article class="result-card">
    <div class="card-content"><div class="card-topline"><span class="card-number">${result.number} /</span><span>${escape(local(result.category))}</span></div>
    <h3>${escape(local(result.title))}</h3><p class="card-description">${escape(local(result.summary))}</p>
    <p class="card-byline">${escape(local(result.byline))}</p>
    <div class="card-footer"><span class="record-badge"><svg viewBox="0 0 12 12" aria-hidden="true"><path d="m2 6 3 3 5-6"/></svg>${t('records')}</span><button class="result-open" type="button" data-result="${result.id}" aria-label="${escape(`${t('historyLink')} · ${local(result.title)}`)}">${t('exploreResult')}</button></div></div>
    <div class="card-art" aria-hidden="true"><svg viewBox="0 0 124 140">${art[Number(result.number) - 1]}</svg></div></article>`).join('');
  $('#empty-state').hidden = visible.length !== 0;
  $$('[data-filter]').forEach(button => button.setAttribute('aria-pressed', String(button.dataset.filter === activeFilter)));
}

function renderDialog(result) {
  $('#dialog-content').innerHTML = `<div class="dialog-eyebrow">${result.number} / ${escape(local(result.category))}</div>
    <h2 id="dialog-title">${escape(local(result.title))}</h2><p class="dialog-intro">${escape(local(result.summary))}</p>
    <section class="dialog-section"><h3>${t('historyTitle')}</h3><p>${escape(local(result.history))}</p></section>
    <section class="dialog-section"><h3>${t('proofCredit')}</h3><p>${escape(local(result.credit))}</p></section>
    <section class="dialog-section"><h3>${t('scopeTitle')}</h3><p>${escape(local(result.scope))}</p><code>${escape(result.declaration)}</code></section>
    <section class="dialog-section"><h3>${t('formalizationTitle')}</h3><p>${escape(local(result.formalization))}</p></section>
    <section class="dialog-section"><h3>${t('bibliographyTitle')}</h3><ol class="bibliography">${result.bibliography.map(key => {
      const reference = references[key];
      return `<li><span class="reference-authors">${escape(local(reference.authors))}</span><a href="${escape(reference.url)}" target="_blank" rel="noopener noreferrer">${escape(reference.title)} ↗</a><p>${escape(local(reference.publication))}</p>${reference.preprint ? `<a class="preprint-link" href="${escape(reference.preprint)}" target="_blank" rel="noopener noreferrer">${language === 'zh' ? '所引版本 / 作者稿件' : 'Cited version / author manuscript'} ↗</a>` : ''}</li>`;
    }).join('')}</ol></section>
    <div class="dialog-links"><a class="button button-primary" href="${sourceRoot + result.path}README.md" target="_blank" rel="noopener noreferrer">${t('readScope')} ↗</a><a class="button button-secondary" href="${sourceRoot.replace('/blob/', '/tree/') + result.path}verification/" target="_blank" rel="noopener noreferrer">${t('readRecords')} ↗</a><button class="button button-secondary" id="dialog-map" type="button">${t('openMap')} ↗</button></div>
    <p class="dialog-disclaimer">${t('suppliedEvidence')}</p>`;
}

function renderExperiment() {
  const p = Number($('#probability').value) / 100;
  const exact = binomialTail(8, 4, p);
  let qualifying = 0;
  $('#samples').innerHTML = samples.map(sample => {
    const count = sample.filter(value => value < p).length;
    if (count >= 4) qualifying++;
    return `<div class="sample ${count >= 4 ? 'qualifies' : ''}" aria-hidden="true">${sample.map(value => `<span class="sample-dot ${value < p ? 'kept' : ''}"></span>`).join('')}</div>`;
  }).join('');
  $('#samples').setAttribute('aria-label', language === 'zh' ? `12 个随机子集中，${qualifying} 个至少保留了四个点。每个点独立地以概率 ${p} 被保留。` : `${qualifying} of 12 sampled subsets kept at least four points. Each point is independently kept with probability ${p}.`);
  $('#sample-count').textContent = language === 'zh' ? `${qualifying} / 12 组符合` : `${qualifying} / 12 in this sample`;
  $('#p-value').textContent = p.toFixed(2);
  $('#probability').setAttribute('aria-valuetext', language === 'zh' ? `${Math.round(p * 100)}% 的保留概率` : `${Math.round(p * 100)}% chance of keeping each point`);
  $('#probability').style.background = `linear-gradient(to right, #7b975b ${p * 100}%, #dce4cd ${p * 100}%)`;
  $('#exact-value').innerHTML = `${(exact * 100).toFixed(1)}<span>%</span>`;
  const x = 10 + p * 220;
  const y = 88 - exact * 80;
  $('#chart-point').setAttribute('cx', x);
  $('#chart-point').setAttribute('cy', y);
  $('#chart-guide').setAttribute('d', `M${x} 88V${y}`);
}

function drawChart() {
  const points = Array.from({ length: 101 }, (_, index) => `${10 + index * 2.2},${88 - binomialTail(8, 4, index / 100) * 80}`);
  $('#chart-line').setAttribute('d', `M${points.join('L')}`);
  $('#chart-area').setAttribute('d', `M10,88L${points.join('L')}L230,88Z`);
}

$$('[data-language]').forEach(button => button.addEventListener('click', () => {
  language = button.dataset.language;
  try { localStorage.setItem('reflexive-language', language); } catch { /* The UI still works without storage. */ }
  applyLanguage();
}));
$$('[data-node]').forEach(button => button.addEventListener('click', () => { selectedNode = button.dataset.node; renderNode(); }));
$$('[data-mode]').forEach(button => button.addEventListener('click', () => { mode = button.dataset.mode; renderNode(); }));
$$('[data-filter]').forEach(button => button.addEventListener('click', () => { activeFilter = button.dataset.filter; renderResults(); }));
$$('[data-filter-link]').forEach(link => link.addEventListener('click', () => { activeFilter = link.dataset.filterLink; $('#search').value = ''; renderResults(); }));
$('#search').addEventListener('input', renderResults);
$('#probability').addEventListener('input', renderExperiment);
$('#reroll').addEventListener('click', () => { samples = makeSamples(); renderExperiment(); });
$('#result-grid').addEventListener('click', (event) => {
  const button = event.target.closest('[data-result]');
  if (!button) return;
  openResult = results.find(result => result.id === button.dataset.result);
  renderDialog(openResult);
  $('#result-dialog').showModal();
  document.body.style.overflow = 'hidden';
});
$('#dialog-close').addEventListener('click', () => $('#result-dialog').close());
$('#result-dialog').addEventListener('click', (event) => {
  if (event.target.closest('#dialog-map')) {
    const id = openResult.id;
    $('#result-dialog').close();
    blueprint.openProject(id);
  }
  if (event.target === $('#result-dialog')) {
    const rect = $('#result-dialog').getBoundingClientRect();
    if (event.clientX < rect.left || event.clientX > rect.right || event.clientY < rect.top || event.clientY > rect.bottom) $('#result-dialog').close();
  }
});
$('#result-dialog').addEventListener('close', () => { openResult = null; document.body.style.overflow = document.querySelector('dialog[open]') ? 'hidden' : ''; });

const sourceReader = createSourceReader({ getLanguage: () => language });
const blueprint = createBlueprint({ getLanguage: () => language, showResult: id => {
  openResult = results.find(result => result.id === id);
  renderDialog(openResult);
  $('#result-dialog').showModal();
  document.body.style.overflow = 'hidden';
} });

drawChart();
applyLanguage();
