import { messages, results, nodes as introductions, sourceRoot } from './data.js';
import { indexProject, visibleDeclarations, layoutDeclarations } from './blueprint-graph.js';

const escape = value => String(value).replace(/[&<>"']/g, char => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' })[char]);
const kindGroup = node => node.kind === 'theorem' ? 'theorem' : node.kind === 'lemma' ? 'lemma' : 'definition';
const shorten = (text, limit) => text.length > limit ? text.slice(0, limit - 1) + '…' : text;

export function createBlueprint({ getLanguage, showResult }) {
  const $ = selector => document.querySelector(selector);
  const t = key => messages[key]?.[getLanguage() === 'zh' ? 1 : 0] ?? key;
  const local = value => typeof value === 'string' ? value : value[getLanguage()];
  const kindLabel = node => t({ theorem: 'bpTheorem', lemma: 'bpLemma', definition: 'bpDefinition' }[kindGroup(node)]);
  const svg = $('#bp-graph');
  const input = $('#bp-search');
  const menu = $('#bp-search-menu');
  let projects = [], project, selected, layout, scope = 'neighbors';
  let searchMatches = [], searchActive = -1;
  let view = { x: 0, y: 0, scale: 1 };
  let drag = null, failed = false;

  function renderOptions() {
    $('#bp-collection').innerHTML = projects.map(item => `<option value="${item.id}">${escape(local(results.find(result => result.id === item.id).title))}</option>`).join('');
    $('#bp-collection').value = project.id;
  }

  function setProject(id) {
    project = projects.find(item => item.id === id);
    selected = project.defaultNode;
    input.value = '';
    closeSearch();
    renderGraph();
    renderInspector();
  }

  function selectDeclaration(id, { focus = false, center = false } = {}) {
    if (!project?.byId.has(id)) return;
    selected = id;
    renderGraph(scope !== 'all');
    renderInspector();
    if (center && scope === 'all') centerSelected();
    if (focus) [...$('#bp-nodes').children].find(element => element.dataset.bpNode === selected)?.focus({ preventScroll: true });
  }

  function renderGraph(resetView = true) {
    const visible = visibleDeclarations(project, selected, scope);
    layout = layoutDeclarations(visible);
    const parents = new Set(project.byId.get(selected).dependsOn);
    const children = new Set(project.usedBy.get(selected));
    $('#bp-edges').innerHTML = layout.edges.map(edge => {
      const from = layout.positions.get(edge.from), to = layout.positions.get(edge.to);
      const x1 = from.x + layout.nodeWidth, y1 = from.y + layout.nodeHeight / 2;
      const x2 = to.x, y2 = to.y + layout.nodeHeight / 2;
      const bend = Math.max(35, (x2 - x1) / 2);
      const active = edge.from === selected || edge.to === selected;
      return `<path class="bp-edge ${active ? 'is-active' : ''}" d="M${x1},${y1}C${x1 + bend},${y1} ${x2 - bend},${y2} ${x2},${y2}"/>`;
    }).join('');
    $('#bp-nodes').innerHTML = visible.map(node => {
      const { x, y } = layout.positions.get(node.id);
      const isSelected = selected === node.id;
      const related = parents.has(node.id) || children.has(node.id);
      return `<g class="bp-node bp-kind-${kindGroup(node)} ${isSelected ? 'is-selected' : ''} ${related ? 'is-related' : ''}" transform="translate(${x},${y})" role="button" tabindex="0" aria-label="${escape(`${kindLabel(node)}: ${node.name}`)}" aria-pressed="${isSelected}" data-bp-node="${escape(node.id)}"><title>${escape(node.name)}</title><rect width="${layout.nodeWidth}" height="${layout.nodeHeight}" rx="7"/><text class="bp-node-meta" x="14" y="19">${escape(`${kindLabel(node)} · ${shorten(node.module.split('.').at(-1), 21)}`)}</text><text class="bp-node-label" x="14" y="41">${escape(shorten(node.shortName.replaceAll('_', ' '), 27))}</text></g>`;
    }).join('');
    $('#bp-graph-summary').textContent = getLanguage() === 'zh'
      ? `${visible.length} / ${project.nodes.length} 个声明 · ${layout.edges.length} 条引用`
      : `${visible.length} / ${project.nodes.length} declarations · ${layout.edges.length} references`;
    document.querySelectorAll('[data-bp-scope]').forEach(button => button.setAttribute('aria-pressed', String(button.dataset.bpScope === scope)));
    if (resetView) fit();
  }

  function referenceList(ids, emptyKey) {
    if (!ids.length) return `<p class="bp-no-references">${t(emptyKey)}</p>`;
    const buttons = list => `<div class="bp-reference-list">${list.map(id => `<button type="button" data-bp-reference="${escape(id)}" title="${escape(project.byId.get(id).name)}">${escape(project.byId.get(id).shortName)}</button>`).join('')}</div>`;
    return buttons(ids.slice(0, 6)) + (ids.length > 6 ? `<details class="bp-more"><summary>${t('bpMore')} (${ids.length - 6})</summary>${buttons(ids.slice(6))}</details>` : '');
  }

  function renderInspector() {
    const node = project.byId.get(selected);
    const collection = results.find(result => result.id === project.id);
    const introduction = Object.values(introductions).find(item => item.code.split('\n').includes(node.name));
    let explanation;
    if (introduction) explanation = `<h4>${escape(local(introduction.title))}</h4><p>${escape(local(introduction.description))}</p>`;
    else if (selected === project.defaultNode) explanation = `<p>${escape(local(collection.summary))}</p>`;
    else explanation = `<p>${t('bpNoExplanation')}</p>`;
    const auditLink = node.auditSource ? `<a href="${escape(sourceRoot + node.auditSource)}" target="_blank" rel="noopener noreferrer">${t('bpAudit')}</a>` : '';
    $('#bp-inspector').setAttribute('aria-label', `${t('bpSelected')}: ${node.name}`);
    $('#bp-inspector').innerHTML = `<div class="bp-inspector-header"><span class="bp-inspector-eyebrow">${t('bpSelected')}</span><span class="bp-kind-badge">${escape(node.kind)}</span></div>
      <h3 id="bp-selected-name">${escape(node.name)}</h3><p class="bp-module">${escape(node.module)} · ${escape(node.source.split('/').at(-1))}:${node.line}</p>
      <div class="bp-explanation">${explanation}</div>
      <section class="bp-inspector-section"><h4>${t('bpStatement')}</h4><pre id="bp-statement"><code>${escape(node.statement)}</code></pre></section>
      ${node.documentation ? `<section class="bp-inspector-section"><h4>${t('bpOriginalDoc')}</h4><p class="bp-source-doc">${escape(node.documentation)}</p></section>` : ''}
      <div class="bp-links"><a id="bp-source" href="${escape(sourceRoot + node.source)}#L${node.line}" data-lean-source="${escape(node.source)}" data-lean-line="${node.line}" data-lean-length="${node.statement.split('\n').length}" aria-haspopup="dialog">${t('viewLean')} ↗</a>${auditLink}<a href="${escape(sourceRoot.replace('/blob/', '/tree/') + collection.path)}verification/" target="_blank" rel="noopener noreferrer">${t('bpVerification')}</a></div>
      ${!node.auditSource ? `<p class="bp-audit-note">${t('bpNoAudit')}</p>` : ''}
      <section class="bp-inspector-section"><h4>${t('bpDependencies')} (${node.dependsOn.length})</h4>${referenceList(node.dependsOn, 'bpNoDependencies')}</section>
      <section class="bp-inspector-section"><h4>${t('bpDependents')} (${project.usedBy.get(selected).length})</h4>${referenceList(project.usedBy.get(selected), 'bpNoDependents')}</section>
      <button class="button button-secondary bp-result-history" type="button" data-bp-result="${project.id}">${t('historyLink')} ↗</button>`;
    $('#bp-inspector').scrollTop = 0;
  }

  function updateView() {
    $('#bp-scene').setAttribute('transform', `translate(${view.x},${view.y}) scale(${view.scale})`);
    $('#bp-zoom-value').value = `${Math.round(view.scale * 100)}%`;
  }

  function fit() {
    if (!layout) return;
    const { width, height } = svg.getBoundingClientRect();
    if (!width || !height) return;
    const scale = Math.min((width - 32) / layout.width, (height - 32) / layout.height, 1.15);
    view = { scale, x: (width - layout.width * scale) / 2, y: (height - layout.height * scale) / 2 };
    updateView();
  }

  function zoom(factor, cx, cy) {
    if (!layout) return;
    const rect = svg.getBoundingClientRect();
    const x = cx ?? rect.width / 2, y = cy ?? rect.height / 2;
    const scale = Math.max(.025, Math.min(3.5, view.scale * factor));
    view.x = x - (x - view.x) * scale / view.scale;
    view.y = y - (y - view.y) * scale / view.scale;
    view.scale = scale;
    updateView();
  }

  function centerSelected() {
    const position = layout.positions.get(selected);
    const { width, height } = svg.getBoundingClientRect();
    view.scale = Math.max(.8, view.scale);
    view.x = width / 2 - (position.x + layout.nodeWidth / 2) * view.scale;
    view.y = height / 2 - (position.y + layout.nodeHeight / 2) * view.scale;
    updateView();
  }

  function openSearch() {
    if (!project) return;
    const query = input.value.toLocaleLowerCase().trim();
    const matches = project.nodes.filter(node => !query || [node.name, node.module, node.documentation].join(' ').toLocaleLowerCase().includes(query));
    matches.sort((a, b) => {
      const score = node => node.id === project.defaultNode && !query ? 0 : node.shortName.toLocaleLowerCase() === query ? 0 : node.kind === 'theorem' ? 1 : node.kind === 'lemma' ? 2 : 3;
      return score(a) - score(b) || a.name.localeCompare(b.name);
    });
    searchMatches = matches.slice(0, 30);
    searchActive = -1;
    input.removeAttribute('aria-activedescendant');
    $('#bp-search-results').innerHTML = searchMatches.length ? searchMatches.map((node, index) => `<button type="button" class="bp-search-result" role="option" tabindex="-1" aria-selected="false" id="bp-search-option-${index}" data-bp-search-index="${index}"><strong>${escape(node.shortName)}</strong><span>${escape(`${kindLabel(node)} · ${node.module}`)}</span></button>`).join('') : `<p class="bp-search-empty">${t('bpNoMatches')}</p>`;
    menu.hidden = false;
    input.setAttribute('aria-expanded', 'true');
  }

  function closeSearch() {
    menu.hidden = true;
    input.setAttribute('aria-expanded', 'false');
    input.removeAttribute('aria-activedescendant');
    searchActive = -1;
  }

  function chooseSearch(index) {
    const node = searchMatches[index];
    if (!node) return;
    input.value = node.shortName;
    closeSearch();
    selectDeclaration(node.id, { center: true });
    input.focus({ preventScroll: true });
  }

  input.addEventListener('focus', openSearch);
  input.addEventListener('input', openSearch);
  input.addEventListener('keydown', event => {
    if (event.key === 'Escape') { closeSearch(); event.stopPropagation(); return; }
    if (event.key === 'Enter' && !menu.hidden) { event.preventDefault(); chooseSearch(Math.max(0, searchActive)); return; }
    if (!['ArrowDown', 'ArrowUp'].includes(event.key)) return;
    event.preventDefault();
    if (menu.hidden) openSearch();
    if (!searchMatches.length) return;
    searchActive = (searchActive + (event.key === 'ArrowDown' ? 1 : -1) + searchMatches.length) % searchMatches.length;
    [...$('#bp-search-results').children].forEach((element, index) => element.setAttribute('aria-selected', String(index === searchActive)));
    const option = $(`#bp-search-option-${searchActive}`);
    input.setAttribute('aria-activedescendant', option.id);
    option.scrollIntoView({ block: 'nearest' });
  });
  menu.addEventListener('pointerdown', event => event.preventDefault());
  menu.addEventListener('click', event => {
    const button = event.target.closest('[data-bp-search-index]');
    if (button) chooseSearch(Number(button.dataset.bpSearchIndex));
  });
  document.addEventListener('pointerdown', event => { if (!event.target.closest('.bp-search-wrap')) closeSearch(); });
  document.addEventListener('focusin', event => { if (!event.target.closest('.bp-search-wrap')) closeSearch(); });
  $('#bp-collection').addEventListener('change', event => setProject(event.target.value));
  document.querySelectorAll('[data-bp-scope]').forEach(button => button.addEventListener('click', () => {
    if (!project) return;
    scope = button.dataset.bpScope;
    renderGraph();
  }));
  $('#bp-home').addEventListener('click', () => { if (project) selectDeclaration(project.defaultNode, { center: true }); });
  $('#bp-inspector').addEventListener('click', event => {
    const reference = event.target.closest('[data-bp-reference]');
    if (reference) selectDeclaration(reference.dataset.bpReference, { center: true });
    const result = event.target.closest('[data-bp-result]');
    if (result) showResult(result.dataset.bpResult);
  });
  $('#bp-zoom-in').addEventListener('click', () => zoom(1.3));
  $('#bp-zoom-out').addEventListener('click', () => zoom(1 / 1.3));
  $('#bp-fit').addEventListener('click', fit);
  svg.addEventListener('wheel', event => {
    if (!layout) return;
    event.preventDefault();
    const rect = svg.getBoundingClientRect();
    zoom(Math.exp(-Math.max(-100, Math.min(100, event.deltaY)) * .006), event.clientX - rect.left, event.clientY - rect.top);
  }, { passive: false });
  svg.addEventListener('pointerdown', event => {
    if (!layout || event.button !== 0 || drag) return;
    drag = { pointerId: event.pointerId, x: event.clientX, y: event.clientY, startX: view.x, startY: view.y, node: event.target.closest('[data-bp-node]')?.dataset.bpNode, moved: false };
    svg.setPointerCapture(event.pointerId);
  });
  svg.addEventListener('pointermove', event => {
    if (!drag || drag.pointerId !== event.pointerId) return;
    const dx = event.clientX - drag.x, dy = event.clientY - drag.y;
    if (Math.abs(dx) + Math.abs(dy) > 5) drag.moved = true;
    if (!drag.moved) return;
    svg.classList.add('is-dragging');
    view.x = drag.startX + dx; view.y = drag.startY + dy;
    updateView();
  });
  svg.addEventListener('pointerup', event => {
    if (!drag || drag.pointerId !== event.pointerId) return;
    const last = drag;
    drag = null;
    svg.classList.remove('is-dragging');
    if (svg.hasPointerCapture(event.pointerId)) svg.releasePointerCapture(event.pointerId);
    if (!last.moved && last.node) selectDeclaration(last.node, { focus: true });
  });
  const cancelDrag = () => { drag = null; svg.classList.remove('is-dragging'); };
  svg.addEventListener('pointercancel', cancelDrag);
  svg.addEventListener('lostpointercapture', cancelDrag);
  svg.addEventListener('keydown', event => {
    const node = event.target.closest('[data-bp-node]');
    if (node && ['Enter', ' '].includes(event.key)) {
      event.preventDefault(); selectDeclaration(node.dataset.bpNode, { focus: true }); return;
    }
    if (event.key === '+' || event.key === '=') { event.preventDefault(); zoom(1.3); }
    if (event.key === '-') { event.preventDefault(); zoom(1 / 1.3); }
    if (event.key === '0') { event.preventDefault(); fit(); }
    const delta = { ArrowLeft: [40, 0], ArrowRight: [-40, 0], ArrowUp: [0, 40], ArrowDown: [0, -40] }[event.key];
    if (delta && layout) { event.preventDefault(); view.x += delta[0]; view.y += delta[1]; updateView(); }
  });
  let observedWidth = 0;
  new ResizeObserver(entries => {
    const width = entries[0].contentRect.width;
    if (Math.abs(width - observedWidth) > 1) { observedWidth = width; fit(); }
  }).observe(svg);

  fetch(new URL('./blueprint-data.json', import.meta.url)).then(response => {
    if (!response.ok) throw new Error(`Blueprint HTTP ${response.status}`);
    return response.json();
  }).then(data => {
    projects = data.projects.map(indexProject);
    setProject('smallness');
    renderOptions();
    $('#bp-collection').disabled = false;
    input.disabled = false;
    $('#blueprint-workbench').setAttribute('aria-busy', 'false');
  }).catch(error => {
    failed = true;
    $('#blueprint-workbench').setAttribute('aria-busy', 'false');
    $('#bp-graph-summary').textContent = t('bpError');
    console.error('Blueprint load failed:', error);
  });

  return {
    setLanguage() {
      if (failed) { $('#bp-graph-summary').textContent = t('bpError'); return; }
      if (!project) return;
      renderOptions(); renderGraph(false); renderInspector();
      if (!menu.hidden) openSearch();
    },
    openProject(id) {
      if (projects.length) { scope = 'neighbors'; setProject(id); renderOptions(); }
      $('#blueprint').scrollIntoView({ behavior: matchMedia('(prefers-reduced-motion: reduce)').matches ? 'instant' : 'smooth' });
    },
  };
}
