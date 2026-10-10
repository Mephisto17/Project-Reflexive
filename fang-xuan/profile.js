const chinese = {
  skip:'跳至正文',navResearch:'研究方向',navPapers:'论文',navContact:'联系',affiliation:'数学 · 复旦大学',
  position:'AI for Math 方向博士研究生',
  intro:'我目前在复旦大学数学科学学院攻读 AI for Math 方向博士，本科也就读于复旦大学数学科学学院。',
  interests:'我的研究方向是概率论、组合数学与 AI for Math。',viewPapers:'查看我的论文',getInTouch:'联系我',
  school:'数学科学学院',fudan:'复旦大学',researchTitle:'研究方向',probability:'概率论',combinatorics:'组合数学',aiMath:'AI for Math',
  papersTitle:'论文与预印本',papersIntro:'近期研究工作，以及原文和引用信息。',downloadBib:'下载 BibTeX',preprintNote:'以下论文均按 arXiv 预印本列出。',
  september:'2026 年 9 月',august:'2026 年 8 月',historical:'历史参考',preprint:'预印本',and:' 与 ',copyCitation:'复制引用',
  historicalNote:'作者将本预印本保留为历史参考：更新后的 arXiv 摘要说明，后续更强的结果已取代本文的比较界。',
  liSummary:'运用 Chen Li 的方法，回答 Talagrand 提出的另一个问题。',
  khintchineSummary:'精细化 Khintchine 不等式，并改进线性阈值函数一次 Fourier 权重的下界。',
  sourceNote:'题名、作者顺序和预印本状态于 2026 年 10 月 10 日依据 arXiv 核实。',educationTitle:'教育经历',current:'目前',previous:'本科阶段',
  phd:'博士阶段 · AI for Math',undergraduate:'本科阶段',institution:'复旦大学数学科学学院',
  projectLabel:'让数学可以被探索',projectDescription:'探索数学命题、交互式证明关系图与 Lean 形式化。',projectExplore:'探索项目网站',
  contactLabel:'联系方式',contactTitle:'一起交流数学。',backTop:'返回顶部'
};
const nodes = [...document.querySelectorAll('[data-i18n]')];
const english = Object.fromEntries(nodes.map(node => [node.dataset.i18n, node.textContent]));
let language = 'en';
let toastTimeout;
function setLanguage(next) {
  language = next === 'zh' ? 'zh' : 'en';
  document.documentElement.lang = language === 'zh' ? 'zh-Hans' : 'en';
  document.title = language === 'zh' ? '方轩 · Xuan Fang | 复旦大学' : 'Xuan Fang · 方轩 | Fudan University';
  nodes.forEach(node => { node.textContent = language === 'zh' ? (chinese[node.dataset.i18n] || english[node.dataset.i18n]) : english[node.dataset.i18n]; });
  document.querySelectorAll('[data-language]').forEach(button => button.setAttribute('aria-pressed', String(button.dataset.language === language)));
  document.querySelector('nav').setAttribute('aria-label', language === 'zh' ? '主导航' : 'Main navigation');
  document.querySelector('.portrait img').alt = language === 'zh' ? '方轩的照片' : 'Portrait of Xuan Fang';
  document.querySelectorAll('[data-cite]').forEach(button => button.setAttribute('aria-label', (language === 'zh' ? '复制 BibTeX 引用：arXiv ' : 'Copy BibTeX citation: arXiv ') + button.dataset.cite));
  try { localStorage.setItem('xuan-fang-language', language); } catch { /* The page also works without storage. */ }
}
document.querySelectorAll('[data-language]').forEach(button => button.addEventListener('click', () => setLanguage(button.dataset.language)));
try { if (localStorage.getItem('xuan-fang-language') === 'zh') setLanguage('zh'); } catch { /* Keep English as the default. */ }

const paperTitles = {
  '2609.30680':'A Log-Star Comparison Between Expectation Threshold and Fractional Expectation Threshold',
  '2609.18458':'A Note on a Result of Chen Li',
  '2608.27908':'A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions'
};
function citation(id) {
  return `@misc{fang_wang_${id.replace('.', '_')},\n  title = {${paperTitles[id]}},\n  author = {Fang, Xuan and Wang, Tianyu},\n  year = {2026},\n  eprint = {${id}},\n  archivePrefix = {arXiv},\n  url = {https://arxiv.org/abs/${id}}\n}`;
}
function notify(message) {
  const status = document.getElementById('copy-status');
  status.textContent = message;
  status.hidden = false;
  clearTimeout(toastTimeout);
  toastTimeout = setTimeout(() => { status.hidden = true; }, 4500);
}
document.querySelectorAll('[data-cite]').forEach(button => button.addEventListener('click', async () => {
  try {
    await navigator.clipboard.writeText(citation(button.dataset.cite));
    notify(language === 'zh' ? 'BibTeX 引用已复制。' : 'BibTeX citation copied.');
  } catch {
    notify(language === 'zh' ? '无法复制，请使用“下载 BibTeX”链接。' : 'Copy unavailable. Please use the Download BibTeX link.');
  }
}));
