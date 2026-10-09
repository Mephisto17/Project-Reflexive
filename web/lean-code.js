// This lexer only adds color. It never evaluates, rewrites, or verifies Lean.
const keywords = new Set('import open namespace end section variable variables theorem lemma def abbrev instance structure inductive class noncomputable private protected unsafe mutual where by at exact apply refine simpa simp rw rfl intro intros have let show from fun forall if then else match with sorry axiom deriving do obtain constructor cases rcases calc'.split(' '));
const escape = value => value.replace(/[&<>"']/g, char => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' })[char]);

export function leanTokens(source) {
  const pattern = /\/-|--|"(?:\\[\s\S]|[^"\\])*"|[A-Za-z_][A-Za-z0-9_']*|\b\d+(?:\.\d+)?\b/g;
  const tokens = [];
  let previous = 0, match;
  while ((match = pattern.exec(source))) {
    if (match.index > previous) tokens.push({ text: source.slice(previous, match.index), kind: '' });
    const start = match.index;
    let end = pattern.lastIndex, kind = '';
    if (match[0] === '/-') {
      let depth = 1;
      while (end < source.length && depth) {
        const pair = source.slice(end, end + 2);
        if (pair === '/-') { depth++; end += 2; }
        else if (pair === '-/') { depth--; end += 2; }
        else end++;
      }
      kind = 'comment';
    } else if (match[0] === '--') {
      end = source.indexOf('\n', end);
      if (end < 0) end = source.length;
      kind = 'comment';
    } else if (match[0].startsWith('"')) kind = 'string';
    else if (keywords.has(match[0])) kind = 'keyword';
    else if (/^\d/.test(match[0])) kind = 'number';
    tokens.push({ text: source.slice(start, end), kind });
    previous = end;
    pattern.lastIndex = end;
  }
  if (previous < source.length) tokens.push({ text: source.slice(previous), kind: '' });
  return tokens;
}

export function highlightedLeanLines(source) {
  const lines = [''];
  for (const token of leanTokens(source)) {
    token.text.split('\n').forEach((part, index) => {
      if (index) lines.push('');
      const content = escape(part);
      lines[lines.length - 1] += token.kind && content ? `<span class="lean-token-${token.kind}">${content}</span>` : content;
    });
  }
  return lines;
}
