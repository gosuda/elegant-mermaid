import { JSDOM } from 'jsdom';
const { window } = new JSDOM('');
for (const [name, value] of [['window', window], ['document', window.document], ['Option', window.Option]]) {
  Object.defineProperty(globalThis, name, { value, writable: true, configurable: true });
}
const { default: mermaid } = await import('mermaid');
mermaid.initialize({ startOnLoad: false, securityLevel: 'loose' });
const cases = [
  ['total entity', 'erDiagram\n  total ||--o{ x : y\n'],
  ['manythings entity', 'erDiagram\n  manythings ||--o{ x : y\n'],
  ['onlyone entity', 'erDiagram\n  onlyone ||--o{ x : y\n'],
  ['zerofill entity', 'erDiagram\n  zerofill ||--o{ x : y\n'],
  ['onething entity', 'erDiagram\n  onething ||--o{ x : y\n'],
  ['u entity line', 'erDiagram\n  u ||--|| ORDER : places\n  PROJECT u--o{ TEAM_MEMBER : "parent"\n'],
  ['u dot', 'erDiagram\n  A u. B : x\n'],
];
for (const [name, src] of cases) {
  let ok = false, msg = '';
  try { await mermaid.parse(src); ok = true; } catch (e) { msg = String(e.message ?? e).slice(0, 100).replace(/\n/g, ' | '); }
  console.log(`${ok ? 'ACCEPT' : 'REJECT'} ${name}${ok ? '' : ' :: ' + msg}`);
}
