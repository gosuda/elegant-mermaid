#!/usr/bin/env node
import { readFileSync, writeFileSync } from 'node:fs';
import { JSDOM } from 'jsdom';

const { window } = new JSDOM('');
for (const [name, value] of [['window', window], ['document', window.document], ['Option', window.Option]]) {
  Object.defineProperty(globalThis, name, { value, writable: true, configurable: true });
}
window.SVGElement.prototype.getBBox = () => ({ x: 0, y: 0, width: 120, height: 24 });
const { default: mermaid } = await import('mermaid');
mermaid.initialize({ startOnLoad: false, securityLevel: 'loose' });

for (const path of process.argv.slice(2)) {
  const diagram = await mermaid.mermaidAPI.getDiagramFromText(readFileSync(path, 'utf8'));
  const state = diagram.db.getState();
  const summary = {
    boxes: state.boxes.map((box) => [box.frame.name, box.swimlane.index]),
    lanes: state.sortedSwimlanesArray.map((lane) => [lane.index, lane.label]),
    relations: state.relations.map((relation) => [relation.sourceBox.frame.name, relation.targetBox.frame.name]),
  };
  writeFileSync(path.replace(/\.mmd$/, '.state.json'), `${JSON.stringify(summary)}\n`);
}
