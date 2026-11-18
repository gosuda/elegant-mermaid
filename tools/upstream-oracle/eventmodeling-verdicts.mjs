#!/usr/bin/env node
import { readFileSync, writeFileSync } from 'node:fs';
import { JSDOM } from 'jsdom';

const { window } = new JSDOM('');
for (const [name, value] of [['window', window], ['document', window.document], ['Option', window.Option]]) {
  Object.defineProperty(globalThis, name, { value, writable: true, configurable: true });
}
const { default: mermaid } = await import('mermaid');
mermaid.initialize({ startOnLoad: false, securityLevel: 'loose' });

const path = process.argv[2];
const cases = JSON.parse(readFileSync(path, 'utf8'));
for (const entry of cases) {
  try {
    await mermaid.parse(entry.source);
    entry.accept = true;
  } catch {
    entry.accept = false;
  }
}
writeFileSync(path, `${JSON.stringify(cases, null, 1)}\n`);
