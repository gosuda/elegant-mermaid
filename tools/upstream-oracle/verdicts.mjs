#!/usr/bin/env node
import { readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join, relative, sep } from 'node:path';
import { fileURLToPath } from 'node:url';

const REPOSITORY_ROOT = fileURLToPath(new URL('../..', import.meta.url));
const CORPUS_DIRECTORY = join(REPOSITORY_ROOT, 'corpus');
const REGISTRY_PATH = join(REPOSITORY_ROOT, 'spec', 'data', 'kinds.json');
const SKIPPED_DIRECTORIES = new Set(['.cache', '_out-of-scope']);
const PSEUDO_DIAGRAM_TYPES = new Set(['error', '---']);

function fail(message) {
  process.stderr.write(`${message}\n`);
  process.exit(1);
}

function compareBytes(left, right) {
  return Buffer.compare(Buffer.from(left, 'utf8'), Buffer.from(right, 'utf8'));
}

function corpusFiles() {
  const files = [];
  const visit = (directory) => {
    for (const entry of readdirSync(directory, { withFileTypes: true })) {
      const path = join(directory, entry.name);
      if (entry.isDirectory()) {
        if (!SKIPPED_DIRECTORIES.has(entry.name)) visit(path);
      } else if (entry.isFile() && entry.name.endsWith('.mmd')) {
        files.push({ path, key: relative(REPOSITORY_ROOT, path).split(sep).join('/') });
      }
    }
  };
  visit(CORPUS_DIRECTORY);
  return files.sort((left, right) => compareBytes(left.key, right.key));
}

function loadKindIndex() {
  const index = new Map();
  for (const kind of JSON.parse(readFileSync(REGISTRY_PATH, 'utf8'))) {
    index.set(kind.id, kind.id);
    for (const alias of kind.aliases) index.set(alias, kind.id);
  }
  return index;
}

async function loadMermaid() {
  if (!globalThis.window) {
    const { JSDOM } = await import('jsdom');
    const { window } = new JSDOM('');
    const globals = [
      ['window', window],
      ['document', window.document],
      ['Option', window.Option],
    ];
    for (const [name, value] of globals) {
      Object.defineProperty(globalThis, name, { value, writable: true, configurable: true });
    }
  }
  const { default: mermaid } = await import('mermaid');
  mermaid.initialize({ startOnLoad: false, securityLevel: 'loose' });
  return mermaid;
}

function firstLine(error) {
  const text = error !== null && typeof error === 'object' && typeof error.message === 'string' ? error.message : String(error);
  return /^[^\r\n]*/.exec(text)[0];
}

function detectDiagramType(mermaid, text) {
  try {
    return mermaid.detectType(text);
  } catch {
    return null;
  }
}

async function verdictFor(mermaid, source, kindOf) {
  let diagramType = null;
  let message = '';
  let accept = true;
  try {
    ({ diagramType } = await mermaid.parse(source));
    accept = !PSEUDO_DIAGRAM_TYPES.has(diagramType);
  } catch (error) {
    accept = false;
    message = firstLine(error);
    diagramType = detectDiagramType(mermaid, source);
  }
  if (PSEUDO_DIAGRAM_TYPES.has(diagramType)) diagramType = null;
  if (diagramType !== null && !kindOf.has(diagramType)) fail(`unknown upstream diagram type ${diagramType}`);
  return { accept, kind: diagramType === null ? null : kindOf.get(diagramType), message };
}

async function main() {
  const entries = corpusFiles();
  const kindOf = loadKindIndex();
  const mermaid = await loadMermaid();
  const verdicts = new Map();
  for (const entry of entries) {
    verdicts.set(entry.key, await verdictFor(mermaid, readFileSync(entry.path, 'utf8'), kindOf));
  }
  const ordered = Object.fromEntries(verdicts);
  writeFileSync(join(CORPUS_DIRECTORY, 'verdicts.json'), `${JSON.stringify(ordered, null, 2)}\n`);
}

await main();
