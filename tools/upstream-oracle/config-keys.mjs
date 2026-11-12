import { existsSync, readFileSync, readdirSync } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const repoRoot = fileURLToPath(new URL('../..', import.meta.url));
const schemaPath = '.references/mermaid/packages/mermaid/src/schemas/config.schema.yaml';
const kindsPath = 'spec/data/kinds.json';
const baseDefinition = 'BaseDiagramConfig';
const rowSeparator = '\u0000';
const definitionRef = /^#\/\$defs\/([A-Za-z0-9_]+)$/;
const definitionMention = /#\/\$defs\/([A-Za-z0-9_]+)/g;
const blockKindTable = new Map([['wardley-beta', 'wardley']]);

function compareBytewise(left, right) {
  if (left < right) return -1;
  if (left > right) return 1;
  return 0;
}

function indentOf(line) {
  let count = 0;
  while (count < line.length && line[count] === ' ') count += 1;
  return count;
}

function isSkippable(line) {
  const body = line.trim();
  return body === '' || body.startsWith('#');
}

function stripComment(line) {
  let quote = '';
  for (let index = 0; index < line.length; index += 1) {
    const character = line[index];
    if (quote === "'") {
      if (character === "'") quote = '';
      continue;
    }
    if (quote === '"') {
      if (character === '\\') {
        index += 1;
        continue;
      }
      if (character === '"') quote = '';
      continue;
    }
    if (character === "'" || character === '"') {
      quote = character;
      continue;
    }
    if (character === '#' && (index === 0 || line[index - 1] === ' ' || line[index - 1] === '\t')) {
      return line.slice(0, index);
    }
  }
  return line;
}

function unquote(text) {
  if (text.length < 2) return text;
  const first = text[0];
  const last = text[text.length - 1];
  if (first === "'" && last === "'") return text.slice(1, -1).replaceAll("''", "'");
  if (first === '"' && last === '"') return text.slice(1, -1);
  return text;
}

function bracketDepth(text) {
  let depth = 0;
  let quote = '';
  for (let index = 0; index < text.length; index += 1) {
    const character = text[index];
    if (quote === "'") {
      if (character === "'") quote = '';
      continue;
    }
    if (quote === '"') {
      if (character === '\\') {
        index += 1;
        continue;
      }
      if (character === '"') quote = '';
      continue;
    }
    if (character === "'" || character === '"') {
      quote = character;
      continue;
    }
    if (character === '[' || character === '{') depth += 1;
    if (character === ']' || character === '}') depth -= 1;
  }
  return depth;
}

function splitKey(content) {
  let quote = '';
  for (let index = 0; index < content.length; index += 1) {
    const character = content[index];
    if (quote === "'") {
      if (character === "'") quote = '';
      continue;
    }
    if (quote === '"') {
      if (character === '\\') {
        index += 1;
        continue;
      }
      if (character === '"') quote = '';
      continue;
    }
    if (character === "'" || character === '"') {
      quote = character;
      continue;
    }
    const next = content[index + 1];
    const isSeparator = character === ':' && (next === undefined || next === ' ' || next === '\t');
    if (isSeparator) {
      return { key: unquote(content.slice(0, index).trim()), rest: content.slice(index + 1).trim() };
    }
  }
  return null;
}

function readFlow(state, text) {
  let depth = bracketDepth(text);
  let raw = text;
  while (depth > 0 && state.index < state.lines.length) {
    const line = state.lines[state.index];
    state.index += 1;
    raw += `\n${line.trim()}`;
    depth += bracketDepth(line);
  }
  return new Map([['flow', raw]]);
}

function readSequence(state, indent) {
  const parts = [];
  while (state.index < state.lines.length) {
    const line = state.lines[state.index];
    if (isSkippable(line)) {
      state.index += 1;
      continue;
    }
    if (indentOf(line) < indent) break;
    parts.push(line.slice(indent));
    state.index += 1;
  }
  return new Map([['flow', parts.join('\n')]]);
}

function readBlockScalar(state, indent) {
  while (state.index < state.lines.length) {
    const body = state.lines[state.index];
    if (isSkippable(body)) {
      state.index += 1;
      continue;
    }
    if (indentOf(body) <= indent) break;
    state.index += 1;
  }
  return new Map();
}

function readValue(state, parentIndent) {
  while (state.index < state.lines.length && isSkippable(state.lines[state.index])) state.index += 1;
  if (state.index >= state.lines.length) return new Map();
  const line = state.lines[state.index];
  const indent = indentOf(line);
  const content = line.slice(indent);
  const isSequenceItem = content.startsWith('- ') || content === '-';
  if (indent < parentIndent || (indent === parentIndent && !isSequenceItem)) return new Map();
  if (isSequenceItem) return readSequence(state, indent);
  return readMapping(state, indent);
}

function readInlineValue(state, rest, indent) {
  if (rest.startsWith('|') || rest.startsWith('>')) return readBlockScalar(state, indent);
  if (rest.startsWith('[') || rest.startsWith('{')) return readFlow(state, rest);
  if (rest.startsWith('&') || rest.startsWith('!')) {
    const remainder = rest.replace(/^[&!]\S*/, '').trim();
    return remainder === '' ? readValue(state, indent) : unquote(remainder);
  }
  return unquote(rest);
}

function readMapping(state, indent) {
  const mapping = new Map();
  while (state.index < state.lines.length) {
    const line = state.lines[state.index];
    if (isSkippable(line)) {
      state.index += 1;
      continue;
    }
    const lineIndent = indentOf(line);
    if (lineIndent < indent) break;
    const content = line.slice(lineIndent);
    const pair = lineIndent === indent ? splitKey(content) : null;
    if (pair === null) {
      state.index += 1;
      if (content.startsWith('[') || content.startsWith('{')) readFlow(state, content);
      continue;
    }
    state.index += 1;
    mapping.set(pair.key, pair.rest === '' ? readValue(state, indent) : readInlineValue(state, pair.rest, indent));
  }
  return mapping;
}

function parseYaml(text) {
  const lines = text.split('\n').map((line) => stripComment(line.replace(/\r$/, '')));
  const state = { lines, index: 0 };
  while (state.index < lines.length && isSkippable(lines[state.index])) state.index += 1;
  if (state.index >= lines.length) return new Map();
  return readMapping(state, indentOf(lines[state.index]));
}

function textOf(value) {
  if (typeof value === 'string') return value;
  return value instanceof Map && typeof value.get('flow') === 'string' ? value.get('flow') : '';
}

function mentionedDefinitions(value) {
  const names = [];
  for (const match of textOf(value).matchAll(definitionMention)) names.push(match[1]);
  return names;
}

function composesBase(name, definitions) {
  const reached = new Set();
  const pending = [name];
  while (pending.length > 0) {
    const current = pending.pop();
    if (reached.has(current)) continue;
    reached.add(current);
    const definition = definitions.get(current);
    if (!(definition instanceof Map)) continue;
    for (const composed of mentionedDefinitions(definition.get('allOf'))) pending.push(composed);
  }
  return reached.has(baseDefinition);
}

function composedKeys(schema, definitions) {
  const keys = new Set();
  const pending = [schema];
  const rootRef = textOf(schema.get('$ref'));
  const named = definitionRef.exec(rootRef);
  if (named !== null) pending.push(definitions.get(named[1]));
  while (pending.length > 0) {
    const current = pending.pop();
    if (!(current instanceof Map)) continue;
    for (const name of mentionedDefinitions(current.get('allOf'))) pending.push(definitions.get(name));
    const own = current.get('properties');
    if (own instanceof Map) for (const key of own.keys()) keys.add(key);
  }
  return [...keys].sort(compareBytewise);
}

function diagramBlockOf(value, definitions) {
  const ref = textOf(value.get('$ref'));
  const named = definitionRef.exec(ref);
  if (named === null) return null;
  if (!composesBase(named[1], definitions)) return null;
  return { definition: named[1], keys: composedKeys(value, definitions) };
}

function loadKinds() {
  const file = path.join(repoRoot, kindsPath);
  if (!existsSync(file)) return [];
  const parsed = JSON.parse(readFileSync(file, 'utf8'));
  return Array.isArray(parsed) ? parsed : [];
}

function kindNames(kind) {
  const names = [];
  if (typeof kind.id === 'string') names.push(kind.id);
  if (Array.isArray(kind.aliases)) for (const alias of kind.aliases) if (typeof alias === 'string') names.push(alias);
  return names;
}

function kindForBlock(blockName, kinds) {
  const lowered = blockName.toLowerCase();
  const matches = new Set();
  for (const kind of kinds) {
    if (typeof kind.id !== 'string') continue;
    if (kindNames(kind).some((name) => name.toLowerCase() === lowered)) matches.add(kind.id);
  }
  if (matches.size === 1) return { kind: [...matches][0], reason: '' };
  if (matches.size > 1) return { kind: null, reason: `ambiguous: ${[...matches].sort(compareBytewise).join(', ')}` };
  const overridden = blockKindTable.get(lowered);
  if (overridden !== undefined) return { kind: overridden, reason: 'explicit table' };
  return { kind: null, reason: 'no kind id, alias, or table entry' };
}

function readRows(directory) {
  const rows = [];
  if (!existsSync(directory)) return rows;
  for (const entry of readdirSync(directory).sort(compareBytewise)) {
    if (!entry.endsWith('.json')) continue;
    const parsed = JSON.parse(readFileSync(path.join(directory, entry), 'utf8'));
    if (!Array.isArray(parsed)) continue;
    for (const row of parsed) {
      if (row === null || typeof row !== 'object' || typeof row.key !== 'string') continue;
      rows.push({ kind: typeof row.kind === 'string' ? row.kind : '', key: row.key });
    }
  }
  return rows;
}

function schemaInventory() {
  const schema = parseYaml(readFileSync(path.join(repoRoot, schemaPath), 'utf8'));
  const definitions = schema.get('$defs');
  const properties = schema.get('properties');
  if (!(definitions instanceof Map)) throw new Error(`no $defs mapping in ${schemaPath}`);
  if (!(properties instanceof Map)) throw new Error(`no properties mapping in ${schemaPath}`);
  const entries = [];
  for (const [topLevel, value] of properties) {
    entries.push({ topLevel, block: value instanceof Map ? diagramBlockOf(value, definitions) : null });
  }
  return entries;
}

function reportInventory(entries) {
  const kinds = loadKinds();
  const paths = new Set();
  const blocks = [];
  for (const entry of entries) {
    paths.add(entry.topLevel);
    if (entry.block === null) continue;
    for (const key of entry.block.keys) paths.add(`${entry.topLevel}.${key}`);
    blocks.push(entry);
  }
  for (const item of [...paths].sort(compareBytewise)) process.stdout.write(`${item}\n`);
  process.stderr.write(`top-level keys: ${entries.length}\n`);
  process.stderr.write(`blocks: ${blocks.length}\n`);
  for (const [blockName, kind] of [...blockKindTable].sort((left, right) => compareBytewise(left[0], right[0]))) {
    process.stderr.write(`table ${blockName} -> ${kind}\n`);
  }
  for (const entry of blocks) {
    const resolved = kindForBlock(entry.topLevel, kinds);
    const source = resolved.kind === null ? `unmapped (${resolved.reason})` : resolved.kind;
    process.stderr.write(`block ${entry.topLevel} (${entry.block.definition}) -> ${source}: ${entry.block.keys.length}\n`);
  }
}

function reportMissing(entries, directory) {
  const kinds = loadKinds();
  const commonRows = new Set();
  const kindRows = new Set();
  for (const row of readRows(directory)) {
    if (row.kind === '') {
      commonRows.add(row.key);
      continue;
    }
    kindRows.add(`${row.kind}${rowSeparator}${row.key}`);
  }
  const missing = new Set();
  const unmapped = [];
  for (const entry of entries) {
    if (!commonRows.has(entry.topLevel)) missing.add(entry.topLevel);
    if (entry.block === null) continue;
    const resolved = kindForBlock(entry.topLevel, kinds);
    if (resolved.kind === null) {
      unmapped.push(`${entry.topLevel} (${resolved.reason})`);
      continue;
    }
    for (const key of entry.block.keys) {
      if (!kindRows.has(`${resolved.kind}${rowSeparator}${key}`)) missing.add(`${entry.topLevel}.${key}`);
    }
  }
  if (unmapped.length > 0) {
    process.stderr.write(`unmapped config blocks: ${unmapped.join('; ')}\n`);
    return 2;
  }
  for (const item of [...missing].sort(compareBytewise)) process.stdout.write(`${item}\n`);
  process.stderr.write(`missing keys: ${missing.size}\n`);
  return missing.size === 0 ? 0 : 1;
}

function main(argv) {
  const entries = schemaInventory();
  if (argv.length === 0) {
    reportInventory(entries);
    return 0;
  }
  if (argv.length === 2 && argv[0] === '--missing') return reportMissing(entries, path.resolve(argv[1]));
  process.stderr.write('usage: config-keys.mjs [--missing DIR]\n');
  return 2;
}

process.exitCode = main(process.argv.slice(2));
