import { closeSync, mkdirSync, mkdtempSync, openSync, readFileSync, writeFileSync, renameSync, rmSync } from 'node:fs';
import { execFile } from 'node:child_process';
import { tmpdir } from 'node:os';
import { promisify } from 'node:util';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import dagre from '@dagrejs/dagre';
import ELK from 'elkjs/lib/elk.bundled.js';

const repoRoot = fileURLToPath(new URL('../..', import.meta.url));
const cacheDir = path.join(repoRoot, 'corpus/.cache/quality');
const unitScale = 64;
const zeroPadding = '[top=0,left=0,bottom=0,right=0]';
const directionToElk = new Map([
  ['TB', 'DOWN'],
  ['BT', 'UP'],
  ['LR', 'RIGHT'],
  ['RL', 'LEFT'],
]);
const elkOptions = {
  'elk.algorithm': 'layered',
  'elk.spacing.nodeNode': '24',
  'elk.layered.spacing.nodeNodeBetweenLayers': '48',
  'elk.spacing.edgeEdge': '12',
  'elk.layered.spacing.edgeEdgeBetweenLayers': '12',
  'elk.layered.spacing.edgeNodeBetweenLayers': '12',
  'elk.padding': zeroPadding,
  'elk.edgeRouting': 'ORTHOGONAL',
  'elk.layered.crossingMinimization.forceNodeModelOrder': 'true',
  'elk.layered.considerModelOrder.strategy': 'NODES_AND_EDGES',
  'elk.layered.nodePlacement.bk.fixedAlignment': 'BALANCED',
  'elk.hierarchyHandling': 'INCLUDE_CHILDREN',
  'elk.edgeLabels.inline': 'true',
  'elk.edgeLabels.placement': 'CENTER',
};
const constants = JSON.parse(readFileSync(path.join(repoRoot, 'spec/data/layout-constants.json'), 'utf8'));
const spacing = (name) => constants.find((entry) => entry.name === name).vector / 64;
const dagreSpacing = { nodesep: spacing('node_gap'), ranksep: spacing('rank_gap'), edgesep: spacing('slot'), marginx: 0, marginy: 0 };
elkOptions['elk.spacing.nodeNode'] = String(dagreSpacing.nodesep);
elkOptions['elk.layered.spacing.nodeNodeBetweenLayers'] = String(dagreSpacing.ranksep);
for (const key of ['elk.spacing.edgeEdge', 'elk.layered.spacing.edgeEdgeBetweenLayers', 'elk.layered.spacing.edgeNodeBetweenLayers']) elkOptions[key] = String(dagreSpacing.edgesep);
const execute = promisify(execFile);
const edgeIdPrefix = '__emd_edge__';
const usage = 'usage: node tools/upstream-oracle/baseline.mjs LISTFILE JOBS | --self-test';

function fail(message) {
  process.stderr.write(`baseline: ${message}\n`);
  process.exitCode = 1;
  throw new Error(message);
}

function roundHalfAway(value) {
  if (!Number.isFinite(value)) fail(`non-finite coordinate ${value}`);
  return value < 0 ? -Math.floor(-value + 0.5) : Math.floor(value + 0.5);
}

function unitsOf(value) {
  return roundHalfAway(unitScale * value);
}

function pxOf(units) {
  return units / unitScale;
}

function floorDiv(left, right) {
  return Math.floor(left / right);
}

function isObject(value) {
  return typeof value === 'object' && value !== null && !Array.isArray(value);
}


function sortedKeys(object) {
  return Object.keys(object).sort((left, right) => (left < right ? -1 : left > right ? 1 : 0));
}

function escapeString(value) {
  return JSON.stringify(value);
}

function writeInteger(value) {
  const number = Number(value);
  if (!Number.isSafeInteger(number)) fail(`invalid integer ${value}`);
  return String(number);
}

function writePoint(point) {
  return `[${writeInteger(point[0])},${writeInteger(point[1])}]`;
}

function writeLimits(value) {
  const limits = isObject(value) ? value : {};
  const nodes = Number.isInteger(limits.max_nodes) ? limits.max_nodes : 2000;
  const edges = Number.isInteger(limits.max_edges) ? limits.max_edges : 5000;
  const bytes = Number.isInteger(limits.max_text_bytes) ? limits.max_text_bytes : 1048576;
  return `{"max_nodes":${writeInteger(nodes)},"max_edges":${writeInteger(edges)},"max_text_bytes":${writeInteger(bytes)}}`;
}

function normalizeOptions(options) {
  const source = isObject(options) ? options : {};
  const head = [];
  head.push(`"profile":${escapeString(typeof source.profile === 'string' ? source.profile : 'vector')}`);
  head.push(`"thoroughness":${writeInteger(Number.isInteger(source.thoroughness) ? source.thoroughness : 3)}`);
  head.push(`"max_width":${writeInteger(Number.isInteger(source.max_width) ? source.max_width : 0)}`);
  head.push(`"direction":${escapeString(typeof source.direction === 'string' ? source.direction : 'TB')}`);
  head.push(`"limits":${writeLimits(source.limits)}`);
  const reserved = new Set(['profile', 'thoroughness', 'max_width', 'direction', 'limits']);
  for (const key of sortedKeys(source)) {
    if (reserved.has(key)) continue;
    head.push(`${escapeString(key)}:${JSON.stringify(source[key])}`);
  }
  return `{${head.join(',')}}`;
}

function writeBox(box) {
  return [
    `"id":${escapeString(box.id)}`,
    `"role":${escapeString(box.role)}`,
    `"x":${writeInteger(box.x)}`,
    `"y":${writeInteger(box.y)}`,
    `"w":${writeInteger(box.w)}`,
    `"h":${writeInteger(box.h)}`,
    `"parent":${escapeString(box.parent)}`,
    `"exclusive":${box.exclusive ? 'true' : 'false'}`,
  ].join(',');
}

function writeRoute(route) {
  const points = route.points.map(writePoint).join(',');
  return [
    `"id":${escapeString(route.id)}`,
    `"from":${escapeString(route.from)}`,
    `"to":${escapeString(route.to)}`,
    `"orthogonal":${route.orthogonal ? 'true' : 'false'}`,
    `"points":[${points}]`,
  ].join(',');
}

function writeLabel(label) {
  const lines = label.lines.map(escapeString).join(',');
  return [
    `"id":${escapeString(label.id)}`,
    `"owner":${escapeString(label.owner)}`,
    `"text":${escapeString(label.text)}`,
    `"x":${writeInteger(label.x)}`,
    `"y":${writeInteger(label.y)}`,
    `"w":${writeInteger(label.w)}`,
    `"h":${writeInteger(label.h)}`,
    `"lines":[${lines}]`,
  ].join(',');
}

function writeArray(name, elements, writer) {
  const body = elements.map((element) => `{${writer(element)}}`).join(',\n');
  return `"${name}":[${body}]`;
}

function serialize(dump) {
  const head = [
    `"version":1`,
    `"stage":"layout"`,
    `"kind":${escapeString(dump.kind)}`,
    `"profile":"vector"`,
    `"options":${dump.options}`,
    `"canvas":{"w":${writeInteger(dump.canvas.w)},"h":${writeInteger(dump.canvas.h)}}`,
  ].join(',');
  const boxes = writeArray('boxes', dump.boxes, writeBox);
  const routes = writeArray('routes', dump.routes, writeRoute);
  const labels = writeArray('labels', dump.labels, writeLabel);
  return `{${head},\n${boxes},\n${routes},\n${labels}}\n`;
}

function requireArray(value, name) {
  if (!Array.isArray(value)) fail(`our dump has no ${name} array`);
  return value;
}

function readOurDump(raw) {
  const file = 'our vector layout';
  if (!isObject(raw)) fail(`${file} is not a JSON object`);
  const boxes = requireArray(raw.boxes, 'boxes').map((box) => {
    if (!isObject(box) || typeof box.id !== 'string') fail(`${file} has a box without an id`);
    return {
      id: box.id,
      role: typeof box.role === 'string' ? box.role : 'node',
      x: Number(box.x ?? 0),
      y: Number(box.y ?? 0),
      w: Number(box.w ?? 0),
      h: Number(box.h ?? 0),
      parent: typeof box.parent === 'string' ? box.parent : '',
      exclusive: box.exclusive === true,
    };
  });
  const routes = requireArray(raw.routes, 'routes').map((route) => {
    if (!isObject(route) || typeof route.id !== 'string') fail(`${file} has a route without an id`);
    const points = Array.isArray(route.points) ? route.points : [];
    return {
      id: route.id,
      from: String(route.from),
      to: String(route.to),
      orthogonal: route.orthogonal === true,
      points: points.map((point) => [Number(point[0]), Number(point[1])]),
    };
  });
  const labels = requireArray(raw.labels, 'labels').map((label) => {
    if (!isObject(label) || typeof label.id !== 'string') fail(`${file} has a label without an id`);
    return {
      id: label.id,
      owner: typeof label.owner === 'string' ? label.owner : '',
      text: typeof label.text === 'string' ? label.text : '',
      x: Number(label.x ?? 0),
      y: Number(label.y ?? 0),
      w: Number(label.w ?? 0),
      h: Number(label.h ?? 0),
      lines: Array.isArray(label.lines) ? label.lines.filter((line) => typeof line === 'string') : [],
    };
  });
  return {
    kind: typeof raw.kind === 'string' ? raw.kind : 'flowchart',
    options: raw.options,
    direction: isObject(raw.options) && typeof raw.options.direction === 'string' ? raw.options.direction : 'TB',
    boxes,
    routes,
    labels,
  };
}

function makeTranslated(dump, boxes, routes, labels) {
  let minX = Infinity;
  let minY = Infinity;
  let maxX = -Infinity;
  let maxY = -Infinity;
  const visit = (x, y) => {
    if (x < minX) minX = x;
    if (y < minY) minY = y;
    if (x > maxX) maxX = x;
    if (y > maxY) maxY = y;
  };
  for (const box of boxes) {
    visit(box.x, box.y);
    visit(box.x + box.w, box.y + box.h);
  }
  for (const label of labels) {
    visit(label.x, label.y);
    visit(label.x + label.w, label.y + label.h);
  }
  for (const route of routes) for (const point of route.points) visit(point[0], point[1]);
  if (!Number.isFinite(minX)) {
    minX = 0;
    minY = 0;
    maxX = 0;
    maxY = 0;
  }
  const shiftX = -minX;
  const shiftY = -minY;
  const move = (value, shift) => roundHalfAway(value + shift);
  const movedBoxes = boxes.map((box) => ({ ...box, x: move(box.x, shiftX), y: move(box.y, shiftY) }));
  const movedRoutes = routes.map((route) => ({
    ...route,
    points: route.points.map((point) => [move(point[0], shiftX), move(point[1], shiftY)]),
  }));
  const movedLabels = labels.map((label) => ({ ...label, x: move(label.x, shiftX), y: move(label.y, shiftY) }));
  return {
    kind: dump.kind,
    options: normalizeOptions(dump.options),
    canvas: { w: Math.max(0, writeInteger(roundHalfAway(maxX - minX))), h: Math.max(0, writeInteger(roundHalfAway(maxY - minY))) },
    boxes: movedBoxes,
    routes: movedRoutes,
    labels: movedLabels,
  };
}

function finalPoint(point) {
  return [unitsOf(point.x), unitsOf(point.y)];
}

function withoutRepeats(points) {
  const out = [];
  for (const point of points) {
    const last = out[out.length - 1];
    if (last && last[0] === point[0] && last[1] === point[1]) continue;
    out.push(point);
  }
  return out;
}

function routeLabelOf(dump, routeId) {
  return dump.labels.filter((label) => label.owner === routeId);
}

function hasAncestor(box, ancestor, byId) {
  let parent = box.parent;
  while (parent !== '') {
    if (parent === ancestor) return true;
    parent = byId.get(parent).parent;
  }
  return false;
}

function dagreEndpoints(dump, byId) {
  const endpoints = new Map();
  for (const box of dump.boxes) {
    const descendant = dump.boxes.find((candidate) => candidate.role === 'node' && hasAncestor(candidate, box.id, byId));
    endpoints.set(box.id, descendant?.id ?? box.id);
  }
  return endpoints;
}

function dagreEdge(graph, route) {
  return graph.edge(graph.graph().routeEndpoints.get(route.id));
}

function dagreGraph(dump) {
  const graph = new dagre.graphlib.Graph({ compound: true, multigraph: true });
  const direction = dump.direction;
  graph.setGraph({
    rankdir: direction === 'TD' ? 'TB' : direction,
    nodesep: dagreSpacing.nodesep,
    ranksep: dagreSpacing.ranksep,
    edgesep: dagreSpacing.edgesep,
    marginx: dagreSpacing.marginx,
    marginy: dagreSpacing.marginy,
    compound: true,
  });
  graph.setDefaultEdgeLabel(() => ({}));
  graph.graph().routeEndpoints = new Map();
  const byId = new Map();
  for (const box of dump.boxes) byId.set(box.id, box);
  const endpoints = dagreEndpoints(dump, byId);
  for (const box of dump.boxes) {
    graph.setNode(box.id, { width: pxOf(box.w), height: pxOf(box.h) });
  }
  for (const box of dump.boxes) {
    if (box.parent === '') continue;
    if (!byId.has(box.parent)) fail(`box ${box.id} names missing parent ${box.parent}`);
    if (endpoints.get(box.parent) === box.parent) continue;
    graph.setParent(box.id, box.parent);
  }
  addDagreEdges(graph, dump, byId, endpoints);
  return graph;
}

function addDagreEdges(graph, dump, byId, endpoints) {
  for (const route of dump.routes) {
    if (!byId.has(route.from)) fail(`route ${route.id} names missing box ${route.from}`);
    if (!byId.has(route.to)) fail(`route ${route.id} names missing box ${route.to}`);
    const labels = routeLabelOf(dump, route.id);
    const first = labels[0];
    const label = first
      ? { width: pxOf(first.w), height: pxOf(first.h), labelpos: 'c' }
      : { width: 0, height: 0, labelpos: 'c' };
    const edge = { v: endpoints.get(route.from), w: endpoints.get(route.to), name: route.id };
    graph.setEdge(edge, label);
    graph.graph().routeEndpoints.set(route.id, edge);
  }
}

function dagreDump(dump) {
  const graph = dagreGraph(dump);
  dagre.layout(graph);

  const boxes = dump.boxes.map((box) => {
    const node = graph.node(box.id);
    if (!isObject(node) || !Number.isFinite(node.x) || !Number.isFinite(node.y)) {
      return fail(`dagre returned no position for box ${box.id}`);
    }
    const w = box.role === 'group' ? unitsOf(node.width) : box.w;
    const h = box.role === 'group' ? unitsOf(node.height) : box.h;
    return {
      ...box,
      x: unitsOf(node.x) - floorDiv(w, 2),
      y: unitsOf(node.y) - floorDiv(h, 2),
      w,
      h,
    };
  });

  const routes = dump.routes.map((route) => {
    const edge = dagreEdge(graph, route);
    if (!isObject(edge) || !Array.isArray(edge.points)) {
      return fail(`dagre returned no points for route ${route.id}`);
    }
    return { ...route, points: withoutRepeats(edge.points.map(finalPoint)) };
  });

  const labels = dump.labels.map((label) => {
    if (!dump.routes.some((route) => route.id === label.owner)) return { ...label };
    const route = dump.routes.find((candidate) => candidate.id === label.owner);
    const edge = dagreEdge(graph, route);
    if (!isObject(edge) || !Number.isFinite(edge.x) || !Number.isFinite(edge.y)) {
      return fail(`dagre returned no label position for route ${route.id}`);
    }
    return {
      ...label,
      x: unitsOf(edge.x) - floorDiv(label.w, 2),
      y: unitsOf(edge.y) - floorDiv(label.h, 2),
    };
  });

  return makeTranslated(dump, boxes, routes, labels);
}

function elkEdgePoint(point, offset) {
  return finalPoint({ x: point.x + offset.x, y: point.y + offset.y });
}

function elkChildren(dump, parentId, layoutOptions) {
  const children = [];
  for (const box of dump.boxes) {
    if (box.parent !== parentId) continue;
    const nested = elkChildren(dump, box.id, layoutOptions);
    const node = { id: box.id, width: pxOf(box.w), height: pxOf(box.h) };
    if (nested.length > 0) {
      node.layoutOptions = { ...layoutOptions };
      node.children = nested;
    } else {
      node.width = pxOf(box.w);
      node.height = pxOf(box.h);
    }
    children.push(node);
  }
  return children;
}

function elkGraph(dump) {
  const byId = new Map();
  for (const box of dump.boxes) byId.set(box.id, box);
  for (const box of dump.boxes) {
    if (box.parent !== '' && !byId.has(box.parent)) fail(`box ${box.id} names missing parent ${box.parent}`);
  }
  const direction = dump.direction;
  const elkDirection = directionToElk.get(direction === 'TD' ? 'TB' : direction);
  if (!elkDirection) fail(`unknown direction ${direction}`);
  const layoutOptions = { ...elkOptions, 'elk.direction': elkDirection };
  // ELK 0.12.1 initializes model-order indices at the root. Repeating these
  // options on a child graph makes its fan-out sorter read missing indices.
  const nestedOptions = { ...layoutOptions };
  delete nestedOptions['elk.layered.crossingMinimization.forceNodeModelOrder'];
  delete nestedOptions['elk.layered.considerModelOrder.strategy'];
  const graph = {
    id: '__emd_root__',
    layoutOptions,
    children: elkChildren(dump, '', nestedOptions),
    edges: [],
  };
  graph.edges = dump.routes.map((route) => elkEdge(dump, route, byId));
  return graph;
}

function elkEdge(dump, route, byId) {
    if (!byId.has(route.from)) fail(`route ${route.id} names missing box ${route.from}`);
    if (!byId.has(route.to)) fail(`route ${route.id} names missing box ${route.to}`);
    const labels = routeLabelOf(dump, route.id);
    const edge = {
      id: `${edgeIdPrefix}${route.id}`,
      sources: [route.from],
      targets: [route.to],
    };
    if (labels.length > 0) {
      edge.labels = labels.map((label) => ({
        id: label.id,
        width: pxOf(label.w),
        height: pxOf(label.h),
      }));
    }
    return edge;
}

async function elkDump(dump) {
  const graph = elkGraph(dump);
  const elk = new ELK();
  const result = await elk.layout(graph);

  const absolute = new Map();
  absolute.set(result.id, { x: 0, y: 0 });
  const raw = new Map();
  const sizeOf = new Map();
  const walk = (node, baseX, baseY) => {
    const x = baseX + (Number.isFinite(node.x) ? node.x : 0);
    const y = baseY + (Number.isFinite(node.y) ? node.y : 0);
    raw.set(node.id, { x: Number.isFinite(node.x) ? node.x : 0, y: Number.isFinite(node.y) ? node.y : 0 });
    absolute.set(node.id, { x, y });
    sizeOf.set(node.id, {
      w: Number.isFinite(node.width) ? node.width : 0,
      h: Number.isFinite(node.height) ? node.height : 0,
    });
    for (const child of node.children ?? []) walk(child, x, y);
  };
  for (const child of result.children ?? []) walk(child, 0, 0);

  const boxes = dump.boxes.map((box) => {
    const position = absolute.get(box.id);
    if (!position) fail(`elk returned no position for box ${box.id}`);
    const size = sizeOf.get(box.id);
    const w = box.role === 'group' ? unitsOf(size.w) : box.w;
    const h = box.role === 'group' ? unitsOf(size.h) : box.h;
    return { ...box, x: unitsOf(position.x), y: unitsOf(position.y), w, h };
  });

  const { edgeIndex, labelIndex } = elkIndexes(result);
  const routes = dump.routes.map((route) => elkRoute(route, edgeIndex, absolute));
  const labels = dump.labels.map((label) => elkLabel(label, labelIndex));
  return { dump: makeTranslated(dump, boxes, routes, labels), absolute, raw };
}

function elkIndexes(result) {
  const edgeIndex = new Map();
  for (const edge of result.edges ?? []) {
    if (typeof edge.id !== 'string' || !edge.id.startsWith(edgeIdPrefix)) continue;
    edgeIndex.set(edge.id.slice(edgeIdPrefix.length), edge);
  }
  const labelIndex = new Map();
  for (const [routeId, edge] of edgeIndex) {
    for (const label of edge.labels ?? []) {
      if (typeof label.id !== 'string') fail('elk returned a label without an id');
      labelIndex.set(label.id, { routeId, label });
    }
  }
  return { edgeIndex, labelIndex };
}

function elkRoute(route, edgeIndex, absolute) {
    const edge = edgeIndex.get(route.id);
    if (!edge) fail(`elk returned no edge for route ${route.id}`);
    const offset = absolute.get(edge.container);
    if (!offset) fail(`elk returned unknown container ${edge.container} for route ${route.id}`);
    const points = [];
    for (const section of edge.sections ?? []) {
      if (section.startPoint) points.push(elkEdgePoint(section.startPoint, offset));
      for (const bend of section.bendPoints ?? []) points.push(elkEdgePoint(bend, offset));
      if (section.endPoint) points.push(elkEdgePoint(section.endPoint, offset));
    }
    return { ...route, points: withoutRepeats(points) };
}

function elkLabel(label, labelIndex) {
    const entry = labelIndex.get(label.id);
    if (!entry) return { ...label };
    const position = entry.label;
    if (!Number.isFinite(position.x) || !Number.isFinite(position.y)) {
      return fail(`elk returned no position for label ${label.id}`);
    }
    return { ...label, x: unitsOf(position.x), y: unitsOf(position.y) };
}

function writeDumpFile(target, text) {
  mkdirSync(path.dirname(target), { recursive: true });
  const temporary = `${target}.${process.pid}.tmp`;
  const descriptor = openSync(temporary, 'wx');
  try {
    try {
      writeFileSync(descriptor, text);
    } finally {
      closeSync(descriptor);
    }
    renameSync(temporary, target);
  } finally {
    rmSync(temporary, { force: true });
  }
}

function resolveCachePath(corpusPath) {
  const ours = path.join(cacheDir, `${corpusPath}.ours.json`);
  const dagreFile = path.join(cacheDir, `${corpusPath}.dagre.json`);
  const elkFile = path.join(cacheDir, `${corpusPath}.elk.json`);
  for (const candidate of [ours, dagreFile, elkFile]) {
    const relative = path.relative(cacheDir, candidate);
    if (relative.startsWith('..') || path.isAbsolute(relative)) fail(`corpus path escapes the cache: ${corpusPath}`);
  }
  return { ours, dagreFile, elkFile };
}

async function engineResult(name, run) {
  try {
    return await run();
  } catch (error) {
    throw new Error(`${name}: ${error.message}`, { cause: error });
  }
}

async function runFixture(corpusPath) {
  try {
    const files = resolveCachePath(corpusPath);
    const binary = process.env.EMD_BIN ?? path.join(repoRoot, 'bin/emd-go');
    const { stdout } = await execute(binary, ['layout', '--profile', 'vector', corpusPath], { cwd: repoRoot, maxBuffer: 64 * 1024 * 1024 });
    const dump = readOurDump(JSON.parse(stdout));
    const dagreText = serialize(await engineResult('dagre', () => dagreDump(dump)));
    const elk = await engineResult('elk', () => elkDump(dump));
    const elkText = serialize(elk.dump);
    writeDumpFile(files.dagreFile, dagreText);
    writeDumpFile(files.elkFile, elkText);
  } catch (error) {
    throw new Error(`${corpusPath}: ${error.message}`, { cause: error });
  }
}

async function runList(listFile, jobs) {
  const paths = readFileSync(listFile, 'utf8').split(/\r?\n/).filter((line) => line !== '');
  let next = 0;
  const worker = async () => {
    while (next < paths.length) await runFixture(paths[next++]);
  };
  await Promise.all(Array.from({ length: Math.min(jobs, paths.length) }, worker));
}

function testDagreGroups(dump) {
  const grouped = structuredClone(dump);
  grouped.routes[0].from = 'G1';
  grouped.routes[0].to = 'G2';
  grouped.boxes.push({ id: 'Empty', role: 'group', x: 0, y: 0, w: 2048, h: 1280, parent: '', exclusive: false });
  const graph = dagreGraph(grouped);
  const edge = graph.graph().routeEndpoints.get('e0');
  if (edge.v !== 'A' || edge.w !== 'B') fail('dagre group endpoint assertion failed');
  if (graph.children('Empty').length !== 0) fail('dagre empty group assertion failed');
  const result = dagreDump(grouped);
  if (result.routes[0].from !== 'G1' || result.routes[0].to !== 'G2') fail('dagre relation preservation assertion failed');
}

async function testElkNestedOptions() {
  for (const direction of ['TB', 'LR']) {
    const dump = {
      kind: 'flowchart',
      options: { profile: 'vector', thoroughness: 3, max_width: 0, direction, limits: {} },
      direction,
      boxes: [
        { id: 'Outer', role: 'group', x: 0, y: 0, w: 0, h: 0, parent: '', exclusive: false },
        { id: 'Inner', role: 'group', x: 0, y: 0, w: 0, h: 0, parent: 'Outer', exclusive: false },
        { id: 'A', role: 'node', x: 0, y: 0, w: 2048, h: 1280, parent: 'Inner', exclusive: true },
        { id: 'B', role: 'node', x: 0, y: 0, w: 2048, h: 1280, parent: 'Inner', exclusive: true },
      ],
      routes: [{ id: 'e0', from: 'A', to: 'B', orthogonal: true, points: [] }],
      labels: [],
    };
    const result = await elkDump(dump);
    const source = result.dump.boxes.find((box) => box.id === 'A');
    const target = result.dump.boxes.find((box) => box.id === 'B');
    const gap = direction === 'TB' ? target.y - source.y - source.h : target.x - source.x - source.w;
    const expected = unitsOf(dagreSpacing.ranksep);
    if (gap !== expected) {
      fail(`nested ${direction} rank gap is ${gap} units; expected ${expected}`);
    }
  }
}

async function testElkMixedHierarchy(dump) {
  const mixed = structuredClone(dump);
  mixed.boxes.push(
    { id: 'C', role: 'node', x: 0, y: 0, w: 2048, h: 1280, parent: 'G1', exclusive: true },
    { id: 'E', role: 'node', x: 0, y: 0, w: 2048, h: 1280, parent: 'G1', exclusive: true },
    { id: 'D', role: 'node', x: 0, y: 0, w: 2048, h: 1280, parent: '', exclusive: true },
  );
  mixed.routes.push(
    { id: 'e1', from: 'A', to: 'C', orthogonal: true, points: [] },
    { id: 'e2', from: 'D', to: 'G1', orthogonal: true, points: [] },
    { id: 'e3', from: 'G1', to: 'G2', orthogonal: true, points: [] },
    { id: 'e4', from: 'A', to: 'E', orthogonal: true, points: [] },
  );
  const result = await elkDump(mixed);
  if (result.dump.boxes.length !== mixed.boxes.length || result.dump.routes.length !== mixed.routes.length) {
    fail('ELK lost mixed hierarchy elements');
  }
  for (const route of result.dump.routes) {
    if (route.points.length < 2) fail(`ELK returned no route for ${route.id}`);
  }
}

function testTemporaryOwnership() {
  const directory = mkdtempSync(path.join(tmpdir(), 'emd-baseline-'));
  const target = path.join(directory, 'layout.json');
  const temporary = `${target}.${process.pid}.tmp`;
  try {
    writeFileSync(target, 'original');
    writeFileSync(temporary, 'occupied');
    let refused = false;
    try {
      writeDumpFile(target, 'replacement');
    } catch (error) {
      if (error.code !== 'EEXIST') throw error;
      refused = true;
    }
    if (!refused || readFileSync(target, 'utf8') !== 'original' || readFileSync(temporary, 'utf8') !== 'occupied') {
      fail('baseline output changed a file it did not own');
    }
  } finally {
    rmSync(directory, { recursive: true, force: true });
  }
}

async function selfTest() {
  testTemporaryOwnership();
  const dump = {
    kind: 'flowchart',
    options: { profile: 'vector', thoroughness: 3, max_width: 0, direction: 'TB', limits: {} },
    direction: 'TB',
    boxes: [
      { id: 'G1', role: 'group', x: 0, y: 0, w: 0, h: 0, parent: '', exclusive: false },
      { id: 'A', role: 'node', x: 0, y: 0, w: 2048, h: 1280, parent: 'G1', exclusive: true },
      { id: 'G2', role: 'group', x: 0, y: 0, w: 0, h: 0, parent: '', exclusive: false },
      { id: 'B', role: 'node', x: 0, y: 0, w: 2048, h: 1280, parent: 'G2', exclusive: true },
    ],
    routes: [{ id: 'e0', from: 'A', to: 'B', orthogonal: true, points: [] }],
    labels: [],
  };
  testDagreGroups(dump);
  await testElkNestedOptions();
  await testElkMixedHierarchy(dump);
  const elk = await elkDump(dump);
  const boxOf = (id) => elk.dump.boxes.find((box) => box.id === id);
  const groupRaw = elk.raw.get('G2');
  const childRaw = elk.raw.get('B');
  if (groupRaw.x === 0 && groupRaw.y === 0) fail('self-test fixture did not move the second group');
  if (childRaw.x !== 0 || childRaw.y !== 0) fail('self-test fixture did not place the child at the group origin');
  const group = boxOf('G2');
  const child = boxOf('B');
  if (child.x !== group.x || child.y !== group.y) {
    fail(`child at (0,0) inside a group did not take the group position: group ${group.x},${group.y} child ${child.x},${child.y}`);
  }
  const nested = structuredClone(dump);
  nested.boxes.push({ id: 'C', role: 'node', x: 0, y: 0, w: 2048, h: 1280, parent: 'G2', exclusive: true });
  nested.routes.push({ id: 'e1', from: 'B', to: 'C', orthogonal: true, points: [] });
  const nestedElk = await elkDump(nested);
  const source = nestedElk.dump.boxes.find((box) => box.id === 'B');
  const sourceGroup = nestedElk.absolute.get('G2');
  if (sourceGroup.x === 0 && sourceGroup.y === 0) fail('route self-test fixture did not move its container');
  const first = nestedElk.dump.routes.find((route) => route.id === 'e1').points[0];
  if (!first || first[0] < source.x - 1 || first[0] > source.x + source.w + 1
      || first[1] < source.y - 1 || first[1] > source.y + source.h + 1) {
    fail('nested route start did not take its container position');
  }
  if (unitsOf(-0.5 / 64) !== -1 || unitsOf(0.5 / 64) !== 1) fail('rounding assertion failed');
  const points = withoutRepeats([{ x: 1, y: 2 }, { x: 1, y: 2 }, { x: 3, y: 4 }].map(finalPoint));
  if (JSON.stringify(points) !== '[[64,128],[192,256]]') fail('route point assertion failed');
  process.stdout.write('self-test ok\n');
}

const args = process.argv.slice(2);
try {
  if (args.length === 1 && args[0] === '--self-test') {
    await selfTest();
  } else if (args.length === 2 && /^[1-9][0-9]*$/.test(args[1]) && Number.isSafeInteger(Number(args[1]))) {
    await selfTest();
    await runList(args[0], Number(args[1]));
  } else {
    throw new Error(usage);
  }
} catch (error) {
  process.stderr.write(`baseline: ${error.message}\n`);
  process.exitCode = 1;
}
