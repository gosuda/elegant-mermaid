import { readFileSync } from 'node:fs';
import { hierarchy, treemap, treemapSquarify } from 'd3-hierarchy';
import { sankey, sankeyJustify } from 'd3-sankey';

const unitScale = 64;
const treemapSectionHeader = 1600;
const treemapSectionPadding = 640;
const treemapInnerPadding = 640;

function fail(message) {
  process.stderr.write(`d3: ${message}\n`);
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

function compareBytewise(left, right) {
  if (left < right) return -1;
  if (left > right) return 1;
  return 0;
}

function readJson(file) {
  let text;
  try {
    text = readFileSync(file, 'utf8');
  } catch (error) {
    return fail(`cannot read ${file}: ${error.message}`);
  }
  try {
    return JSON.parse(text);
  } catch (error) {
    return fail(`invalid JSON in ${file}: ${error.message}`);
  }
}

function numberOf(value, name) {
  if (typeof value !== 'number' || !Number.isFinite(value)) fail(`${name} must be a number`);
  return value;
}

function positiveOf(value, name) {
  const number = numberOf(value, name);
  if (number <= 0) fail(`${name} must be positive`);
  return number;
}

function runSankey(description) {
  const width = positiveOf(description.width, 'width');
  const height = positiveOf(description.height, 'height');
  const nodeWidth = positiveOf(description.nodeWidth ?? 10, 'nodeWidth');
  const nodePadding = positiveOf(description.nodePadding ?? 12, 'nodePadding');
  if (!Array.isArray(description.nodes)) fail('nodes must be an array');
  if (!Array.isArray(description.links)) fail('links must be an array');
  const nodes = description.nodes.map((node) => {
    if (typeof node !== 'object' || node === null || typeof node.id !== 'string') fail('each node needs a string id');
    return { id: node.id };
  });
  const links = description.links.map((link) => {
    if (typeof link !== 'object' || link === null) fail('each link must be an object');
    return {
      source: String(link.source),
      target: String(link.target),
      value: positiveOf(link.value, 'link value'),
    };
  });
  const layout = sankey()
    .nodeId((node) => node.id)
    .nodeWidth(nodeWidth)
    .nodePadding(nodePadding)
    .nodeAlign(sankeyJustify)
    .iterations(description.iterations ?? 6)
    .size([width, height]);
  const graph = layout({ nodes, links });
  return graph.nodes.map((node) => ({
    id: node.id,
    x0: unitsOf(node.x0),
    y0: unitsOf(node.y0),
    x1: unitsOf(node.x1),
    y1: unitsOf(node.y1),
  }));
}

function describeTree(node, name) {
  if (typeof node !== 'object' || node === null) fail(`${name} must be an object`);
  if (typeof node.id !== 'string') fail(`${name} needs a string id`);
  const children = Array.isArray(node.children) ? node.children : [];
  if (children.length === 0) {
    const value = numberOf(node.value, `value of ${node.id}`);
    if (value < 0) fail(`value of ${node.id} must not be negative`);
    return { id: node.id, value };
  }
  return { id: node.id, children: children.map((child) => describeTree(child, `child of ${node.id}`)) };
}

function rectangleOf(node) {
  return {
    id: node.data.id,
    x0: unitsOf(node.x0),
    y0: unitsOf(node.y0),
    x1: unitsOf(node.x1),
    y1: unitsOf(node.y1),
  };
}


function runTreemap(description) {
  const width = positiveOf(description.width ?? 960, 'width');
  const height = positiveOf(description.height ?? 500, 'height');
  const sectionHeader = treemapSectionHeader / unitScale;
  const sectionPadding = treemapSectionPadding / unitScale;
  const innerPadding = treemapInnerPadding / unitScale;
  const tree = describeTree(description.tree, 'tree');
  const root = hierarchy(tree).sum((node) => (Array.isArray(node.children) ? 0 : node.value));
  const layout = treemap()
    .size([width, height])
    .round(true)
    .tile(treemapSquarify)
    .paddingInner(innerPadding)
    .paddingTop(sectionHeader + sectionPadding)
    .paddingLeft(sectionPadding)
    .paddingRight(sectionPadding)
    .paddingBottom(sectionPadding);
  layout(root);
  return root.leaves().map(rectangleOf);
}

const args = process.argv.slice(2);
if (args.length !== 2) fail('usage: d3.mjs sankey|treemap FILE');
const kind = args[0];
const description = readJson(args[1]);
if (typeof description !== 'object' || description === null) fail('description must be a JSON object');
let rows;
if (kind === 'sankey') rows = runSankey(description);
else if (kind === 'treemap') rows = runTreemap(description);
else fail(`unknown kind ${kind}`);
rows.sort((left, right) => compareBytewise(left.id, right.id));
let out = '';
for (const row of rows) {
  out += `${row.id} ${row.x0} ${row.y0} ${row.x1} ${row.y1}\n`;
}
process.stdout.write(out);
