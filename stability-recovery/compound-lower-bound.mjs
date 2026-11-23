import { readFileSync } from 'node:fs';
import path from 'node:path';

const unitScale = 64n;

function nonnegativeInteger(value, context) {
  if (!Number.isSafeInteger(value) || value < 0) {
    throw new Error(context + ' must be a nonnegative safe integer');
  }
  return BigInt(value);
}

function positiveInteger(value, context) {
  const integer = nonnegativeInteger(value, context);
  if (integer === 0n) throw new Error(context + ' must be positive');
  return integer;
}

function maximum(left, right) {
  return left > right ? left : right;
}

function directionOf(dump) {
  const direction = dump.options.direction;
  return direction === 'TD' ? 'TB' : direction;
}

function metricInteger(metric, key, context) {
  return nonnegativeInteger(metric[key], context + '.' + key);
}

function shapeSignature(dump) {
  return JSON.stringify({
    kind: dump.kind,
    direction: directionOf(dump),
    boxes: dump.boxes.map((box) => [
      box.id, box.role, box.parent, box.exclusive,
      box.role === 'node' ? box.w : null,
      box.role === 'node' ? box.h : null,
    ]),
    routes: dump.routes.map((route) => [route.id, route.from, route.to]),
    labels: dump.labels.map((label) => [
      label.id, label.owner, label.text, label.lines, label.w, label.h,
    ]),
  });
}

function requireSameInput(ours, baseline, engine) {
  if (shapeSignature(ours) !== shapeSignature(baseline)) {
    throw new Error(engine + ' baseline differs in fixed semantic input or node/label sizes');
  }
}

function unsupported(reason) {
  return { supported: false, reason };
}

// The input graph is flat and acyclic. Each group top anchor is a source and
// each bottom anchor is a sink, so protected hierarchy edges cannot introduce a
// cycle or cause reversal of a semantic edge.
function topologicalOrder(nodes, routes) {
  const indegree = new Map(nodes.map((node) => [node.id, 0]));
  const outgoing = new Map(nodes.map((node) => [node.id, []]));
  for (const route of routes) {
    indegree.set(route.to, indegree.get(route.to) + 1);
    outgoing.get(route.from).push(route.to);
  }
  const queue = nodes.filter((node) => indegree.get(node.id) === 0).map((node) => node.id);
  for (let cursor = 0; cursor < queue.length; cursor += 1) {
    for (const target of outgoing.get(queue[cursor])) {
      const remaining = indegree.get(target) - 1;
      indegree.set(target, remaining);
      if (remaining === 0) queue.push(target);
    }
  }
  return { order: queue, outgoing };
}

function analyzeFixture(dump, source, metrics, constants) {
  if (dump.kind !== 'flowchart') return unsupported('kind outside the proven flowchart subset');
  if (dump.profile !== 'vector' || dump.options.profile !== 'vector') {
    throw new Error('expected a native vector layout dump');
  }
  const direction = directionOf(dump);
  if (!['TB', 'BT', 'LR', 'RL'].includes(direction)) throw new Error('invalid direction');
  // This deliberately also rejects occurrences in comments and node text.
  if (/\bdirection\b/i.test(source)) return unsupported('source contains a direction token');
  const nodes = dump.boxes.filter((box) => box.role === 'node');
  const groups = dump.boxes.filter((box) => box.role === 'group');
  if (nodes.length === 0) return unsupported('no real nodes');
  if (groups.length === 0) return unsupported('no ordinary groups');
  if (nodes.length + groups.length !== dump.boxes.length) return unsupported('other box role');
  if (groups.some((group) => group.parent !== '')) return unsupported('nested group');
  if (nodes.some((node) => node.exclusive !== true)) return unsupported('nonexclusive real node');
  const byId = new Map(dump.boxes.map((box) => [box.id, box]));
  if (byId.size !== dump.boxes.length) throw new Error('duplicate box ID');
  const byGroup = new Map(groups.map((group) => [group.id, []]));
  for (const node of nodes) {
    if (node.parent !== '' && !byGroup.has(node.parent)) {
      throw new Error('node names a missing or non-group parent');
    }
    if (node.parent !== '') byGroup.get(node.parent).push(node);
  }
  if ([...byGroup.values()].some((members) => members.length === 0)) {
    return unsupported('empty group has no measured title input');
  }
  if (dump.routes.some((route) =>
    byId.get(route.from)?.role !== 'node' || byId.get(route.to)?.role !== 'node')) {
    return unsupported('route endpoint is not a real node');
  }
  const { order, outgoing } = topologicalOrder(nodes, dump.routes);
  if (order.length !== nodes.length) return unsupported('semantic graph contains a cycle or self-loop');

  const vertical = direction === 'TB' || direction === 'BT';
  const size = new Map(nodes.map((node) => [node.id, {
    cross: positiveInteger(vertical ? node.w : node.h, node.id + '.cross'),
    rank: positiveInteger(vertical ? node.h : node.w, node.id + '.rank'),
  }]));
  const n = BigInt(nodes.length);
  const extentSum = nodes.reduce((sum, node) =>
    sum + (positiveInteger(node.w, node.id + '.w') + positiveInteger(node.h, node.id + '.h')) / 2n, 0n);
  const mean = maximum(1n, extentSum / n);
  for (const engine of ['ours', 'dagre', 'elk']) {
    if (metricInteger(metrics[engine], 'nodes', engine) !== n ||
        metricInteger(metrics[engine], 'mean_node_extent', engine) !== mean) {
      throw new Error(engine + ' metric does not match the fixed node dimensions');
    }
  }

  // Longest weighted path restricted to each group's real-node induced DAG.
  const distance = new Map(nodes.map((node) => [node.id, size.get(node.id).rank]));
  const predecessor = new Map(nodes.map((node) => [node.id, null]));
  let internalEdges = 0n;
  for (const from of order) {
    const parent = byId.get(from).parent;
    for (const to of outgoing.get(from)) {
      if (parent === '' || parent !== byId.get(to).parent) continue;
      internalEdges += 1n;
      const candidate = distance.get(from) + constants.rankGap + size.get(to).rank;
      if (candidate > distance.get(to)) {
        distance.set(to, candidate);
        predecessor.set(to, from);
      }
    }
  }

  const titleRankMinimum = vertical ? constants.lineHeight + constants.clusterPad : 0n;
  const bounds = [];
  let containmentArea = 0n;
  let borderArea = 0n;
  for (const group of groups) {
    const members = byGroup.get(group.id);
    let end = members[0].id;
    let cross = 0n;
    let separatedCross = 0n;
    for (const member of members) {
      const extent = size.get(member.id).cross;
      cross = maximum(cross, extent);
      // Two border-to-member paths telescope. Keep the odd-width floor loss.
      const bordered = 2n * (extent / 2n) + 2n * (constants.borderWidth / 2n) +
        constants.borderWidth + 2n * constants.clusterPad;
      separatedCross = maximum(separatedCross, maximum(extent, bordered));
      if (distance.get(member.id) > distance.get(end)) end = member.id;
    }
    const path = [];
    for (let at = end; at !== null; at = predecessor.get(at)) path.push(at);
    path.reverse();
    const rank = titleRankMinimum + 2n * constants.rankGap + distance.get(end);
    containmentArea += cross * rank;
    borderArea += separatedCross * rank;
    const actualCross = nonnegativeInteger(vertical ? group.w : group.h, group.id + '.cross');
    const actualRank = nonnegativeInteger(vertical ? group.h : group.w, group.id + '.rank');
    bounds.push({
      id: group.id,
      nodes: members.length,
      longest_path: path,
      node_path_rank_extent: distance.get(end),
      minimum_title_rank_extent: titleRankMinimum,
      minimum_rank_extent: rank,
      containment_cross_extent: cross,
      border_cross_extent: separatedCross,
      observed_cross_extent: actualCross,
      observed_rank_extent: actualRank,
      observed_below_literal_size: actualCross < separatedCross || actualRank < rank,
    });
  }
  // C8a separates each top-level group from other groups and outside nodes.
  // C2 separates root exclusive nodes. Thus these rectangles have disjoint
  // interiors, and the bounding rectangle's area is at least their area sum.
  let rootArea = 0n;
  for (const node of nodes) {
    if (node.parent === '') rootArea += BigInt(node.w) * BigInt(node.h);
  }
  containmentArea += rootArea;
  borderArea += rootArea;
  const denominator = mean * mean * n;
  const routeLength = internalEdges * constants.rankGap;
  const lengthTerm = routeLength / mean;
  const containmentCost = lengthTerm + containmentArea / denominator;
  const borderCost = lengthTerm + borderArea / denominator;
  const ours = metricInteger(metrics.ours, 'soft_cost', 'ours');
  const dagre = metricInteger(metrics.dagre, 'soft_cost', 'dagre');
  const elk = metricInteger(metrics.elk, 'soft_cost', 'elk');
  const best = dagre < elk ? dagre : elk;
  const exceeds = (cost) => 100n * cost > 120n * best;
  const singleChain = groups.length === 1 && nodes.every((node) => node.parent === groups[0].id) &&
    dump.routes.length === nodes.length - 1 &&
    nodes.every((node) => outgoing.get(node.id).length <= 1) &&
    new Set(dump.routes.map((route) => route.to)).size === dump.routes.length;
  return {
    supported: true,
    pattern: singleChain ? 'one ordinary group containing a directed chain' : 'flat ordinary groups with an acyclic real-node graph',
    direction,
    nodes: nodes.length,
    groups: groups.length,
    mean_node_extent: mean,
    internal_group_edges: internalEdges,
    minimum_route_length: routeLength,
    minimum_area_containment_width: containmentArea,
    minimum_area_border_width: borderArea,
    cost_denominator: denominator,
    lower_cost_containment_width: containmentCost,
    lower_cost_border_width: borderCost,
    ours_cost: ours,
    dagre_cost: dagre,
    elk_cost: elk,
    best_baseline_cost: best,
    containment_unavoidable: exceeds(containmentCost),
    literal_unavoidable: exceeds(borderCost),
    observed_below_literal_cost: ours < borderCost,
    observed_below_literal_size: bounds.some((bound) => bound.observed_below_literal_size),
    group_bounds: bounds,
  };
}

function selfTest() {
  const constants = { rankGap: 3072n, lineHeight: 1280n, clusterPad: 1024n, borderWidth: 512n };
  const dump = {
    kind: 'flowchart', profile: 'vector', options: { profile: 'vector', direction: 'TB' },
    boxes: [
      { id: 'one', role: 'group', w: 5260, h: 16128, parent: '', exclusive: false },
      { id: 'A', role: 'node', w: 2188, h: 2304, parent: 'one', exclusive: true },
      { id: 'B', role: 'node', w: 2127, h: 2304, parent: 'one', exclusive: true },
    ],
    routes: [{ id: 'e0', from: 'A', to: 'B' }], labels: [],
  };
  const metric = (soft_cost) => ({ nodes: 2, mean_node_extent: 2230, soft_cost });
  const metrics = { ours: metric(9), dagre: metric(5), elk: metric(2) };
  const assert = (condition, label) => { if (!condition) throw new Error('self-test: ' + label); };
  const result = analyzeFixture(dump, 'graph TB\nsubgraph one\nA --> B\nend\n', metrics, constants);
  assert(result.lower_cost_containment_width === 4n, 'containment lower bound');
  assert(result.lower_cost_border_width === 9n, 'border lower bound');
  assert(result.minimum_route_length === 3072n, 'route length lower bound');
  assert(result.minimum_area_border_width === 84833280n, 'area lower bound');
  assert(result.literal_unavoidable && result.containment_unavoidable, 'strict exception inequality');
  assert(!result.observed_below_literal_size, 'literal dimensions accepted');
  const equalThreshold = { ...metrics, dagre: metric(8), elk: metric(10) };
  assert(!analyzeFixture(dump, '', equalThreshold, constants).literal_unavoidable, 'within 20 percent');
  const odd = structuredClone(dump);
  odd.boxes[1].w = 2189;
  assert(analyzeFixture(odd, '', metrics, constants).group_bounds[0].border_cross_extent === 5260n,
    'odd-width separation uses floors');
  assert(!analyzeFixture(dump, 'direction LR', metrics, constants).supported, 'direction token excluded');
  const nested = structuredClone(dump);
  nested.boxes[0].parent = 'outer';
  assert(!analyzeFixture(nested, '', metrics, constants).supported, 'nested group excluded');
  const cycle = structuredClone(dump);
  cycle.routes.push({ id: 'e1', from: 'B', to: 'A' });
  assert(!analyzeFixture(cycle, '', metrics, constants).supported, 'cycle excluded');
  const changed = structuredClone(dump);
  changed.boxes[1].w += 1;
  let rejected = false;
  try { requireSameInput(dump, changed, 'test'); } catch { rejected = true; }
  assert(rejected, 'fixed node-size mismatch rejected');
  return 'compound lower-bound self-test passed';
}

function readJSON(filename) {
  return JSON.parse(readFileSync(filename, 'utf8'));
}

function resolveInside(root, relative) {
  if (typeof relative !== 'string' || relative.length === 0 || path.isAbsolute(relative)) {
    throw new Error('expected a nonempty relative corpus path');
  }
  const target = path.resolve(root, relative);
  const remainder = path.relative(root, target);
  if (remainder === '..' || remainder.startsWith('..' + path.sep) || path.isAbsolute(remainder)) {
    throw new Error('corpus path escapes its input root: ' + relative);
  }
  return target;
}

function readConstants(repo) {
  const rows = readJSON(path.join(repo, 'spec/data/layout-constants.json'));
  const value = (name) => {
    const matches = rows.filter((row) => row.name === name);
    if (matches.length !== 1) throw new Error('missing or duplicate constant ' + name);
    return nonnegativeInteger(matches[0].vector, name + '.vector');
  };
  const constants = {
    rankGap: value('rank_gap'), lineHeight: value('line_h'),
    clusterPad: value('cluster_pad'), borderWidth: value('cluster_border_w'),
  };
  if (constants.rankGap === 0n || constants.lineHeight === 0n || constants.borderWidth === 0n) {
    throw new Error('rank_gap, line_h, and cluster_border_w must be positive');
  }
  return constants;
}

function argumentsOf(args) {
  const options = {
    repo: '.', metrics: 'recovery-results/trial-metrics.json',
    dumps: 'recovery-results/trial', baselineCache: 'corpus/.cache/quality',
    corpus: 'corpus/quality-corpus.txt',
  };
  const names = new Map([
    ['--repo', 'repo'], ['--metrics', 'metrics'], ['--dumps', 'dumps'],
    ['--baseline-cache', 'baselineCache'], ['--corpus', 'corpus'],
  ]);
  for (let index = 0; index < args.length; index += 2) {
    const name = names.get(args[index]);
    if (!name || index + 1 >= args.length) {
      throw new Error('usage: node compound-lower-bound.mjs [--repo DIR] [--metrics FILE] ' +
        '[--dumps DIR] [--baseline-cache DIR] [--corpus FILE] | --self-test');
    }
    options[name] = args[index + 1];
  }
  options.repo = path.resolve(options.repo);
  for (const name of ['metrics', 'dumps', 'baselineCache', 'corpus']) {
    options[name] = path.resolve(options.repo, options[name]);
  }
  return options;
}

function collect(options) {
  const constants = readConstants(options.repo);
  const paths = readFileSync(options.corpus, 'utf8').split(/\r?\n/)
    .map((line) => line.trim()).filter((line) => line !== '' && !line.startsWith('#'));
  if (new Set(paths).size !== paths.length) throw new Error('duplicate corpus path');
  const rows = readJSON(options.metrics);
  if (!Array.isArray(rows)) throw new Error('metrics must be an array');
  const byPath = new Map(rows.map((row) => [row.path, row]));
  if (byPath.size !== rows.length || rows.length !== paths.length ||
      paths.some((filename) => !byPath.has(filename))) {
    throw new Error('metric rows must cover the exact corpus list once each');
  }
  const supported = [];
  const skipped = [];
  for (const filename of paths) {
    try {
      const dump = readJSON(resolveInside(options.dumps, filename + '.ours.json'));
      const source = readFileSync(resolveInside(options.repo, filename), 'utf8');
      const result = analyzeFixture(dump, source, byPath.get(filename), constants);
      if (!result.supported) {
        skipped.push({ path: filename, reason: result.reason });
        continue;
      }
      for (const engine of ['dagre', 'elk']) {
        const baseline = readJSON(resolveInside(options.baselineCache, filename + '.' + engine + '.json'));
        requireSameInput(dump, baseline, engine);
      }
      supported.push({
        path: filename, ...result,
        node_sizes: dump.boxes.filter((box) => box.role === 'node')
          .map((box) => ({ id: box.id, parent: box.parent, w: box.w, h: box.h })),
      });
    } catch (error) {
      throw new Error(filename + ': ' + error.message, { cause: error });
    }
  }
  const skipCounts = {};
  for (const row of skipped) skipCounts[row.reason] = (skipCounts[row.reason] ?? 0) + 1;
  const counterexamples = supported.filter((row) => row.literal_unavoidable);
  const weakerCounterexamples = supported.filter((row) => row.containment_unavoidable);
  const budget = Math.floor(paths.length / 20);
  return {
    schema: 1,
    purpose: 'Read-only lower bounds under the literal ordinary-group layered contract',
    units_per_pixel: Number(unitScale),
    computed_integer_encoding: 'decimal strings',
    inputs: options,
    constants,
    fixture_count: paths.length,
    supported_count: supported.length,
    skipped_count: skipped.length,
    skip_counts: skipCounts,
    allowed_quality_exceptions: budget,
    containment_width_unavoidable_count: weakerCounterexamples.length,
    literal_border_width_unavoidable_count: counterexamples.length,
    supported_subset_exceeds_exception_budget: counterexamples.length > budget,
    warning: 'These bounds include the mandatory hierarchy rank bands. A post-layout phase that ' +
      'changes those rules needs a new explicit contract. Unsupported fixtures contribute no count.',
    counterexamples,
    supported_summaries: supported.map((row) => ({
      path: row.path, pattern: row.pattern, nodes: row.nodes, groups: row.groups,
      lower_cost_containment_width: row.lower_cost_containment_width,
      lower_cost_border_width: row.lower_cost_border_width,
      best_baseline_cost: row.best_baseline_cost,
      ours_cost: row.ours_cost,
    })),
    observed_below_literal_contract: supported
      .filter((row) => row.observed_below_literal_cost || row.observed_below_literal_size)
      .map((row) => ({
        path: row.path, ours_cost: row.ours_cost,
        lower_cost_border_width: row.lower_cost_border_width,
        group_bounds: row.group_bounds,
      })),
    skipped,
  };
}

if (process.argv.length === 3 && process.argv[2] === '--self-test') {
  process.stdout.write(selfTest() + '\n');
} else {
  const result = collect(argumentsOf(process.argv.slice(2)));
  process.stdout.write(JSON.stringify(result, (_key, value) =>
    typeof value === 'bigint' ? value.toString() : value, 2) + '\n');
}
