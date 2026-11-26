<script lang="ts">
import { onMount } from 'svelte';
import { ENGINE_URLS, staticUrl } from '../lib/assets';
import { type Comparison, compare, type EngineAnswers, excerpt } from '../lib/compare';
import { debounce } from '../lib/debounce';
import {
  CHARSETS,
  type Charset,
  COPY_OK,
  COPY_REFUSED,
  COPY_UNSUPPORTED,
  DEFAULT_SOURCE,
  EMPTY_MESSAGE,
  INVALID_LINK_MESSAGE,
  THEMES,
} from '../lib/defaults';
import {
  accessibleName,
  editorRanges,
  emptySourceDiagnostic,
  type MergedDiagnostic,
  mergeDiagnostics,
  selectionLabel,
} from '../lib/diagnostics';
import Editor from '../lib/Editor.svelte';
import EnginePane from '../lib/EnginePane.svelte';
import { EngineClient, type EngineSnapshot, IDLE_SNAPSHOT } from '../lib/engine-client';
import { createEngineWorker } from '../lib/engine-worker-factory';
import { INITIAL_TEXT } from '../lib/initial-text';
import { optionsJson, type RenderOptions } from '../lib/options';
import { ANSWER_OPS, type AnswerOp, DEBOUNCE_MS, ENGINE_IDS, ENGINE_NAME, type EngineId } from '../lib/protocol';
import { parseResponse } from '../lib/response';
import { RevisionGuard } from '../lib/revision';
import samples from '../lib/samples.json';
import {
  compressionSupported,
  decodeShare,
  encodeShare,
  fragmentPayload,
  type SharePayload,
  shareUrl,
} from '../lib/share';
import { type EngineView, emptyView, failureText, nextTab, paneContent, TABS, type TabId } from '../lib/view';

type EngineChoice = EngineId | 'both';

interface Job extends RenderOptions {
  revision: number;
  source: string;
}

const guard = new RevisionGuard();
const clients: Partial<Record<EngineId, EngineClient>> = {};
const dispatched: Record<EngineId, number> = { go: 0, rust: 0 };
const sampleText = INITIAL_TEXT !== '' ? INITIAL_TEXT : 'Engines are loading. Output appears here.';
const DEFAULT_SHARE: SharePayload = {
  src: DEFAULT_SOURCE,
  opt: { theme: 'elegant-light', background: null, charset: 'unicode', max_width: null },
};

let source = $state(DEFAULT_SHARE.src);
let theme = $state<string>(DEFAULT_SHARE.opt.theme);
let charset = $state<Charset>(DEFAULT_SHARE.opt.charset);
let background = $state<string | null>(DEFAULT_SHARE.opt.background);
let maxWidth = $state<number | null>(DEFAULT_SHARE.opt.max_width);
let engineChoice = $state<EngineChoice>('both');
let tab = $state<TabId>('svg');
let latest = $state(0);
let issued = $state<Job | null>(null);
let message = $state('');
let sharedUrl = $state<string | null>(null);
let fixing = $state(false);
let bootDone = false;
let hashRevision = 0;
let snapshots = $state<Record<EngineId, EngineSnapshot>>({ go: IDLE_SNAPSHOT, rust: IDLE_SNAPSHOT });
let views = $state<Record<EngineId, EngineView>>({ go: emptyView(), rust: emptyView() });
let svgUrls = $state<Record<EngineId, string | null>>({ go: null, rust: null });
let editor: ReturnType<typeof Editor> | undefined = $state();
const tabButtons: (HTMLButtonElement | undefined)[] = [];

const selected = $derived<EngineId[]>(engineChoice === 'both' ? ['go', 'rust'] : [engineChoice]);
const issuedEmpty = $derived(issued !== null && issued.source === '');
const sampleKind = $derived(samples.find((entry) => entry.source === source)?.kind ?? '');
const fixEngine = $derived<EngineId>(selected.includes('go') ? 'go' : 'rust');
const fixDisabled = $derived(snapshots[fixEngine].state !== 'ready' || fixing);
const radioDisabled = $derived({
  go: snapshots.go.state === 'error',
  rust: snapshots.rust.state === 'error',
  both: snapshots.go.state === 'error' || snapshots.rust.state === 'error',
});

const merged = $derived.by<MergedDiagnostic[]>(() => {
  if (issuedEmpty) {
    return [{ engine: selectionLabel(selected), diagnostic: emptySourceDiagnostic(), source: '' }];
  }
  return mergeDiagnostics(
    selected.includes('go') ? views.go.diagnostics : null,
    selected.includes('rust') ? views.rust.diagnostics : null,
  );
});

const comparison = $derived.by<Comparison>(() => {
  if (engineChoice !== 'both' || latest === 0) {
    return { kind: 'none', text: '' };
  }
  const answers = (id: EngineId): EngineAnswers => {
    const view = views[id];
    const current = view.revision === latest;
    return {
      failed: snapshots[id].state === 'error',
      layout: current ? (view.answers.layout ?? null) : null,
      text: current ? (view.answers.render_text ?? null) : null,
    };
  };
  return compare(answers('go'), answers('rust'), latest, issuedEmpty);
});

const difference = $derived(comparison.kind === 'settled' ? comparison.difference : null);

$effect(() => {
  editor?.showDiagnostics(editorRanges(merged, Number.POSITIVE_INFINITY));
});

const schedule = debounce(() => issueRevision(), DEBOUNCE_MS);

function currentOptions(): RenderOptions {
  return { theme, charset, background, maxWidth };
}

function setSvg(id: EngineId, output: string): void {
  const previous = svgUrls[id];
  if (previous !== null) {
    URL.revokeObjectURL(previous);
  }
  svgUrls[id] = URL.createObjectURL(new Blob([output], { type: 'image/svg+xml' }));
}

function accept(id: EngineId, job: Job, op: AnswerOp, raw: string): void {
  if (!guard.accept(job.revision)) {
    return;
  }
  const response = parseResponse(raw) ?? { ok: false, output: '', diagnostics: [], applied: 0 };
  const view = views[id];
  view.answers[op] = { ok: response.ok, output: response.output };
  if (op === 'check' || response.ok) {
    view.valid[op] = { revision: job.revision, output: response.output };
  }
  if (op === 'render_svg' && response.ok) {
    setSvg(id, response.output);
  }
  if (op === 'check') {
    view.diagnostics = { diagnostics: response.diagnostics, source: job.source };
  }
}

async function dispatch(id: EngineId, job: Job): Promise<void> {
  const client = clients[id];
  if (client === undefined || dispatched[id] === job.revision) {
    return;
  }
  dispatched[id] = job.revision;
  await Promise.all(
    ANSWER_OPS.map(async (op) => {
      try {
        accept(id, job, op, await client.call(op, job.source, optionsJson(op, job), job.revision));
      } catch {
        if (snapshots[id].state === 'ready') {
          accept(id, job, op, '');
        }
      }
    }),
  );
}

function issueRevision(): void {
  schedule.cancel();
  const revision = guard.issue();
  latest = revision;
  const job: Job = { revision, source, ...currentOptions() };
  issued = job;
  for (const id of ENGINE_IDS) {
    views[id].revision = revision;
    views[id].answers = {};
  }
  if (job.source === '') {
    return;
  }
  for (const id of selected) {
    if (snapshots[id].state === 'ready') {
      void dispatch(id, job);
    }
  }
}

function onSnapshot(id: EngineId, snapshot: EngineSnapshot): void {
  const previous = snapshots[id].state;
  snapshots[id] = snapshot;
  const name = ENGINE_NAME[id];
  if (snapshot.state === 'ready' && previous !== 'ready') {
    message = `${name} engine ready.`;
    if (bootDone && issued !== null && issued.source !== '' && selected.includes(id)) {
      void dispatch(id, issued);
    }
  } else if (snapshot.state === 'error' && previous !== 'error') {
    dispatched[id] = 0;
    message = failureText(name, snapshot.message);
  } else if (snapshot.state === 'loading' && previous === 'error') {
    message = '';
  }
}

function onSourceChange(text: string): void {
  source = text;
  if (bootDone) {
    message = '';
    schedule();
  }
}

function selectEngine(choice: EngineChoice): void {
  engineChoice = choice;
  for (const id of selected) {
    clients[id]?.start();
    if (bootDone && issued !== null && issued.source !== '' && snapshots[id].state === 'ready') {
      void dispatch(id, issued);
    }
  }
}

function changeOption(apply: () => void): void {
  apply();
  if (bootDone) {
    schedule();
  }
}

function selectTab(id: TabId): void {
  tab = id;
}

function onTabKey(event: KeyboardEvent): void {
  const target = nextTab(tab, event.key);
  if (target === null) {
    return;
  }
  event.preventDefault();
  tab = target;
  tabButtons[TABS.findIndex((spec) => spec.id === target)]?.focus();
}

function chooseSample(kind: string): void {
  const entry = samples.find((candidate) => candidate.kind === kind);
  if (entry !== undefined) {
    editor?.setText(entry.source);
  }
}

function selectDiagnostic(item: MergedDiagnostic): void {
  const [range] = editorRanges([item], Number.POSITIVE_INFINITY);
  if (range !== undefined) {
    editor?.select(range.from, range.to);
  }
}

function skipToEditor(event: MouseEvent): void {
  event.preventDefault();
  if (editor?.focus() !== true) {
    document.querySelector<HTMLElement>('#editor pre')?.focus();
  }
}

async function applyFix(): Promise<void> {
  const client = clients[fixEngine];
  if (client === undefined || fixing) {
    return;
  }
  fixing = true;
  const text = editor?.getText() ?? source;
  try {
    const raw = await client.call('fix', text, optionsJson('fix', currentOptions()), guard.latest);
    const response = parseResponse(raw);
    if (response === null) {
      message = `The ${ENGINE_NAME[fixEngine]} engine returned an unreadable answer.`;
      return;
    }
    if (editor?.getText() === text && response.output !== text) {
      editor.setText(response.output);
    }
    message =
      response.applied === 0
        ? 'No safe fixes to apply.'
        : `Applied ${response.applied} ${response.applied === 1 ? 'fix' : 'fixes'}.`;
  } catch (error) {
    message = `The ${ENGINE_NAME[fixEngine]} engine could not apply fixes: ${error instanceof Error ? error.message : String(error)}`;
  } finally {
    fixing = false;
  }
}

async function copyLink(): Promise<void> {
  sharedUrl = null;
  let url: string;
  try {
    if (!compressionSupported()) {
      throw new Error('CompressionStream is not available');
    }
    const encoded = await encodeShare({
      src: editor?.getText() ?? source,
      opt: { theme, background, charset, max_width: maxWidth },
    });
    url = shareUrl(window.location.href, encoded);
  } catch (error) {
    message = error instanceof RangeError ? error.message : COPY_UNSUPPORTED;
    return;
  }
  try {
    await navigator.clipboard.writeText(url);
    message = COPY_OK;
  } catch {
    sharedUrl = url;
    message = COPY_REFUSED;
  }
}

async function openShare(encoded: string): Promise<string> {
  const payload = compressionSupported() ? await decodeShare(encoded) : null;
  const shared = payload ?? DEFAULT_SHARE;
  theme = shared.opt.theme;
  charset = shared.opt.charset;
  background = shared.opt.background;
  maxWidth = shared.opt.max_width;
  editor?.setText(shared.src);
  source = shared.src;
  return payload === null ? INVALID_LINK_MESSAGE : '';
}

async function boot(): Promise<void> {
  const encoded = fragmentPayload(window.location.hash);
  const note = encoded === null ? '' : await openShare(encoded);
  bootDone = true;
  issueRevision();
  if (note !== '') {
    message = note;
  }
}

async function followShare(): Promise<void> {
  const revision = ++hashRevision;
  const encoded = fragmentPayload(window.location.hash);
  if (encoded === null || !bootDone) {
    return;
  }
  const note = await openShare(encoded);
  if (revision !== hashRevision) {
    return;
  }
  issueRevision();
  message = note;
}

onMount(() => {
  const unsubscribe: (() => void)[] = [];
  for (const id of ENGINE_IDS) {
    const client = new EngineClient({
      id,
      createWorker: createEngineWorker,
      loader: staticUrl(ENGINE_URLS[id].loader),
      wasm: staticUrl(ENGINE_URLS[id].wasm),
    });
    clients[id] = client;
    unsubscribe.push(client.subscribe((snapshot) => onSnapshot(id, snapshot)));
  }
  for (const id of selected) {
    clients[id]?.start();
  }
  void boot();
  return () => {
    ++hashRevision;
    schedule.cancel();
    for (const stop of unsubscribe) {
      stop();
    }
    for (const id of ENGINE_IDS) {
      clients[id]?.dispose();
      const url = svgUrls[id];
      if (url !== null) {
        URL.revokeObjectURL(url);
      }
    }
  };
});
</script>

<svelte:window onhashchange={() => void followShare()} />

<main>
  <a class="skip" href="#editor" onclick={skipToEditor}>Skip to editor</a>

  <header>
    <h1>Elegant Mermaid</h1>
    <p>Render and compare Mermaid diagrams locally in your browser; source is never uploaded.</p>
  </header>

  <div class="toolbar" role="group" aria-label="Playground options">
    <label>
      Sample
      <select value={sampleKind} onchange={(event) => chooseSample(event.currentTarget.value)}>
        <option value="" disabled>Choose a sample</option>
        {#each samples as entry (entry.kind)}
          <option value={entry.kind}>{entry.kind}</option>
        {/each}
      </select>
    </label>
    <label>
      Theme
      <select value={theme} onchange={(event) => changeOption(() => (theme = event.currentTarget.value))}>
        {#each THEMES as name (name)}
          <option value={name}>{name}</option>
        {/each}
      </select>
    </label>
    <label>
      Charset
      <select value={charset} onchange={(event) => changeOption(() => (charset = event.currentTarget.value as Charset))}>
        {#each CHARSETS as name (name)}
          <option value={name}>{name}</option>
        {/each}
      </select>
    </label>
    <button type="button" onclick={copyLink}>Copy link</button>
  </div>

  <div class="status-area">
    {#if comparison.kind === 'pending'}
      <p class="comparison" data-testid="comparison">{comparison.text}</p>
    {/if}
    <div class="status" role="status" aria-live="polite">
      {#if comparison.kind === 'settled' || comparison.kind === 'unavailable'}
        <p class="comparison" data-testid="comparison">{comparison.text}</p>
      {/if}
      {#if message !== ''}
        <p data-testid="message">{message}</p>
      {/if}
    </div>
    {#if sharedUrl !== null}
      <label class="shared">
        Shared link
        <input type="text" readonly value={sharedUrl} onfocus={(event) => event.currentTarget.select()} />
      </label>
    {/if}
    {#if difference !== null}
      <section class="difference" aria-label="First difference" data-testid="difference">
        <p>First difference: {difference.subject} line {difference.difference.line}</p>
        <dl>
          <dt>Go line {difference.difference.line}</dt>
          <dd><code>{excerpt(difference.difference.left, difference.difference.line)}</code></dd>
          <dt>Rust line {difference.difference.line}</dt>
          <dd><code>{excerpt(difference.difference.right, difference.difference.line)}</code></dd>
        </dl>
      </section>
    {/if}
  </div>

  <div class="layout">
    <section class="source" aria-labelledby="source-heading">
      <h2 id="source-heading">Source</h2>
      <div id="editor" tabindex="-1">
        <Editor bind:this={editor} initial={DEFAULT_SOURCE} onchange={onSourceChange} />
      </div>
      <div class="actions">
        <button type="button" onclick={applyFix} disabled={fixDisabled}>Fix</button>
      </div>
      <section aria-labelledby="diagnostics-heading">
        <h2 id="diagnostics-heading">Diagnostics</h2>
        {#if merged.length === 0}
          <p class="quiet">No diagnostics.</p>
        {:else}
          <ul class="diagnostics" aria-label="Diagnostics">
            {#each merged as item, index (index)}
              <li>
                <button type="button" class="diagnostic" data-severity={item.diagnostic.severity} onclick={() => selectDiagnostic(item)}>{accessibleName(item)}</button>
              </li>
            {/each}
          </ul>
        {/if}
      </section>
    </section>

    <section class="output" aria-labelledby="output-heading">
      <h2 id="output-heading">Output</h2>

      <fieldset class="engines">
        <legend>Engine</legend>
        <label>
          <input type="radio" name="engine" value="go" checked={engineChoice === 'go'} disabled={radioDisabled.go} onchange={() => selectEngine('go')} />
          Go
        </label>
        <label>
          <input type="radio" name="engine" value="rust" checked={engineChoice === 'rust'} disabled={radioDisabled.rust} onchange={() => selectEngine('rust')} />
          Rust
        </label>
        <label>
          <input type="radio" name="engine" value="both" checked={engineChoice === 'both'} disabled={radioDisabled.both} onchange={() => selectEngine('both')} />
          Both
        </label>
      </fieldset>

      {#each ENGINE_IDS as id (id)}
        {#if snapshots[id].state === 'error' && !selected.includes(id)}
          <div role="group" aria-label="Recover {ENGINE_NAME[id]} engine">
            <p>{failureText(ENGINE_NAME[id], snapshots[id].message)}</p>
            <button type="button" onclick={() => clients[id]?.retry()}>Retry {ENGINE_NAME[id]} engine</button>
          </div>
        {/if}
      {/each}

      <div class="tabs" role="tablist" aria-label="Output">
        {#each TABS as spec, index (spec.id)}
          <button
            type="button"
            role="tab"
            id="tab-{spec.id}"
            aria-selected={tab === spec.id}
            aria-controls="panel-{spec.id}"
            tabindex={tab === spec.id ? 0 : -1}
            onclick={() => selectTab(spec.id)}
            onkeydown={onTabKey}
            bind:this={tabButtons[index]}>{spec.label}</button
          >
        {/each}
      </div>

      {#each TABS as spec (spec.id)}
        <div role="tabpanel" id="panel-{spec.id}" aria-labelledby="tab-{spec.id}" hidden={tab !== spec.id}>
          {#if tab === spec.id}
            {#if !issuedEmpty && !selected.some((id) => paneContent(views[id], spec.op, latest).slot !== null)}
              <!-- svelte-ignore a11y_no_noninteractive_tabindex -->
              <pre class="sample" role="group" tabindex="0" aria-label="Sample output while the engines load">{sampleText}</pre>
            {/if}
            <div class="panes" data-both={selected.length === 2}>
              {#each selected as id (id)}
                <EnginePane
                  engine={id}
                  tab={spec}
                  snapshot={snapshots[id]}
                  view={views[id]}
                  {latest}
                  svgUrl={svgUrls[id]}
                  heading={selected.length === 2}
                  emptyMessage={issuedEmpty ? EMPTY_MESSAGE : null}
                  onretry={() => clients[id]?.retry()}
                />
              {/each}
            </div>
          {/if}
        </div>
      {/each}
    </section>
  </div>

  <noscript>
    <p>This playground needs JavaScript to render your edits; the sample source and output remain available.</p>
  </noscript>
</main>

<style>
  main {
    position: relative;
    display: flex;
    flex-direction: column;
    gap: var(--gutter);
    min-width: 0;
    max-width: 100%;
    padding: var(--gutter);
  }

  header {
    display: flex;
    flex-direction: column;
    gap: var(--sp-1);
  }

  .skip {
    position: absolute;
    top: var(--sp-2);
    left: var(--sp-2);
    z-index: 1;
    padding: var(--sp-2) var(--sp-3);
    border: var(--stroke) solid var(--emd-border);
    border-radius: var(--radius);
    background: var(--emd-surface);
    color: var(--emd-fg);
    transform: translateY(-400%);
    transition: transform var(--duration) var(--ease);
  }

  .skip:focus {
    transform: translateY(0);
  }

  .toolbar {
    display: flex;
    flex-wrap: wrap;
    align-items: flex-end;
    gap: var(--sp-2);
  }

  .toolbar label,
  .shared {
    display: flex;
    flex-direction: column;
    gap: var(--sp-1);
    font-size: 14px;
    line-height: 20px;
    font-weight: 600;
  }

  .status-area {
    display: flex;
    flex-direction: column;
    gap: var(--sp-2);
    min-width: 0;
  }

  .status {
    display: flex;
    flex-direction: column;
    gap: var(--sp-1);
    min-width: 0;
  }

  .difference {
    padding: var(--sp-2) var(--sp-3);
    border: var(--stroke) solid var(--emd-border);
    border-left: var(--sp-1) solid var(--emd-warning);
    border-radius: var(--radius);
    background: var(--emd-surface);
    overflow: auto;
  }

  .difference dl {
    margin: 0;
  }

  .difference dt {
    font-weight: 600;
  }

  .difference dd {
    margin: 0 0 var(--sp-1);
  }

  code {
    font-family: var(--font-mono);
    font-size: 14px;
    white-space: pre;
  }

  .layout {
    display: grid;
    grid-template-columns: minmax(0, 1fr);
    gap: var(--gutter);
    min-width: 0;
  }

  .source,
  .output {
    display: flex;
    flex-direction: column;
    gap: var(--sp-3);
    min-width: 0;
    max-width: 100%;
  }

  .actions {
    display: flex;
    gap: var(--sp-2);
  }

  .quiet {
    color: var(--emd-muted);
  }

  .diagnostics {
    display: flex;
    flex-direction: column;
    gap: var(--sp-2);
    margin: 0;
    padding: 0;
    list-style: none;
  }

  .diagnostic {
    width: 100%;
    text-align: left;
    border-left: var(--sp-1) solid var(--emd-border);
  }

  .diagnostic[data-severity='error'] {
    border-left-color: var(--emd-error);
  }

  .diagnostic[data-severity='warning'] {
    border-left-color: var(--emd-warning);
  }

  .diagnostic[data-severity='info'] {
    border-left-color: var(--emd-accent);
  }

  .engines {
    display: flex;
    flex-wrap: wrap;
    gap: var(--sp-2) var(--sp-4);
    margin: 0;
    padding: var(--sp-2) var(--sp-3);
    border: var(--stroke) solid var(--emd-border);
    border-radius: var(--radius);
  }

  .engines label {
    display: flex;
    align-items: center;
    gap: var(--sp-2);
    min-height: var(--sp-8);
  }

  .tabs {
    display: flex;
    flex-wrap: wrap;
    gap: var(--sp-1);
    border-bottom: var(--stroke) solid var(--emd-border);
  }

  .tabs [role='tab'] {
    border-color: transparent;
    border-bottom: var(--stroke-emphasis) solid transparent;
    border-radius: var(--radius) var(--radius) 0 0;
    background: transparent;
  }

  .tabs [role='tab'][aria-selected='true'] {
    border-bottom-color: var(--emd-accent);
    font-weight: 600;
  }

  [role='tabpanel'] {
    display: flex;
    flex-direction: column;
    gap: var(--sp-3);
    min-width: 0;
  }

  [role='tabpanel'][hidden] {
    display: none;
  }

  .sample {
    max-width: 100%;
    max-height: 60vh;
    overflow: auto;
    padding: var(--sp-3);
    border: var(--stroke) solid var(--emd-border);
    border-radius: var(--radius);
    background: var(--emd-surface);
  }

  .panes {
    display: grid;
    grid-template-columns: minmax(0, 1fr);
    gap: var(--sp-4);
    min-width: 0;
  }

  @media (min-width: 1024px) {
    .layout {
      grid-template-columns: minmax(0, 2fr) minmax(0, 3fr);
      gap: var(--sp-4);
      align-items: start;
    }

    .toolbar {
      gap: var(--sp-2) var(--sp-4);
    }

    .panes[data-both='true'] {
      grid-template-columns: repeat(2, minmax(0, 1fr));
    }
  }
</style>
