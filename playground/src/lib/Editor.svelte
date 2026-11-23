<script lang="ts">
import { type Diagnostic as CmDiagnostic, lintGutter, setDiagnostics } from '@codemirror/lint';
import { EditorState } from '@codemirror/state';
import { EditorView } from '@codemirror/view';
import { basicSetup } from 'codemirror';
import { onMount } from 'svelte';
import type { EditorRange } from './diagnostics';

let { initial, onchange }: { initial: string; onchange: (text: string) => void } = $props();

let host: HTMLDivElement | undefined = $state();
let view: EditorView | null = null;
let active = $state(false);

const theme = EditorView.theme({
  '&': {
    color: 'var(--emd-fg)',
    backgroundColor: 'var(--emd-surface)',
    border: 'var(--stroke) solid var(--emd-border)',
    borderRadius: 'var(--radius)',
    maxWidth: '100%',
    minHeight: 'calc(12 * 20px + 2 * var(--sp-2))',
    height: 'clamp(260px, 60vh, 640px)',
  },
  '&.cm-focused': { outline: 'var(--stroke-emphasis) solid var(--emd-accent)', outlineOffset: 'var(--sp-1)' },
  '.cm-scroller': { fontFamily: 'var(--font-mono)', fontSize: '14px', lineHeight: '20px', overflow: 'auto' },
  '.cm-content': { caretColor: 'var(--emd-fg)', padding: 'var(--sp-2) 0' },
  '.cm-cursor, .cm-dropCursor': { borderLeftColor: 'var(--emd-fg)' },
  '.cm-gutters': {
    backgroundColor: 'var(--emd-surface)',
    color: 'var(--emd-muted)',
    borderRight: 'var(--stroke) solid var(--emd-border)',
  },
  '.cm-activeLine': { backgroundColor: 'transparent' },
  '.cm-activeLineGutter': { backgroundColor: 'transparent', color: 'var(--emd-fg)' },
  '.cm-selectionBackground, &.cm-focused > .cm-scroller > .cm-selectionLayer .cm-selectionBackground': {
    backgroundColor: 'var(--emd-accent)',
    opacity: '0.3',
  },
  '.cm-tooltip': {
    backgroundColor: 'var(--emd-surface)',
    color: 'var(--emd-fg)',
    border: 'var(--stroke) solid var(--emd-border)',
  },
  '.cm-diagnostic': { color: 'var(--emd-fg)' },
  '.cm-diagnostic-error': { borderLeftColor: 'var(--emd-error)' },
  '.cm-diagnostic-warning': { borderLeftColor: 'var(--emd-warning)' },
  '.cm-diagnostic-info': { borderLeftColor: 'var(--emd-accent)' },
  '.cm-lint-marker-error, .cm-lint-marker-warning, .cm-lint-marker-info': {
    content: 'normal',
    width: '12px',
    height: '12px',
    boxSizing: 'border-box',
  },
  '.cm-lint-marker-error': { backgroundColor: 'var(--emd-error)', borderRadius: '50%' },
  '.cm-lint-marker-warning': { backgroundColor: 'var(--emd-warning)', borderRadius: '2px' },
  '.cm-lint-marker-info': { border: 'var(--stroke-emphasis) solid var(--emd-accent)', borderRadius: '50%' },
  '.cm-lintRange-error, .cm-lintRange-warning, .cm-lintRange-info': {
    backgroundImage: 'none',
    paddingBottom: '0',
    textDecorationLine: 'underline',
    textDecorationStyle: 'wavy',
    textDecorationThickness: 'var(--stroke-emphasis)',
  },
  '.cm-lintRange-error': { textDecorationColor: 'var(--emd-error)' },
  '.cm-lintRange-warning': { textDecorationColor: 'var(--emd-warning)' },
  '.cm-lintRange-info': { textDecorationColor: 'var(--emd-accent)' },
  '.cm-lintRange-active': { backgroundColor: 'transparent' },
  '.cm-lintPoint-error:after': { borderBottomColor: 'var(--emd-error)' },
  '.cm-lintPoint-warning:after': { borderBottomColor: 'var(--emd-warning)' },
  '.cm-lintPoint-info:after': { borderBottomColor: 'var(--emd-accent)' },
});

onMount(() => {
  if (host === undefined) {
    return;
  }
  view = new EditorView({
    parent: host,
    state: EditorState.create({
      doc: initial,
      extensions: [
        basicSetup,
        lintGutter(),
        theme,
        EditorView.contentAttributes.of({ 'aria-label': 'Mermaid source', spellcheck: 'false' }),
        EditorView.updateListener.of((update) => {
          if (update.docChanged) {
            onchange(update.state.doc.toString());
          }
        }),
      ],
    }),
  });
  active = true;
  return () => {
    view?.destroy();
    view = null;
    active = false;
  };
});

export function getText(): string {
  return view?.state.doc.toString() ?? initial;
}

export function setText(text: string): void {
  if (view === null || view.state.doc.toString() === text) {
    return;
  }
  view.dispatch({ changes: { from: 0, to: view.state.doc.length, insert: text } });
}

export function showDiagnostics(ranges: readonly EditorRange[]): void {
  if (view === null) {
    return;
  }
  const length = view.state.doc.length;
  const items: CmDiagnostic[] = ranges.map((range) => ({
    from: Math.min(range.from, length),
    to: Math.min(Math.max(range.to, range.from), length),
    severity: range.severity,
    message: range.message,
    source: range.source,
  }));
  view.dispatch(setDiagnostics(view.state, items));
}

export function select(from: number, to: number): void {
  if (view === null) {
    return;
  }
  const length = view.state.doc.length;
  const anchor = Math.min(from, length);
  view.dispatch({ selection: { anchor, head: Math.min(Math.max(to, anchor), length) }, scrollIntoView: true });
  view.focus();
}

export function focus(): boolean {
  if (view === null) {
    return false;
  }
  view.focus();
  return true;
}
</script>

{#if !active}
  <!-- svelte-ignore a11y_no_noninteractive_tabindex -->
  <pre class="fallback" role="group" aria-label="Mermaid source" tabindex="0">{initial}</pre>
{/if}
<div class="host" bind:this={host} hidden={!active}></div>

<style>
  .fallback {
    min-height: calc(12 * 20px + 2 * var(--sp-2));
    max-width: 100%;
    overflow: auto;
    padding: var(--sp-2) var(--sp-3);
    border: var(--stroke) solid var(--emd-border);
    border-radius: var(--radius);
    background: var(--emd-surface);
  }

  .host {
    min-width: 0;
    max-width: 100%;
  }
</style>
