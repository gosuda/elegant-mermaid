<script lang="ts">
import type { EngineSnapshot } from './engine-client';
import { ENGINE_NAME, type EngineId } from './protocol';
import { type EngineView, failureText, paneContent, progressText, type TabSpec } from './view';

interface Props {
  engine: EngineId;
  tab: TabSpec;
  snapshot: EngineSnapshot;
  view: EngineView;
  latest: number;
  svgUrl: string | null;
  heading: boolean;
  emptyMessage: string | null;
  onretry: () => void;
}

let { engine, tab, snapshot, view, latest, svgUrl, heading, emptyMessage, onretry }: Props = $props();

const name = $derived(ENGINE_NAME[engine]);
const content = $derived(paneContent(view, tab.op, latest));
</script>

<section class="pane" data-engine={engine} data-state={snapshot.state} aria-label="{name} {tab.label}">
  {#if heading}
    <h3>{name}</h3>
  {/if}

  {#if snapshot.state === 'loading'}
    <div class="loading">
      {#if snapshot.total !== null && snapshot.loaded <= snapshot.total}
        <progress aria-label="{name} engine download" value={snapshot.loaded} max={snapshot.total}></progress>
      {:else}
        <progress aria-label="{name} engine download"></progress>
      {/if}
      <span>{progressText(snapshot.loaded, snapshot.total)}</span>
    </div>
  {:else if snapshot.state === 'error'}
    <div class="failure">
      <p>{failureText(name, snapshot.message)}</p>
      <button type="button" onclick={onretry}>Retry {name} engine</button>
    </div>
  {/if}

  {#if emptyMessage !== null}
    <p class="note">{emptyMessage}</p>
  {:else}
    {#if content.stale && content.slot !== null}
      <p class="stale"><strong>Showing the last valid revision</strong> <span>Revision {content.slot.revision} (stale)</span></p>
    {:else if content.invalid}
      <p class="note">No valid output yet. Fix the diagnostics.</p>
    {/if}

    {#if content.slot !== null}
      {#if tab.id === 'svg'}
        <!-- svelte-ignore a11y_no_noninteractive_tabindex -->
        <div class="scroll" role="group" tabindex="0" aria-label="{name} SVG output">
          {#if svgUrl !== null}
            <img src={svgUrl} alt="{name} SVG for revision {content.slot.revision}" />
          {/if}
        </div>
      {:else}
        <!-- svelte-ignore a11y_no_noninteractive_tabindex -->
        <pre class="scroll" role="group" tabindex="0" aria-label="{name} {tab.label} output">{content.slot.output}</pre>
      {/if}
    {/if}
  {/if}
</section>

<style>
  .pane {
    display: flex;
    flex-direction: column;
    gap: var(--sp-2);
    min-width: 0;
    max-width: 100%;
  }

  .loading {
    display: flex;
    flex-wrap: wrap;
    align-items: center;
    gap: var(--sp-2);
  }

  .failure {
    display: flex;
    flex-direction: column;
    align-items: flex-start;
    gap: var(--sp-2);
    padding: var(--sp-3);
    border: var(--stroke) solid var(--emd-border);
    border-left: var(--sp-1) solid var(--emd-error);
    border-radius: var(--radius);
    background: var(--emd-surface);
  }

  .stale {
    display: flex;
    flex-wrap: wrap;
    gap: var(--sp-2);
    padding: var(--sp-2) var(--sp-3);
    border: var(--stroke) solid var(--emd-border);
    border-left: var(--sp-1) solid var(--emd-warning);
    border-radius: var(--radius);
    background: var(--emd-surface);
  }

  .note {
    padding: var(--sp-2) var(--sp-3);
    border: var(--stroke) solid var(--emd-border);
    border-radius: var(--radius);
    background: var(--emd-surface);
  }

  .scroll {
    min-width: 0;
    max-width: 100%;
    max-height: 60vh;
    overflow: auto;
    padding: var(--sp-3);
    border: var(--stroke) solid var(--emd-border);
    border-radius: var(--radius);
    background: var(--emd-surface);
  }

  img {
    display: block;
    max-width: 100%;
    height: auto;
  }
</style>
