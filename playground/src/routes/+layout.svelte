<script lang="ts">
import '../lib/tokens.css';
import '../lib/app.css';
import type { Snippet } from 'svelte';
import { staticUrl } from '../lib/assets';

let { children }: { children: Snippet } = $props();

const fontFaces = [
  { weight: 400, file: 'fonts/Inter-Regular.woff2' },
  { weight: 600, file: 'fonts/Inter-SemiBold.woff2' },
]
  .map(
    ({ weight, file }) =>
      `@font-face{font-family:'Inter';font-style:normal;font-weight:${weight};font-display:swap;src:url('${staticUrl(file)}') format('woff2');}`,
  )
  .join('');
</script>

<svelte:head>
  {@html `<style>${fontFaces}</style>`}
</svelte:head>

{@render children()}
