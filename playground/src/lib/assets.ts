import { asset } from '$app/paths';

export function staticUrl(file: string): string {
  return asset(file as Parameters<typeof asset>[0]);
}

export const ENGINE_URLS = {
  go: { loader: 'wasm/wasm_exec.js', wasm: 'wasm/emd-go.wasm' },
  rust: { loader: 'wasm/emd-rs/elegant_mermaid_wasm.js', wasm: 'wasm/emd-rs/elegant_mermaid_wasm_bg.wasm' },
} as const;
