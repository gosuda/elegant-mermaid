import { CHARSETS, type Charset, THEMES } from './defaults';

export interface ShareOptions {
  theme: string;
  background: string | null;
  charset: Charset;
  max_width: number | null;
}

export interface SharePayload {
  src: string;
  opt: ShareOptions;
}

const PREFIX = 's=';
const MAX_PAYLOAD_BYTES = 1 << 20;

function toBase64Url(bytes: Uint8Array): string {
  let binary = '';
  const step = 0x8000;
  for (let offset = 0; offset < bytes.length; offset += step) {
    binary += String.fromCharCode(...bytes.subarray(offset, offset + step));
  }
  return btoa(binary).replace(/\+/g, '-').replace(/\//g, '_').replace(/=+$/, '');
}

function fromBase64Url(text: string): Uint8Array | null {
  if (!/^[A-Za-z0-9_-]*$/.test(text) || text.length % 4 === 1) {
    return null;
  }
  const padded = text.replace(/-/g, '+').replace(/_/g, '/') + '='.repeat((4 - (text.length % 4)) % 4);
  try {
    const binary = atob(padded);
    const bytes = new Uint8Array(binary.length);
    for (let index = 0; index < binary.length; index += 1) {
      bytes[index] = binary.charCodeAt(index);
    }
    return bytes;
  } catch {
    return null;
  }
}

async function deflate(bytes: Uint8Array<ArrayBuffer>): Promise<Uint8Array> {
  const output = new Blob([bytes]).stream().pipeThrough(new CompressionStream('deflate-raw'));
  return new Uint8Array(await new Response(output).arrayBuffer());
}

async function inflate(bytes: Uint8Array<ArrayBuffer>): Promise<Uint8Array | null> {
  const reader = new Blob([bytes]).stream().pipeThrough(new DecompressionStream('deflate-raw')).getReader();
  const chunks: Uint8Array[] = [];
  let total = 0;
  for (;;) {
    const { done, value } = await reader.read();
    if (done) {
      break;
    }
    total += value.byteLength;
    if (total > MAX_PAYLOAD_BYTES) {
      await reader.cancel();
      return null;
    }
    chunks.push(value);
  }
  const inflated = new Uint8Array(total);
  let offset = 0;
  for (const chunk of chunks) {
    inflated.set(chunk, offset);
    offset += chunk.byteLength;
  }
  return inflated;
}

export function compressionSupported(): boolean {
  return typeof CompressionStream === 'function' && typeof DecompressionStream === 'function';
}

export async function encodeShare(payload: SharePayload): Promise<string> {
  const json = JSON.stringify({
    src: payload.src,
    opt: {
      theme: payload.opt.theme,
      background: payload.opt.background,
      charset: payload.opt.charset,
      max_width: payload.opt.max_width,
    },
  });
  const deflated = await deflate(new TextEncoder().encode(json));
  return toBase64Url(deflated);
}

function parseOptions(value: unknown): ShareOptions | null {
  if (typeof value !== 'object' || value === null || Array.isArray(value)) {
    return null;
  }
  const record = value as Record<string, unknown>;
  const known = new Set(['theme', 'background', 'charset', 'max_width']);
  if (Object.keys(record).some((key) => !known.has(key))) {
    return null;
  }
  const theme = record.theme ?? 'elegant-light';
  const background = record.background ?? null;
  const charset = record.charset ?? 'unicode';
  const maxWidth = record.max_width ?? null;
  if (typeof theme !== 'string' || !(THEMES as readonly string[]).includes(theme)) {
    return null;
  }
  if (
    background !== null &&
    (typeof background !== 'string' || !/^#([0-9a-fA-F]{3}|[0-9a-fA-F]{6})$/.test(background))
  ) {
    return null;
  }
  if (typeof charset !== 'string' || !(CHARSETS as readonly string[]).includes(charset)) {
    return null;
  }
  if (maxWidth !== null && (typeof maxWidth !== 'number' || !Number.isInteger(maxWidth) || maxWidth < 0)) {
    return null;
  }
  return { theme, background, charset: charset as Charset, max_width: maxWidth };
}

export async function decodeShare(encoded: string): Promise<SharePayload | null> {
  const deflated = fromBase64Url(encoded);
  if (deflated === null) {
    return null;
  }
  let json: string;
  try {
    const bytes = await inflate(new Uint8Array(deflated));
    if (bytes === null) {
      return null;
    }
    json = new TextDecoder('utf-8', { fatal: true }).decode(bytes);
  } catch {
    return null;
  }
  let parsed: unknown;
  try {
    parsed = JSON.parse(json);
  } catch {
    return null;
  }
  if (typeof parsed !== 'object' || parsed === null || Array.isArray(parsed)) {
    return null;
  }
  const record = parsed as Record<string, unknown>;
  if (typeof record.src !== 'string') {
    return null;
  }
  const opt = parseOptions(record.opt);
  return opt === null ? null : { src: record.src, opt };
}

export function fragmentPayload(hash: string): string | null {
  const body = hash.startsWith('#') ? hash.slice(1) : hash;
  return body.startsWith(PREFIX) ? body.slice(PREFIX.length) : null;
}

export function shareUrl(href: string, encoded: string): string {
  const url = new URL(href);
  url.hash = PREFIX + encoded;
  return url.href;
}
