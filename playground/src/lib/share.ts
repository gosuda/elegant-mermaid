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
const MAX_JSON_BYTES = 2 * 1024 * 1024;
// Leave room for deflate framing and incompressible input before base64 expansion.
const MAX_ENCODED_CHARACTERS = 4 * 1024 * 1024;
const MAX_COMPRESSED_BYTES = (MAX_ENCODED_CHARACTERS / 4) * 3;
const SIZE_ERROR = 'Shared diagrams must fit within 2 MiB of JSON.';

function toBase64Url(bytes: Uint8Array): string {
  let binary = '';
  const step = 0x8000;
  for (let offset = 0; offset < bytes.length; offset += step) {
    binary += String.fromCharCode(...bytes.subarray(offset, offset + step));
  }
  return btoa(binary).replace(/\+/g, '-').replace(/\//g, '_').replace(/=+$/, '');
}

function fromBase64Url(text: string): Uint8Array | null {
  if (text.length > MAX_ENCODED_CHARACTERS || !/^[A-Za-z0-9_-]*$/.test(text) || text.length % 4 === 1) {
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

async function pipe(
  bytes: Uint8Array<ArrayBuffer>,
  stream: CompressionStream | DecompressionStream,
  limit: number,
): Promise<Uint8Array> {
  const reader = new Blob([bytes]).stream().pipeThrough(stream).getReader();
  const chunks: Uint8Array[] = [];
  let length = 0;
  try {
    for (;;) {
      const { done, value } = await reader.read();
      if (done) {
        break;
      }
      if (value.byteLength > limit - length) {
        await reader.cancel();
        throw new RangeError(SIZE_ERROR);
      }
      chunks.push(value);
      length += value.byteLength;
    }
  } finally {
    reader.releaseLock();
  }
  const output = new Uint8Array(length);
  let offset = 0;
  for (const chunk of chunks) {
    output.set(chunk, offset);
    offset += chunk.byteLength;
  }
  return output;
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
  if (json.length > MAX_JSON_BYTES) {
    throw new RangeError(SIZE_ERROR);
  }
  const bytes = new TextEncoder().encode(json);
  if (bytes.byteLength > MAX_JSON_BYTES) {
    throw new RangeError(SIZE_ERROR);
  }
  const deflated = await pipe(bytes, new CompressionStream('deflate-raw'), MAX_COMPRESSED_BYTES);
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
    const bytes = await pipe(new Uint8Array(deflated), new DecompressionStream('deflate-raw'), MAX_JSON_BYTES);
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
