import { describe, expect, it, vi } from 'vitest';
import { DEFAULT_SOURCE } from './defaults';
import { compressionSupported, decodeShare, encodeShare, fragmentPayload, type SharePayload, shareUrl } from './share';

const payload: SharePayload = {
  src: DEFAULT_SOURCE,
  opt: { theme: 'nord', background: '#fff', charset: 'ascii', max_width: 80 },
};

describe('share link codec', () => {
  it('has compression streams', () => {
    expect(compressionSupported()).toBe(true);
  });

  it('round-trips the default payload', async () => {
    const encoded = await encodeShare(payload);
    expect(encoded).toMatch(/^[A-Za-z0-9_-]+$/);
    expect(await decodeShare(encoded)).toEqual(payload);
  });

  it('round-trips multibyte and large sources without padding characters', async () => {
    const src = `flowchart LR\n  A["héllo 🌍 café"] --> B\n${'  B --> C\n'.repeat(5000)}`;
    const value: SharePayload = {
      src,
      opt: { theme: 'elegant-light', background: null, charset: 'unicode', max_width: null },
    };
    const encoded = await encodeShare(value);
    expect(encoded).not.toContain('=');
    expect(encoded).not.toContain('+');
    expect(encoded).not.toContain('/');
    expect(await decodeShare(encoded)).toEqual(value);
  });

  it('round-trips an empty source', async () => {
    const value: SharePayload = {
      src: '',
      opt: { theme: 'elegant-light', background: null, charset: 'unicode', max_width: null },
    };
    expect(await decodeShare(await encodeShare(value))).toEqual(value);
  });

  it('rejects text that is not base64url', async () => {
    expect(await decodeShare('not base64!')).toBeNull();
    expect(await decodeShare('a')).toBeNull();
  });

  it('rejects bytes that do not inflate', async () => {
    expect(await decodeShare('AAAAAAAA')).toBeNull();
  });

  it('refuses a short link that inflates to megabytes', async () => {
    const value: SharePayload = {
      src: ' '.repeat(2 ** 21),
      opt: { theme: 'elegant-light', background: null, charset: 'unicode', max_width: null },
    };
    const encoded = await encodeShare(value);
    expect(encoded.length).toBeLessThan(8192);
    expect(await decodeShare(encoded)).toBeNull();
  });

  async function encodeRaw(json: string): Promise<string> {
    return encodeBytes(new TextEncoder().encode(json));
  }

  async function encodeBytes(input: Uint8Array<ArrayBuffer>): Promise<string> {
    const stream = new Blob([input]).stream().pipeThrough(new CompressionStream('deflate-raw'));
    const bytes = new Uint8Array(await new Response(stream).arrayBuffer());
    let binary = '';
    for (let offset = 0; offset < bytes.length; offset += 0x8000) {
      binary += String.fromCharCode(...bytes.subarray(offset, offset + 0x8000));
    }
    return btoa(binary).replace(/\+/g, '-').replace(/\//g, '_').replace(/=+$/, '');
  }

  it('rejects JSON that is not the payload shape', async () => {
    expect(await decodeShare(await encodeRaw('not json'))).toBeNull();
    expect(await decodeShare(await encodeRaw('[]'))).toBeNull();
    expect(await decodeShare(await encodeRaw('{"src":1,"opt":{}}'))).toBeNull();
    expect(await decodeShare(await encodeRaw('{"src":"x"}'))).toBeNull();
    expect(await decodeShare(await encodeRaw('{"src":"x","opt":{"theme":"missing"}}'))).toBeNull();
    expect(await decodeShare(await encodeRaw('{"src":"x","opt":{"charset":"latin1"}}'))).toBeNull();
    expect(await decodeShare(await encodeRaw('{"src":"x","opt":{"max_width":-1}}'))).toBeNull();
    expect(await decodeShare(await encodeRaw('{"src":"x","opt":{"background":"red"}}'))).toBeNull();
    expect(await decodeShare(await encodeRaw('{"src":"x","opt":{"extra":1}}'))).toBeNull();
  });

  it('rejects a compressed payload larger than the decoded byte limit', async () => {
    const json = JSON.stringify({ src: 'x'.repeat(2 * 1024 * 1024), opt: {} });
    const encoded = await encodeRaw(json);
    expect(encoded.length).toBeLessThan(4096);
    expect(await decodeShare(encoded)).toBeNull();
  });

  it('refuses to encode a payload that cannot be decoded within the limit', async () => {
    await expect(encodeShare({ ...payload, src: 'x'.repeat(2 * 1024 * 1024) })).rejects.toThrow(
      'Shared diagrams must fit within 2 MiB of JSON.',
    );
  });

  it('accepts exactly 2 MiB of UTF-8 JSON and rejects one byte more', async () => {
    const limit = 2 * 1024 * 1024;
    const overhead = new TextEncoder().encode(JSON.stringify({ ...payload, src: '' })).byteLength;
    const contentBytes = limit - overhead;
    const value: SharePayload = {
      ...payload,
      src: 'é'.repeat(Math.floor(contentBytes / 2)) + 'x'.repeat(contentBytes % 2),
    };
    expect(new TextEncoder().encode(JSON.stringify(value)).byteLength).toBe(limit);
    expect(await decodeShare(await encodeShare(value))).toEqual(value);

    const oversized = { ...value, src: `${value.src}x` };
    expect(new TextEncoder().encode(JSON.stringify(oversized)).byteLength).toBe(limit + 1);
    expect(await decodeShare(await encodeRaw(JSON.stringify(oversized)))).toBeNull();
    await expect(encodeShare(oversized)).rejects.toBeInstanceOf(RangeError);
  });

  it('rejects oversized base64 before decoding and accepts the encoded boundary', async () => {
    const decodeBase64 = vi.spyOn(globalThis, 'atob');
    try {
      expect(await decodeShare('A'.repeat(4 * 1024 * 1024 + 1))).toBeNull();
      expect(decodeBase64).not.toHaveBeenCalled();
      expect(await decodeShare('A'.repeat(4 * 1024 * 1024))).toBeNull();
      expect(decodeBase64).toHaveBeenCalledTimes(1);
    } finally {
      decodeBase64.mockRestore();
    }
  });

  it('cancels decompression before reading beyond an oversized chunk', async () => {
    let reads = 0;
    const cancel = vi.fn();
    class OversizedStream {
      readonly readable = new ReadableStream<Uint8Array>(
        {
          pull(controller) {
            reads += 1;
            controller.enqueue(new Uint8Array(2 * 1024 * 1024 + 1));
          },
          cancel,
        },
        { highWaterMark: 0 },
      );
      readonly writable = new WritableStream<Uint8Array>();
    }
    vi.stubGlobal('DecompressionStream', OversizedStream);
    try {
      expect(await decodeShare('AA')).toBeNull();
      expect(reads).toBe(1);
      expect(cancel).toHaveBeenCalledTimes(1);
    } finally {
      vi.unstubAllGlobals();
    }
  });

  it('rejects malformed UTF-8 instead of repairing it into valid JSON', async () => {
    const prefix = new TextEncoder().encode('{"src":"');
    const suffix = new TextEncoder().encode('","opt":{}}');
    const encoded = await encodeBytes(new Uint8Array([...prefix, 0xff, ...suffix]));
    expect(await decodeShare(encoded)).toBeNull();
  });

  it('fills absent option keys with defaults', async () => {
    expect(await decodeShare(await encodeRaw('{"src":"x","opt":{}}'))).toEqual({
      src: 'x',
      opt: { theme: 'elegant-light', background: null, charset: 'unicode', max_width: null },
    });
  });

  it('reads only the s= fragment', () => {
    expect(fragmentPayload('#s=abc')).toBe('abc');
    expect(fragmentPayload('s=abc')).toBe('abc');
    expect(fragmentPayload('#editor')).toBeNull();
    expect(fragmentPayload('')).toBeNull();
  });

  it('changes only the hash of the page URL', () => {
    const url = shareUrl('https://example.org/elegant-mermaid/?x=1#old', 'abc');
    expect(url).toBe('https://example.org/elegant-mermaid/?x=1#s=abc');
  });
});
