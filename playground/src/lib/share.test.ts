import { describe, expect, it } from 'vitest';
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
    const src = `flowchart LR\n  A["héllo 🌍 世界"] --> B\n${'  B --> C\n'.repeat(5000)}`;
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

  async function encodeRaw(json: string): Promise<string> {
    const stream = new Blob([new TextEncoder().encode(json)])
      .stream()
      .pipeThrough(new CompressionStream('deflate-raw'));
    const bytes = new Uint8Array(await new Response(stream).arrayBuffer());
    return btoa(String.fromCharCode(...bytes))
      .replace(/\+/g, '-')
      .replace(/\//g, '_')
      .replace(/=+$/, '');
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
