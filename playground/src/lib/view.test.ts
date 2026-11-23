import { describe, expect, it } from 'vitest';
import { emptyView, failureText, nextTab, paneContent, progressText } from './view';

describe('paneContent', () => {
  it('shows the last valid output without a stale label while the answer is pending', () => {
    const view = { ...emptyView(), revision: 2, valid: { render_svg: { revision: 1, output: '<svg/>' } } };
    expect(paneContent(view, 'render_svg', 2)).toEqual({
      slot: { revision: 1, output: '<svg/>' },
      stale: false,
      invalid: false,
    });
  });

  it('marks the last valid output stale when the newest answer failed', () => {
    const view = {
      ...emptyView(),
      revision: 3,
      answers: { render_svg: { ok: false, output: '' } },
      valid: { render_svg: { revision: 2, output: '<svg/>' } },
    };
    expect(paneContent(view, 'render_svg', 3)).toEqual({
      slot: { revision: 2, output: '<svg/>' },
      stale: true,
      invalid: false,
    });
  });

  it('reports an invalid state when no valid output exists', () => {
    const view = { ...emptyView(), revision: 1, answers: { layout: { ok: false, output: '' } } };
    expect(paneContent(view, 'layout', 1)).toEqual({ slot: null, stale: false, invalid: true });
  });

  it('never marks the check output stale', () => {
    const view = {
      ...emptyView(),
      revision: 1,
      answers: { check: { ok: false, output: '{}' } },
      valid: { check: { revision: 1, output: '{}' } },
    };
    expect(paneContent(view, 'check', 1)).toEqual({
      slot: { revision: 1, output: '{}' },
      stale: false,
      invalid: false,
    });
  });

  it('ignores answers of an older revision', () => {
    const view = { ...emptyView(), revision: 1, answers: { layout: { ok: false, output: '' } } };
    expect(paneContent(view, 'layout', 2).invalid).toBe(false);
  });
});

describe('nextTab', () => {
  it('wraps with the arrow keys and jumps with Home and End', () => {
    expect(nextTab('svg', 'ArrowRight')).toBe('text');
    expect(nextTab('diagnostics', 'ArrowRight')).toBe('svg');
    expect(nextTab('svg', 'ArrowLeft')).toBe('diagnostics');
    expect(nextTab('layout', 'Home')).toBe('svg');
    expect(nextTab('svg', 'End')).toBe('diagnostics');
    expect(nextTab('svg', 'x')).toBeNull();
  });
});

describe('loading text', () => {
  it('words the failure with the retry control name', () => {
    expect(failureText('Go', 'timed out after 30 seconds')).toBe(
      'The Go engine could not load: timed out after 30 seconds. Check your connection, then select Retry Go engine.',
    );
    expect(failureText('Rust', 'HTTP 404.')).toBe(
      'The Rust engine could not load: HTTP 404. Check your connection, then select Retry Rust engine.',
    );
  });

  it('shows MiB with one decimal and falls back when the total is unusable', () => {
    expect(progressText(1572864, 5242880)).toBe('1.5 of 5.0 MiB');
    expect(progressText(1572864, null)).toBe('1.5 MiB');
    expect(progressText(6291456, 5242880)).toBe('6.0 MiB');
  });
});
