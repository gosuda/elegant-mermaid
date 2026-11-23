import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { debounce } from './debounce';
import { DEBOUNCE_MS } from './protocol';

describe('debounce', () => {
  beforeEach(() => {
    vi.useFakeTimers();
  });
  afterEach(() => {
    vi.useRealTimers();
  });

  it('uses 150 ms', () => {
    expect(DEBOUNCE_MS).toBe(150);
  });

  it('runs once after the quiet period', () => {
    const action = vi.fn();
    const run = debounce(action, DEBOUNCE_MS);
    run();
    vi.advanceTimersByTime(100);
    run();
    vi.advanceTimersByTime(149);
    expect(action).not.toHaveBeenCalled();
    vi.advanceTimersByTime(1);
    expect(action).toHaveBeenCalledTimes(1);
  });

  it('can be cancelled', () => {
    const action = vi.fn();
    const run = debounce(action, DEBOUNCE_MS);
    run();
    run.cancel();
    vi.advanceTimersByTime(1000);
    expect(action).not.toHaveBeenCalled();
  });
});
