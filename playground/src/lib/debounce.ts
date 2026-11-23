export interface Debounced {
  (): void;
  cancel(): void;
}

export function debounce(action: () => void, delayMs: number): Debounced {
  let timer: ReturnType<typeof setTimeout> | null = null;
  const run = (() => {
    if (timer !== null) {
      clearTimeout(timer);
    }
    timer = setTimeout(() => {
      timer = null;
      action();
    }, delayMs);
  }) as Debounced;
  run.cancel = () => {
    if (timer !== null) {
      clearTimeout(timer);
      timer = null;
    }
  };
  return run;
}
