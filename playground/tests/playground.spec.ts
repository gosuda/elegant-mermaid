import { expect, type Locator, type Page, test } from '@playwright/test';

declare const process: { env: Record<string, string | undefined> };

const basePath = process.env.BASE_PATH ?? '';

const DEFAULT_FIRST_LINE = 'flowchart LR';
const EMPTY_MESSAGE = 'Empty diagram: add a Mermaid header such as flowchart TD; waiting for changes';
const IDENTICAL = 'Layout: identical · Text: identical';
const BROKEN_SOURCE = 'flowchart LR\n A[x --> B';

type Engine = 'go' | 'rust';

function pane(page: Page, engine: Engine, tab = 'svg'): Locator {
  return page.locator(`#panel-${tab} [data-engine="${engine}"]`);
}

function comparison(page: Page): Locator {
  return page.getByTestId('comparison');
}

async function openPlayground(page: Page): Promise<void> {
  await page.goto('./');
  await expect(pane(page, 'go')).toHaveAttribute('data-state', 'ready');
  await expect(pane(page, 'rust')).toHaveAttribute('data-state', 'ready');
  await expect(comparison(page)).toHaveText(IDENTICAL);
}

async function setSource(page: Page, text: string): Promise<void> {
  await page.locator('.cm-content').click();
  await page.keyboard.press('ControlOrMeta+A');
  if (text === '') {
    await page.keyboard.press('Backspace');
  } else {
    await page.keyboard.insertText(text);
  }
}

async function svgText(page: Page, engine: Engine): Promise<string> {
  const src = await pane(page, engine).locator('img').getAttribute('src');
  return page.evaluate(async (url) => (await fetch(url as string)).text(), src);
}

test.describe('engines and output', () => {
  test('both engines render the default source from built URLs', async ({ page }) => {
    const urls: string[] = [];
    page.on('request', (request) => urls.push(request.url()));
    await openPlayground(page);
    for (const engine of ['go', 'rust'] as const) {
      const image = pane(page, engine).locator('img');
      await expect(image).toBeVisible();
      const label = engine === 'go' ? 'Go' : 'Rust';
      await expect(image).toHaveAttribute('alt', new RegExp(`^${label} SVG for revision \\d+$`));
      expect(await image.getAttribute('src')).toMatch(/^blob:/);
      await expect(page.getByLabel(`${label} engine download`)).toHaveCount(0);
    }
    const engineUrls = urls.filter((url) => /wasm_exec\.js|\.wasm$|elegant_mermaid_wasm\.js$/.test(url));
    expect(engineUrls.length).toBeGreaterThanOrEqual(4);
    for (const url of engineUrls) {
      expect(new URL(url).pathname.startsWith(`${basePath}/wasm/`)).toBe(true);
    }
  });

  test('typing a diagram updates both panes and the comparison', async ({ page }) => {
    await openPlayground(page);
    await setSource(page, 'flowchart LR\n A --> B');
    for (const engine of ['go', 'rust'] as const) {
      await expect.poll(async () => svgText(page, engine)).toMatch(/>A</);
      await expect.poll(async () => svgText(page, engine)).toMatch(/>B</);
    }
    await expect(comparison(page)).toHaveText(IDENTICAL);
  });

  test('an invalid revision keeps the last valid output and marks it stale', async ({ page }) => {
    await openPlayground(page);
    await setSource(page, BROKEN_SOURCE);
    await expect(page.locator('.cm-lint-marker')).toHaveCount(1);
    const diagnostic = page.getByRole('button', {
      name: /^Go and Rust error [a-z0-9-]+\/[a-z0-9-]+, line 2, column \d+: /,
    });
    await expect(diagnostic).toHaveCount(1);
    await expect(page.getByText('Showing the last valid revision')).toHaveCount(2);
    await expect(page.getByText(/^Revision \d+ \(stale\)$/)).toHaveCount(2);
    await expect(pane(page, 'go').locator('img')).toBeVisible();
    await expect(pane(page, 'rust').locator('img')).toBeVisible();
    await expect(comparison(page)).toHaveText('Comparison unavailable: current source has errors');
    await expect(page.getByText('Showing the last valid revision').first()).toHaveCSS('opacity', '1');
  });

  test('a diagnostic button selects its span in the editor', async ({ page }) => {
    await openPlayground(page);
    await setSource(page, BROKEN_SOURCE);
    const diagnostic = page.getByRole('button', { name: /^Go and Rust error / });
    await diagnostic.focus();
    await page.keyboard.press('Enter');
    await expect(page.locator('.cm-content')).toBeFocused();
  });

  test('the Fix control applies safe fixes with the Go engine', async ({ page }) => {
    await openPlayground(page);
    await setSource(page, 'flowchart LR\n  A -> B\n');
    await expect(page.getByRole('button', { name: /^Go and Rust error / })).toBeVisible();
    await page.getByRole('button', { name: 'Fix', exact: true }).click();
    await expect(page.locator('.cm-content')).toContainText('A --> B');
  });

  test('an empty editor shows the empty message and the empty-source diagnostic', async ({ page }) => {
    await openPlayground(page);
    await setSource(page, '');
    await expect(page.getByText(EMPTY_MESSAGE)).toHaveCount(2);
    await expect(
      page.getByRole('button', {
        name: 'Go and Rust error common/empty-source, line 1, column 1: source is empty',
      }),
    ).toBeVisible();
    await expect(comparison(page)).toHaveText('Comparison unavailable: current source has errors');
  });

  test('a failing engine does not block the other and can be retried', async ({ page }) => {
    await page.route('**/emd-rs/*.wasm', (route) => route.abort());
    await page.goto('./');
    await expect(pane(page, 'go')).toHaveAttribute('data-state', 'ready');
    await expect(pane(page, 'rust')).toHaveAttribute('data-state', 'error');
    await expect(pane(page, 'rust')).toContainText('The Rust engine could not load:');
    await expect(pane(page, 'rust')).toContainText('Check your connection, then select Retry Rust engine.');
    await expect(pane(page, 'go').locator('img')).toBeVisible();
    await expect(comparison(page)).toHaveText('Comparison unavailable: Rust engine failed');
    await expect(page.getByRole('radio', { name: 'Rust' })).toBeDisabled();
    await expect(page.getByRole('radio', { name: 'Both' })).toBeDisabled();
    await expect(page.getByRole('radio', { name: 'Go', exact: true })).toBeEnabled();
    await page.unroute('**/emd-rs/*.wasm');
    await page.getByRole('button', { name: 'Retry Rust engine' }).click();
    await expect(pane(page, 'rust')).toHaveAttribute('data-state', 'ready');
    await expect(comparison(page)).toHaveText(IDENTICAL);
    await expect(page.getByRole('radio', { name: 'Both' })).toBeEnabled();
  });

  test('a failed engine remains recoverable after selecting the healthy engine', async ({ page }) => {
    await page.route('**/emd-rs/*.wasm', (route) => route.abort());
    await page.goto('./');
    await expect(pane(page, 'go')).toHaveAttribute('data-state', 'ready');
    await expect(pane(page, 'rust')).toHaveAttribute('data-state', 'error');
    await page.getByRole('radio', { name: 'Go', exact: true }).check();
    await expect(pane(page, 'rust')).toHaveCount(0);
    await page.unroute('**/emd-rs/*.wasm');
    await page.getByRole('button', { name: 'Retry Rust engine' }).click();
    await expect(page.getByRole('radio', { name: 'Both' })).toBeEnabled();
    await page.getByRole('radio', { name: 'Both' }).check();
    await expect(comparison(page)).toHaveText(IDENTICAL);
  });

  test('renders when Promise.withResolvers is absent in both realms', async ({ page }) => {
    await page.addInitScript(() => {
      Object.defineProperty(Promise, 'withResolvers', { configurable: true, value: undefined });
    });
    let workerRequests = 0;
    await page.route(/engine(?:[.-])worker.*\.js(?:\?.*)?$/, async (route) => {
      workerRequests += 1;
      const response = await route.fetch();
      const prefix = [
        "Object.defineProperty(Promise, 'withResolvers', { configurable: true, value: undefined });",
        "Object.defineProperty(globalThis, 'emdCall', { configurable: true, set(value) {",
        "  setTimeout(() => Object.defineProperty(globalThis, 'emdCall', { configurable: true, writable: true, value }), 25);",
        '} });',
      ].join('\n');
      await route.fulfill({
        response,
        body: `${prefix}\n${await response.text()}`,
      });
    });
    await openPlayground(page);
    expect(workerRequests).toBe(2);
  });

  test('a stalled download shows a native progress element named for its engine', async ({ page }) => {
    await page.route('**/emd-go.wasm', async (route) => {
      const { promise, resolve } = Promise.withResolvers<void>();
      setTimeout(resolve, 2500);
      await promise;
      await route.continue();
    });
    await page.goto('./');
    await expect(page.getByRole('progressbar', { name: 'Go engine download' })).toBeVisible();
    await expect(pane(page, 'go')).toHaveAttribute('data-state', 'ready');
  });
});

test.describe('share links', () => {
  test('copies a link that restores source and options', async ({ page, context }) => {
    await context.grantPermissions(['clipboard-read', 'clipboard-write']);
    await openPlayground(page);
    await setSource(page, 'flowchart TB\n  X --> Y\n');
    await page.getByLabel('Theme').selectOption('nord');
    await page.getByLabel('Charset').selectOption('ascii');
    await page.getByRole('button', { name: 'Copy link' }).click();
    await expect(page.getByRole('status')).toContainText('Link copied');
    const link = await page.evaluate(() => navigator.clipboard.readText());
    const url = new URL(link);
    expect(url.hash.startsWith('#s=')).toBe(true);
    expect(url.pathname).toBe(new URL(page.url()).pathname);
    expect(url.hash).not.toMatch(/[=+/]$/);

    const second = await context.newPage();
    const seen: string[] = [];
    second.on('request', (request) => seen.push(request.url()));
    await second.goto(link);
    await expect(second.locator('.cm-content')).toContainText('X --> Y');
    await expect(second.getByLabel('Theme')).toHaveValue('nord');
    await expect(second.getByLabel('Charset')).toHaveValue('ascii');
    if (basePath !== '') {
      expect(seen.filter((entry) => new URL(entry).pathname === '/')).toEqual([]);
    }
  });

  test('loads links changed in the same tab and follows browser history', async ({ page }) => {
    await openPlayground(page);
    const links = await page.evaluate(async () => {
      const encode = async (src: string, theme: string): Promise<string> => {
        const bytes = new TextEncoder().encode(JSON.stringify({ src, opt: { theme } }));
        const stream = new Blob([bytes]).stream().pipeThrough(new CompressionStream('deflate-raw'));
        const compressed = new Uint8Array(await new Response(stream).arrayBuffer());
        return btoa(String.fromCharCode(...compressed))
          .replace(/\+/g, '-')
          .replace(/\//g, '_')
          .replace(/=+$/, '');
      };
      return [
        await encode('flowchart LR\n First --> Link', 'nord'),
        await encode('flowchart TD\n Second --> Link', 'github-dark'),
      ];
    });
    const [first, second] = links;
    if (first === undefined || second === undefined) {
      throw new Error('expected two shared diagrams');
    }
    await page.evaluate((encoded) => {
      location.hash = `s=${encoded}`;
    }, first);
    await expect(page.locator('.cm-content')).toContainText('First --> Link');
    await expect(page.getByLabel('Theme')).toHaveValue('nord');
    await page.evaluate((encoded) => {
      location.hash = `s=${encoded}`;
    }, second);
    await expect(page.locator('.cm-content')).toContainText('Second --> Link');
    await expect(page.getByLabel('Theme')).toHaveValue('github-dark');
    await page.goBack();
    await expect(page.locator('.cm-content')).toContainText('First --> Link');
    await expect(page.getByLabel('Theme')).toHaveValue('nord');
    await page.evaluate(() => {
      location.hash = 's=bad-link';
    });
    await expect(page.locator('.cm-content')).toContainText(DEFAULT_FIRST_LINE);
    await expect(page.getByRole('status')).toContainText('This shared link is invalid or incomplete');
  });

  test('offers the URL when the clipboard refuses the write', async ({ page }) => {
    await page.addInitScript(() => {
      Object.defineProperty(navigator, 'clipboard', {
        value: { writeText: () => Promise.reject(new Error('denied')) },
      });
    });
    await openPlayground(page);
    await page.getByRole('button', { name: 'Copy link' }).click();
    await expect(page.getByRole('status')).toContainText(
      'Unable to copy automatically. Select and copy the URL below.',
    );
    const field = page.getByLabel('Shared link');
    await expect(field).toHaveAttribute('readonly', '');
    expect(await field.inputValue()).toContain('#s=');
  });

  test('loads the default sample and says so for an invalid link', async ({ page }) => {
    await page.goto('./#s=%%%not-a-link');
    await expect(page.getByRole('status')).toContainText(
      'This shared link is invalid or incomplete; the default sample was loaded.',
    );
    await expect(page.locator('.cm-content')).toContainText(DEFAULT_FIRST_LINE);
  });
});

test.describe('layout', () => {
  for (const width of [320, 390, 640]) {
    test(`has no horizontal scroll at ${width} px`, async ({ page }) => {
      await page.setViewportSize({ width, height: 800 });
      await openPlayground(page);
      const overflow = await page.evaluate(
        () => document.documentElement.scrollWidth - document.documentElement.clientWidth,
      );
      expect(overflow).toBeLessThanOrEqual(0);
    });
  }

  test('uses two columns and side-by-side panes from 1024 px', async ({ page }) => {
    await page.setViewportSize({ width: 1280, height: 900 });
    await openPlayground(page);
    const columns = await page
      .locator('.layout')
      .evaluate((element) => getComputedStyle(element).gridTemplateColumns.split(' ').map(Number.parseFloat));
    expect(columns).toHaveLength(2);
    expect(Math.abs((columns[1] ?? 0) / (columns[0] ?? 1) - 1.5)).toBeLessThan(0.02);
    const go = await pane(page, 'go').boundingBox();
    const rust = await pane(page, 'rust').boundingBox();
    expect(go && rust && Math.abs(go.y - rust.y) < 1 && rust.x > go.x + go.width / 2).toBe(true);
  });

  test('stacks one column with Go above Rust below 1024 px', async ({ page }) => {
    await page.setViewportSize({ width: 1023, height: 900 });
    await openPlayground(page);
    const columns = await page
      .locator('.layout')
      .evaluate((element) => getComputedStyle(element).gridTemplateColumns.split(' ').length);
    expect(columns).toBe(1);
    const go = await pane(page, 'go').boundingBox();
    const rust = await pane(page, 'rust').boundingBox();
    expect(go && rust && rust.y > go.y).toBe(true);
  });
});

test.describe('keyboard and focus', () => {
  test('starts at the skip link and reaches the editor', async ({ page }) => {
    await openPlayground(page);
    await page.keyboard.press('Tab');
    await expect(page.getByRole('link', { name: 'Skip to editor' })).toBeFocused();
    await page.keyboard.press('Enter');
    await expect(page.locator('.cm-content')).toBeFocused();
  });

  test('tabs follow the ARIA tab pattern with one tab stop', async ({ page }) => {
    await openPlayground(page);
    await expect(page.locator('[role=tab][tabindex="0"]')).toHaveCount(1);
    await page.getByRole('tab', { name: 'SVG' }).focus();
    const selected = async (name: string) => {
      const tab = page.getByRole('tab', { name, exact: true });
      await expect(tab).toHaveAttribute('aria-selected', 'true');
      await expect(tab).toBeFocused();
    };
    await page.keyboard.press('ArrowRight');
    await selected('Text');
    await page.keyboard.press('End');
    await selected('Diagnostics JSON');
    await page.keyboard.press('ArrowRight');
    await selected('SVG');
    await page.keyboard.press('ArrowLeft');
    await selected('Diagnostics JSON');
    await page.keyboard.press('Home');
    await selected('SVG');
    await expect(page.getByRole('tabpanel')).toHaveAttribute('aria-labelledby', 'tab-svg');
    await expect(page.locator('[role=tab][tabindex="0"]')).toHaveCount(1);
  });

  test('the engine radios switch panes with the arrow keys', async ({ page }) => {
    await openPlayground(page);
    const fieldset = page.getByRole('group', { name: 'Engine' });
    await expect(fieldset.getByRole('radio', { name: 'Both' })).toBeChecked();
    await fieldset.getByRole('radio', { name: 'Both' }).focus();
    await page.keyboard.press('ArrowLeft');
    await expect(fieldset.getByRole('radio', { name: 'Rust' })).toBeChecked();
    await expect(pane(page, 'go')).toHaveCount(0);
    await expect(pane(page, 'rust').locator('img')).toBeVisible();
    await page.keyboard.press('ArrowLeft');
    await expect(fieldset.getByRole('radio', { name: 'Go', exact: true })).toBeChecked();
    await expect(pane(page, 'rust')).toHaveCount(0);
    await expect(comparison(page)).toHaveCount(0);
  });

  test('every focus stop shows a 2 px accent outline with a 4 px offset', async ({ page }) => {
    await openPlayground(page);
    await setSource(page, BROKEN_SOURCE);
    await expect(page.getByRole('button', { name: /^Go and Rust error / })).toBeVisible();
    await page.locator('a.skip').focus();
    const failures: string[] = [];
    for (let stop = 0; stop < 30; stop += 1) {
      if (stop > 0) {
        await page.keyboard.press('Tab');
      }
      const inEditor = await page.evaluate(() => document.activeElement?.classList.contains('cm-content') === true);
      if (inEditor) {
        await expect(page.locator('.cm-editor.cm-focused')).toHaveCount(1);
      }
      const result = await page.evaluate(() => {
        const active = document.activeElement as HTMLElement | null;
        if (active === null || active === document.body) {
          return null;
        }
        const target = active.classList.contains('cm-content') ? (active.closest('.cm-editor') as HTMLElement) : active;
        const style = getComputedStyle(target);
        const accent = getComputedStyle(document.documentElement).getPropertyValue('--emd-accent').trim();
        const probe = document.createElement('span');
        probe.style.color = accent;
        document.body.append(probe);
        const expected = getComputedStyle(probe).color;
        probe.remove();
        return {
          label: `${active.tagName.toLowerCase()} ${active.getAttribute('aria-label') ?? active.textContent?.slice(0, 24) ?? ''}`,
          style: style.outlineStyle,
          width: style.outlineWidth,
          offset: style.outlineOffset,
          color: style.outlineColor,
          expected,
        };
      });
      if (result === null) {
        continue;
      }
      if (
        result.style === 'none' ||
        result.width !== '2px' ||
        result.offset !== '4px' ||
        result.color !== result.expected
      ) {
        failures.push(JSON.stringify(result));
      }
    }
    expect(failures).toEqual([]);
  });

  test('every control is at least 24 by 24 CSS pixels', async ({ page }) => {
    await openPlayground(page);
    const small = await page.evaluate(() =>
      [...document.querySelectorAll('button, select, input, a[href]')]
        .map((element) => ({ name: element.outerHTML.slice(0, 80), box: element.getBoundingClientRect() }))
        .filter(({ box }) => box.width > 0 && box.height > 0 && (box.width < 24 || box.height < 24))
        .map(({ name, box }) => `${name} ${box.width}x${box.height}`),
    );
    expect(small).toEqual([]);
  });
});

test.describe('motion', () => {
  test('transitions name four properties and last 120 ms', async ({ page }) => {
    await openPlayground(page);
    const style = await page.getByRole('button', { name: 'Copy link' }).evaluate((element) => ({
      property: getComputedStyle(element).transitionProperty,
      duration: getComputedStyle(element).transitionDuration,
      timing: getComputedStyle(element).transitionTimingFunction,
    }));
    expect(style.property).toBe('color, background-color');
    expect(style.duration).toBe('0.12s, 0.12s');
    expect(style.timing).toBe('cubic-bezier(0.2, 0, 0, 1), cubic-bezier(0.2, 0, 0, 1)');
  });

  test('every transition and animation lasts 0 s under reduced motion', async ({ page }) => {
    await page.emulateMedia({ reducedMotion: 'reduce' });
    await openPlayground(page);
    await setSource(page, BROKEN_SOURCE);
    const offenders = await page.evaluate(() => {
      const found: string[] = [];
      for (const element of document.querySelectorAll('*')) {
        const style = getComputedStyle(element);
        for (const value of [style.transitionDuration, style.animationDuration]) {
          if (value.split(',').some((part) => Number.parseFloat(part) !== 0)) {
            found.push(`${element.tagName.toLowerCase()}.${element.className} ${value}`);
          }
        }
      }
      return found;
    });
    expect(offenders).toEqual([]);
  });
});

test.describe('contrast', () => {
  for (const scheme of ['light', 'dark'] as const) {
    test(`text reaches 4.5:1 and control edges 3:1 in the ${scheme} scheme`, async ({ page }) => {
      await page.emulateMedia({ colorScheme: scheme });
      await openPlayground(page);
      await setSource(page, BROKEN_SOURCE);
      await expect(page.getByRole('button', { name: /^Go and Rust error / })).toBeVisible();
      await expect(page.getByText('Showing the last valid revision')).toHaveCount(2);
      const failures = await page.evaluate(() => {
        type Rgba = [number, number, number, number];
        const parse = (value: string): Rgba => {
          const match = value.match(/rgba?\(([^)]+)\)/);
          if (match === null) {
            return [0, 0, 0, 0];
          }
          const parts = (match[1] ?? '')
            .split(/[ ,/]+/)
            .filter(Boolean)
            .map(Number);
          return [parts[0] ?? 0, parts[1] ?? 0, parts[2] ?? 0, parts[3] ?? 1];
        };
        const over = (top: Rgba, bottom: Rgba): Rgba => {
          const alpha = top[3] + bottom[3] * (1 - top[3]);
          if (alpha === 0) {
            return [0, 0, 0, 0];
          }
          const mix = (a: number, b: number) => (a * top[3] + b * bottom[3] * (1 - top[3])) / alpha;
          return [mix(top[0], bottom[0]), mix(top[1], bottom[1]), mix(top[2], bottom[2]), alpha];
        };
        const background = (element: Element | null): Rgba => {
          const layers: Rgba[] = [];
          for (let node = element; node !== null; node = node.parentElement) {
            const layer = parse(getComputedStyle(node).backgroundColor);
            if (layer[3] > 0) {
              layers.push(layer);
              if (layer[3] === 1) {
                break;
              }
            }
          }
          return layers.reduceRight((below, layer) => over(layer, below), [255, 255, 255, 1] as Rgba);
        };
        const luminance = (color: Rgba): number => {
          const linear = color.slice(0, 3).map((channel) => {
            const value = channel / 255;
            return value <= 0.04045 ? value / 12.92 : ((value + 0.055) / 1.055) ** 2.4;
          });
          return 0.2126 * (linear[0] ?? 0) + 0.7152 * (linear[1] ?? 0) + 0.0722 * (linear[2] ?? 0);
        };
        const ratio = (a: Rgba, b: Rgba): number => {
          const [high, low] = [luminance(a), luminance(b)].sort((x, y) => y - x);
          return ((high ?? 0) + 0.05) / ((low ?? 0) + 0.05);
        };
        const visible = (element: Element): boolean => {
          const box = element.getBoundingClientRect();
          const style = getComputedStyle(element);
          return box.width > 0 && box.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
        };
        const name = (element: Element): string =>
          `${element.tagName.toLowerCase()}.${element.className} "${(element.textContent ?? '').trim().slice(0, 30)}"`;
        const problems: string[] = [];
        const textSelector =
          'h1, h2, h3, p, legend, label, button, select, [role=tab], pre, code, dt, dd, .cm-line, .cm-gutterElement';
        for (const element of document.querySelectorAll(textSelector)) {
          const hasText = [...element.childNodes].some(
            (child) => child.nodeType === Node.TEXT_NODE && (child.textContent ?? '').trim() !== '',
          );
          if (!hasText || !visible(element)) {
            continue;
          }
          const measured = ratio(parse(getComputedStyle(element).color), background(element));
          if (measured < 4.5) {
            problems.push(`text ${name(element)} ${measured.toFixed(2)}`);
          }
        }
        const edgeSelector =
          'button, select, input[type=text], .cm-editor, .scroll, .sample, .fallback, .pane .failure';
        for (const element of document.querySelectorAll(edgeSelector)) {
          if (!visible(element)) {
            continue;
          }
          const style = getComputedStyle(element);
          const border = parse(style.borderTopColor);
          if (border[3] === 0 || style.borderTopWidth === '0px' || style.borderTopStyle === 'none') {
            continue;
          }
          const measured = ratio(border, background(element.parentElement));
          if (measured < 3) {
            problems.push(`edge ${name(element)} ${measured.toFixed(2)}`);
          }
        }
        const selectedTab = document.querySelector('[role=tab][aria-selected=true]');
        if (selectedTab !== null) {
          const measured = ratio(
            parse(getComputedStyle(selectedTab).borderBottomColor),
            background(selectedTab.parentElement),
          );
          if (measured < 3) {
            problems.push(`selected tab ${measured.toFixed(2)}`);
          }
        }
        for (const marker of document.querySelectorAll('.cm-lint-marker')) {
          const measured = ratio(parse(getComputedStyle(marker).backgroundColor), background(marker.parentElement));
          if (measured < 3) {
            problems.push(`lint marker ${measured.toFixed(2)}`);
          }
        }
        return problems;
      });
      expect(failures).toEqual([]);
    });
  }
});

test.describe('first paint without scripts', () => {
  test.use({ javaScriptEnabled: false });

  test('serves the prerendered page', async ({ page }) => {
    await page.goto('./');
    await expect(page.getByRole('main')).toHaveCount(1);
    await expect(page.getByRole('heading', { level: 1, name: 'Elegant Mermaid' })).toBeVisible();
    await expect(
      page.getByText('Render and compare Mermaid diagrams locally in your browser; source is never uploaded.'),
    ).toBeVisible();
    await expect(page.getByRole('link', { name: 'Skip to editor' })).toHaveAttribute('href', '#editor');
    const firstFocusable = await page.evaluate(
      () =>
        document.querySelector('a[href], button:not([disabled]), input:not([disabled]), select, [tabindex="0"]')
          ?.textContent,
    );
    expect(firstFocusable).toBe('Skip to editor');
    await expect(page.getByLabel('Mermaid source')).toContainText(DEFAULT_FIRST_LINE);
    await expect(page.getByRole('radio', { name: 'Both' })).toBeChecked();
    await expect(page.getByRole('tab', { name: 'SVG' })).toHaveAttribute('aria-selected', 'true');
    const sample = page.getByLabel('Sample output while the engines load');
    await expect(sample).toBeVisible();
    await expect(sample).toContainText('Start');
    await expect(sample).toContainText('Choice');
    await expect(sample).toContainText('Done');
    await expect(sample).not.toContainText('Engines are loading.');
    await expect(page.getByRole('status')).toBeEmpty();
    await expect(page.locator('noscript p')).toHaveText(
      'This playground needs JavaScript to render your edits; the sample source and output remain available.',
    );
  });
});
