export const DEFAULT_SOURCE = 'flowchart LR\n  A[Start] --> B{Choice}\n  B -->|yes| C[Done]\n  B -->|no| A\n';

export const THEMES = [
  'elegant-light',
  'elegant-dark',
  'github-light',
  'github-dark',
  'catppuccin-latte',
  'catppuccin-mocha',
  'nord',
  'solarized-light',
  'solarized-dark',
] as const;

export type ThemeName = (typeof THEMES)[number];

export const CHARSETS = ['unicode', 'ascii'] as const;

export type Charset = (typeof CHARSETS)[number];

export const EMPTY_MESSAGE = 'Empty diagram: add a Mermaid header such as flowchart TD; waiting for changes';

export const INVALID_LINK_MESSAGE = 'This shared link is invalid or incomplete; the default sample was loaded.';

export const COPY_OK = 'Link copied';

export const COPY_REFUSED = 'Unable to copy automatically. Select and copy the URL below.';

export const COPY_UNSUPPORTED =
  'Unable to create a shared link in this browser. Try a browser with CompressionStream support.';
