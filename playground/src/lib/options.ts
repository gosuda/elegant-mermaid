import type { Charset } from './defaults';
import type { AnswerOp } from './protocol';

export interface RenderOptions {
  theme: string;
  charset: Charset;
  background: string | null;
  maxWidth: number | null;
}

export function optionsJson(op: AnswerOp | 'fix', options: RenderOptions): string {
  switch (op) {
    case 'render_svg':
      return JSON.stringify({ theme: options.theme, background: options.background, max_width: options.maxWidth });
    case 'render_text':
      return JSON.stringify({ theme: options.theme, charset: options.charset, max_width: options.maxWidth });
    case 'layout':
      return JSON.stringify({ profile: 'vector', stage: 'layout' });
    case 'fix':
      return JSON.stringify({ max: 'safe' });
    case 'check':
      return '{}';
  }
}
