# Terminal graphics probe and encoders

This file fixes the capability probe and the Kitty, iTerm2, and Sixel encodings that the viewer uses to draw a pixel image in a terminal.

## Bytes and mode choice

- terminal-graphics-01: `ESC` MUST be the byte 0x1B, `ST` MUST be `ESC \`, `BEL` MUST be 0x07, and `CSI` MUST be `ESC [`. [just go-check]
- terminal-graphics-02: `--graphics kitty|iterm|sixel` MUST select the named mode directly, and it MUST NOT send a mode query beyond the probe of `terminal-graphics-05`; `--graphics cells` MUST select `cells` and MUST send no query at all. [just go-check]
- terminal-graphics-03: `auto`, which is the default, MUST probe when stdin and stdout are terminals, and MUST select `cells` otherwise. [just go-check]
- terminal-graphics-04: Replay MUST NOT probe; in replay `auto` MUST be `cells`, and the cell size MUST be the fallback. [just go-check: TestViewScripts]

## Probe

- terminal-graphics-05: The probe MUST run for `auto` and for the explicit pixel modes `kitty`, `iterm`, and `sixel`, so that the cell size is known in every pixel mode. [just go-check]
- terminal-graphics-06: The probe MUST run with the terminal in raw mode, and it MUST restore the terminal before it returns. [just go-check]
- terminal-graphics-07: The probe MUST send the Kitty query first, and only when the Kitty candidate condition holds: [just go-check]

  - the environment variable `KITTY_WINDOW_ID` is non-empty, or
  - `TERM` is `xterm-kitty`, or
  - `TERM_PROGRAM` is `ghostty` or `WezTerm`.

- terminal-graphics-08: The Kitty query MUST be `ESC _ G i=31,s=1,v=1,a=q,t=d,f=24;AAAA ST`. [just go-check]
- terminal-graphics-09: The probe MUST write three queries in one write, in this order: the Kitty query of the candidate rule, the cell size query `CSI 16 t`, and the device attributes query `CSI c`. [just go-check]
- terminal-graphics-10: The probe MUST read until the DA1 reply arrives or 100 ms pass after the write; a reply MUST count only when it arrives before the DA1 reply, replies after the deadline MUST be dropped, and a missing reply MUST mean that the feature is not supported. [just go-check]
- terminal-graphics-11: A Kitty OK reply MUST be an APC reply that contains `i=31;OK`. [just go-check]
- terminal-graphics-12: A cell size reply `CSI 6 ; h ; w t` with `h > 0` and `w > 0` MUST set `cell_h = h` and `cell_w = w`; otherwise the fallback of 8 by 16 MUST apply. [just go-check]
- terminal-graphics-13: The DA1 reply MUST be `CSI ? params c`, and Sixel MUST be supported exactly when the parameter list contains `4`. [just go-check]
- terminal-graphics-14: Under `auto` the mode MUST be the first match of this list: Kitty OK gives `kitty`; `TERM_PROGRAM` equal to `iTerm.app` gives `iterm`; Sixel supported gives `sixel`; any other result gives `cells`. [just go-check]

## Placement

- terminal-graphics-15: The input of every encoder MUST be the composite buffer of `VW` by `VH` pixels defined in `spec/viewer.md`, and that buffer MUST be placed at the viewport origin, cell row 0 and column 0, which is `CSI 1 ; 1 H`. [just go-check]
- terminal-graphics-16: Before each pixel-mode redraw, the terminal writer MUST draw the text rows first and the image after them. [just go-check]

## Kitty encoding

- terminal-graphics-17: The Kitty encoder MUST delete previous images first with `ESC _ G a=d,d=A,q=2 ST`. [just go-check: TestEncoderGolden]
- terminal-graphics-18: The Kitty encoder MUST encode the PNG bytes of the composite buffer as standard base64 with padding, as RFC 4648 section 4 defines it, and split the text into chunks of 4096 characters, the last one shorter. [just go-check: TestEncoderGolden]
- terminal-graphics-19: Chunk 0 MUST be `ESC _ G a=T,f=100,i=1,q=2,m=M;CHUNK ST`, and every later chunk MUST be `ESC _ G m=M;CHUNK ST`, where `M` is 1 for every chunk except the last and 0 for the last. [just go-check: TestEncoderGolden]

## iTerm2 encoding

- terminal-graphics-20: The iTerm2 encoder MUST write one sequence `ESC ] 1337;File=inline=1;size=N;width=VWpx;height=VHpx;preserveAspectRatio=0:BASE64 BEL`, where `N` is the PNG byte count and `BASE64` is standard base64 with padding, on one line, with no chunking. [just go-check: TestEncoderGolden]

## Sixel encoding

- terminal-graphics-21: The Sixel encoder MUST start its output with `ESC P 7;0;0 q "1;1;VW;VH`. [just go-check: TestEncoderGolden]
- terminal-graphics-22: The Sixel encoder MUST define 216 palette registers, numbered 0 to 215, once, in ascending order, before any data, as `#n;2;R;G;B` with `r6 = n / 36`, `g6 = (n / 6) mod 6`, `b6 = n mod 6`, `R = 20 * r6`, `G = 20 * g6`, and `B = 20 * b6`. [just go-check: TestEncoderGolden]
- terminal-graphics-23: A pixel MUST map to `idx = 36 * q(r) + 6 * q(g) + q(b)`, where `q(v) = (v * 5 + 127) / 255`, and alpha MUST be ignored. [just go-check: TestEncoderGolden]
- terminal-graphics-24: Rows MUST be grouped in bands of 6, where band `b` covers rows `6b` to `6b + 5` and rows at or beyond `VH` are empty. [just go-check: TestEncoderGolden]
- terminal-graphics-25: For each band, for each register `n` in ascending order that occurs in the band, the encoder MUST write `#n` and then one sixel character per column `x` from 0 to `VW - 1`, where the character is `63 + mask` and bit `r` of `mask` is set when row `6b + r` has register `n` at column `x`. [just go-check: TestEncoderGolden]
- terminal-graphics-26: A run of 4 or more equal characters MUST be written as `!k` followed by the character, where `k` is the run length, and a shorter run MUST repeat the character. [just go-check: TestEncoderGolden]
- terminal-graphics-27: The encoder MUST write `$` between the registers of one band, MUST write `-` after the last register of a band unless it is the last band, and MUST end its output with `ST`. [just go-check: TestEncoderGolden]

## Golden fixtures

- terminal-graphics-28: The golden tests MUST use three fixtures in `corpus/termgfx/`, named `tiny`, `tall`, and `wide`, each a PNG `<fixture>.png` with its Mermaid source in `<fixture>.mmd` beside it. [just go-check: TestEncoderGolden]
- terminal-graphics-29: The fixture sources MUST be `tiny.mmd` = `flowchart LR` then `  A --> B`, `tall.mmd` = `flowchart TB` then `  A --> B --> C --> D`, and `wide.mmd` = `sequenceDiagram` then `  A->>B: hi` then `  B-->>A: ok`, one statement per line. [just go-check: TestEncoderGolden]
- terminal-graphics-30: Each PNG MUST be rendered at scale 1 from its source by `bin/emd-go render -e png -s 1 -t elegant-light -o corpus/termgfx/<fixture>.png corpus/termgfx/<fixture>.mmd`, and it MUST be the input of the Kitty and iTerm2 encoders; the same PNG decoded to RGBA8 MUST be the input of the Sixel encoder. [just go-check: TestEncoderGolden]
- terminal-graphics-31: Each fixture MUST have one expected byte file per encoder, named `<fixture>.kitty`, `<fixture>.iterm`, and `<fixture>.sixel`, and the Go test `TestEncoderGolden` MUST compare the three encoders' output with those files byte for byte. [just go-check: TestEncoderGolden]
- terminal-graphics-32: The Rust test `encoder_golden` MUST read `corpus/termgfx/` and compare the three encoders' output with the same expected files byte for byte. [just rust-check: encoder_golden]
- terminal-graphics-33: The PNG bytes that the live viewer produces MAY differ between Go and Rust, and the golden tests MUST NOT compare them. [just rust-check: encoder_golden]
