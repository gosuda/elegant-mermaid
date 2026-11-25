// Package mermaid parses, checks, lints, lays out, and renders Mermaid
// diagrams as SVG or terminal text.
//
// The package imports only the standard library. It reads no network, host
// font, clock, or random source: output depends only on input and options.
// All geometry is integer.
//
// A Document is immutable after Parse. A Document and every function of
// this package are safe for concurrent use.
//
// Parse borrows valid UTF-8 input; callers must not modify it while the
// Document is in use. Invalid UTF-8 is repaired into owned storage, and all
// spans and positions index that repaired source. Diagnostics returns an
// independent copy, including related spans, fixes, and edits. Scene.Dump
// returns fresh bytes on each call.
//
// LayoutOptions.Config accepts a config mapping; empty or whitespace-only
// input means an empty mapping. Per-call config overrides source config
// without changing the Document. The maxTextSize and maxEdges caps are
// rechecked under that overlay; the original parse diagnostics stay unchanged.
// fontFamily selects the SVG font family and conservative vector text widths.
// SVG output also applies look and handDrawnSeed. Rendering supports all
// registered diagram kinds, icon packs, and SVG text paths.
//
// Render errors wrap one exported sentinel for errors.Is, except that a
// cancelled context returns ctx.Err() unchanged. Cancellation is checked at
// stage boundaries; it does not interrupt an in-progress layout phase.
//
// Diagnostic codes are stable identifiers. A renamed code keeps its old name
// as an alias, and a code is never reused. Before version 1.0, a minor
// version may change the API.
package mermaid
