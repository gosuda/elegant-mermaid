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
// Diagnostic codes are stable identifiers. A renamed code keeps its old name
// as an alias, and a code is never reused. Before version 1.0, a minor
// version may change the API.
package mermaid
