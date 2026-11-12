package flowchart

import (
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

const (
	codeUnexpectedToken      = "flowchart/unexpected-token"
	codeUnknownStatement     = "flowchart/unknown-statement"
	codeUnterminated         = "flowchart/unterminated"
	codeUnclosedNodeBracket  = "flowchart/unclosed-node-bracket"
	codeSubgraphDirIgnored   = "flowchart/subgraph-direction-ignored"
	codeArrowInvalid         = "flowchart/arrow-invalid"
	codeLinkUnsupportedMark  = "flowchart/link-unsupported-marker"
	codeLabelDoubleInDouble  = "flowchart/label-double-in-double"
	codeLabelDoubleInSingle  = "flowchart/label-double-in-single"
	codeLabelEscapedQuote    = "flowchart/label-escaped-quote"
	codeLabelQuoteInUnquoted = "flowchart/label-quote-in-unquoted"
	codeLabelParensUnquoted  = "flowchart/label-parens-unquoted"
	codeDirInvalid           = "flowchart/dir-invalid"
	codeDirKeywordInvalid    = "flowchart/dir-kw-invalid"
	codeLinkMissing          = "flowchart/link-missing"
	codeMetaUnsupported      = "flowchart/meta-unsupported"
	codeEndWithoutSubgraph   = "flowchart/end-without-subgraph"
	codeNodeMixedBrackets    = "flowchart/node-mixed-brackets"
	codeNodeEmpty            = "flowchart/node-empty"
	codeQuoteUnclosed        = "flowchart/quote-unclosed"
	codeClassMalformed       = "flowchart/class-malformed"
	codeLinkStyleMultiline   = "flowchart/linkstyle-multiline"
	codeLinkStyleRange       = "flowchart/linkstyle-range-not-supported"
	codeClickExtraText       = "flowchart/click-call-extra-text"
	codeLinkStyleIDUnknown   = "flowchart/linkstyle-id-unknown"
	codeTypedShapeUnsupport  = "flowchart/typed-shape-unsupported"
	codeUnknownKind          = "common/unknown-diagram-kind"
	codeMalformedConfig      = "config/malformed"
)

const (
	tokenPlaceholder = "TOKEN"
	listPlaceholder  = "LIST"
)

type rowSpec struct {
	severity diag.Severity
	template string
	help     string
}

var rows = map[string]rowSpec{
	codeUnexpectedToken: {
		severity: diag.SeverityError,
		template: "unexpected " + tokenPlaceholder + ", expected one of: " + listPlaceholder,
		help:     "Remove the token, or replace it with one of the listed tokens.",
	},
	codeUnknownStatement: {
		severity: diag.SeverityError,
		template: "unknown statement " + tokenPlaceholder,
		help:     "Start the line with a node, an edge, or a flowchart statement such as style or subgraph.",
	},
	codeUnterminated: {
		severity: diag.SeverityError,
		template: "unterminated " + tokenPlaceholder,
		help:     "Close the opening delimiter before the end of the input.",
	},
	codeUnclosedNodeBracket: {
		severity: diag.SeverityError,
		template: "node bracket " + tokenPlaceholder + " is never closed",
		help:     "Add the closing bracket that matches the opening bracket.",
	},
	codeSubgraphDirIgnored: {
		severity: diag.SeverityWarning,
		template: "subgraph direction is ignored because an edge crosses its boundary",
		help:     "Remove the direction statement, or move the crossing edge outside the subgraph.",
	},
	codeArrowInvalid: {
		severity: diag.SeverityError,
		template: "A single arrow -> is used in a flowchart",
		help:     "Replace -> with -->, or use -- text --> for an inline label.",
	},
	codeLinkUnsupportedMark: {
		severity: diag.SeverityError,
		template: "An inline link uses a one-sided end marker, such as --x--> or --o-->",
		help:     "Use a symmetric marker pair such as x--x, or a plain arrow with a label.",
	},
	codeLabelDoubleInDouble: {
		severity: diag.SeverityError,
		template: "A double-quoted label contains another double quote",
		help:     "Use &quot; for the inner quotes.",
	},
	codeLabelDoubleInSingle: {
		severity: diag.SeverityError,
		template: "A single-quoted label contains an unescaped double quote",
		help:     "Replace the inner double quote with &quot;, or use a double-quoted label with &quot; inside.",
	},
	codeLabelEscapedQuote: {
		severity: diag.SeverityError,
		template: "A node label contains a backslash-escaped quote, which Mermaid does not support",
		help:     "Use &quot; for the inner quotes instead of a backslash escape.",
	},
	codeLabelQuoteInUnquoted: {
		severity: diag.SeverityError,
		template: "A double quote appears inside an unquoted label",
		help:     "Wrap the whole label in double quotes and write inner quotes as &quot;.",
	},
	codeLabelParensUnquoted: {
		severity: diag.SeverityError,
		template: "An unquoted label contains an opening or closing parenthesis",
		help:     "Wrap the label in double quotes, or replace ( and ) with &#40; and &#41;.",
	},
	codeDirInvalid: {
		severity: diag.SeverityError,
		template: "The direction token after the header is not one of TD, TB, BT, RL, LR",
		help:     "Use one of TD, TB, BT, RL, or LR.",
	},
	codeDirKeywordInvalid: {
		severity: diag.SeverityError,
		template: "An unknown keyword appears before the direction token",
		help:     "Replace the unknown keyword with direction.",
	},
	codeLinkMissing: {
		severity: diag.SeverityError,
		template: "Two nodes appear on one line without a connecting arrow",
		help:     "Insert --> between the two nodes.",
	},
	codeMetaUnsupported: {
		severity: diag.SeverityError,
		template: "A meta statement such as title appears in a flowchart",
		help:     "Use a Markdown heading above the block, or draw a labelled node at the top.",
	},
	codeEndWithoutSubgraph: {
		severity: diag.SeverityError,
		template: "end appears without a matching subgraph",
		help:     "Remove this end line, or add a subgraph above it.",
	},
	codeNodeMixedBrackets: {
		severity: diag.SeverityError,
		template: "The opening and closing brackets of a node shape do not match",
		help:     "Close with the bracket that matches the opener, for example ) for (.",
	},
	codeNodeEmpty: {
		severity: diag.SeverityError,
		template: "A node shape has empty content, such as A[]",
		help:     "Write text inside the brackets, or drop the brackets and use the bare node id.",
	},
	codeQuoteUnclosed: {
		severity: diag.SeverityError,
		template: "A node label opens a quote but never closes it",
		help:     "Close the quote, for example A[\"Label\"].",
	},
	codeClassMalformed: {
		severity: diag.SeverityError,
		template: "A class statement is missing node ids or the class name",
		help:     "Write class A,B classname.",
	},
	codeLinkStyleMultiline: {
		severity: diag.SeverityError,
		template: "The linkStyle style pairs are placed on a line after the indices",
		help:     "Put the styles on the same line as the indices, for example linkStyle 0,1 stroke:#f00.",
	},
	codeLinkStyleRange: {
		severity: diag.SeverityError,
		template: "A range such as 0:3 is used in the linkStyle index list",
		help:     "Use comma-separated indices instead, for example linkStyle 0,1,2.",
	},
	codeClickExtraText: {
		severity: diag.SeverityError,
		template: "A click call statement carries tooltip or target text after call fn()",
		help:     "Write click A call doThing() with no trailing text.",
	},
	codeLinkStyleIDUnknown: {
		severity: diag.SeverityError,
		template: "linkStyle references an edge id that no link defines",
		help:     "Attach the id to a link first, as in e1@-->, before styling it.",
	},
	codeTypedShapeUnsupport: {
		severity: diag.SeverityError,
		template: "A typed shape in an @{ shape: ... } node is not supported",
		help:     "Use one of the supported shape names such as rect, rounded, diamond, or circle.",
	},
	codeUnknownKind: {
		severity: diag.SeverityError,
		template: "unknown diagram kind " + tokenPlaceholder,
		help:     "Start the source with a supported diagram header, for example flowchart.",
	},
	codeMalformedConfig: {
		severity: diag.SeverityError,
		template: "malformed config value",
	},
}

func row(code string) rowSpec {
	if spec, ok := rows[code]; ok {
		return spec
	}
	return rowSpec{severity: diag.SeverityError}
}

func plainDiagnostic(code string, span source.Span) diag.Diagnostic {
	spec := row(code)
	return diag.Diagnostic{Code: code, Severity: spec.severity, Message: spec.template, Span: span, Help: spec.help}
}

func tokenDiagnostic(code string, span source.Span, token string) diag.Diagnostic {
	spec := row(code)
	message := strings.ReplaceAll(spec.template, tokenPlaceholder, token)
	return diag.Diagnostic{Code: code, Severity: spec.severity, Message: message, Span: span, Help: spec.help}
}

func unexpectedDiagnostic(code string, span source.Span, token string, expected []string) diag.Diagnostic {
	spec := row(code)
	message := strings.ReplaceAll(spec.template, tokenPlaceholder, token)
	message = strings.ReplaceAll(message, listPlaceholder, strings.Join(expected, ", "))
	return diag.Diagnostic{Code: code, Severity: spec.severity, Message: message, Span: span, Help: spec.help}
}
