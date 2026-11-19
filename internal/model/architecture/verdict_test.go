package architecture_test

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	model "github.com/gosuda/elegant-mermaid/internal/model/architecture"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/architecture"
)

type verdictCase struct {
	name   string
	source string
	accept bool
}

func accepts(source string) bool {
	text := []byte(source)
	prep := syntax.Preprocess(text)
	ast, parsed := parser.Parse(text, prep.Removed)
	_, resolved := model.Resolve(text, ast)
	for _, d := range append(parsed, resolved...) {
		if d.Severity == diag.SeverityError {
			return false
		}
	}
	return true
}

func TestUpstreamVerdicts(t *testing.T) {
	for _, tc := range upstreamVerdicts {
		require.Equal(t, tc.accept, accepts(tc.source), tc.name)
	}
}

var upstreamVerdicts = []verdictCase{
	{"digit-id", "architecture-beta\nservice 1abc(server)[X]\n", true},
	{"int-id", "architecture-beta\nservice 123(server)[X]\n", true},
	{"bool-id", "architecture-beta\nservice true(server)[X]\n", true},
	{"boolprefix-id", "architecture-beta\nservice trueblue(server)[X]\n", true},
	{"L-id", "architecture-beta\nservice L(server)[X]\n", false},
	{"Lambda-id", "architecture-beta\nservice Lambda(server)[X]\nservice b(server)[Y]\nLambda:R -- L:b\n", false},
	{"R-lone-id", "architecture-beta\nservice R(server)[X]\nservice b(server)[Y]\nR:R -- L:b\n", false},
	{"hyphen-id", "architecture-beta\nservice group-1(server)[X]\n", true},
	{"kw-id", "architecture-beta\nservice group(server)[X]\n", false},
	{"in-id", "architecture-beta\nservice in(server)[X]\n", false},
	{"row-id", "architecture-beta\nservice row(server)[X]\n", false},
	{"empty", "architecture-beta\n", true},
	{"no-nl", "architecture-beta", true},
	{"group-title-only", "architecture-beta\ngroup g[T]\n", true},
	{"service-string", "architecture-beta\nservice a \"txt\" [T]\n", true},
	{"service-string2", "architecture-beta\nservice a\"txt\"\n", true},
	{"edge-title", "architecture-beta\nservice a(server)\nservice b(server)\na:R -[hi there]- L:b\n", true},
	{"edge-both-into", "architecture-beta\nservice a(server)\nservice b(server)\na:R <--> L:b\n", true},
	{"edge-into-left", "architecture-beta\nservice a(server)\nservice b(server)\na:R <-- L:b\n", true},
	{"edge-into-title", "architecture-beta\nservice a(server)\nservice b(server)\na:R <-[x]-> L:b\n", true},
	{"bad-dir", "architecture-beta\nservice a(server)\nservice b(server)\na:X -- L:b\n", false},
	{"lower-dir", "architecture-beta\nservice a(server)\nservice b(server)\na:r -- L:b\n", false},
	{"self-edge", "architecture-beta\nservice a(server)\na:R -- L:a\n", true},
	{"group-endpoint", "architecture-beta\ngroup g[G]\nservice a(server)\na:R -- L:g\n", false},
	{"missing-endpoint", "architecture-beta\nservice a(server)\na:R -- L:b\n", false},
	{"dup-id", "architecture-beta\nservice a(server)\nservice a(server)\n", false},
	{"self-parent", "architecture-beta\ngroup g[G] in g\n", false},
	{"parent-missing", "architecture-beta\nservice a(server) in g\n", false},
	{"parent-later-group", "architecture-beta\nservice a(server) in g\ngroup g[G]\n", true},
	{"group-parent-later", "architecture-beta\ngroup g[G] in h\ngroup h[H]\n", false},
	{"parent-node", "architecture-beta\nservice a(server)\nservice b(server) in a\n", false},
	{"group-mod-same", "architecture-beta\ngroup g[G]\nservice a(server) in g\nservice b(server) in g\na{group}:R -- L:b\n", false},
	{"group-mod-ungrouped", "architecture-beta\nservice a(server)\nservice b(server)\na{group}:R -- L:b\n", true},
	{"align-one", "architecture-beta\nservice a(server)\nalign row a\n", false},
	{"align-dup", "architecture-beta\nservice a(server)\nservice b(server)\nalign row a a b\n", false},
	{"align-group", "architecture-beta\ngroup g[G]\nservice b(server)\nalign row g b\n", false},
	{"align-missing", "architecture-beta\nservice b(server)\nalign row b c\n", false},
	{"align-bad-dir", "architecture-beta\nservice a(server)\nservice b(server)\nalign diag a b\n", false},
	{"semicolon", "architecture-beta\nservice a(server); service b(server)\n", false},
	{"icon-colon", "architecture-beta\nservice a(logos:aws-lambda)[X]\n", true},
	{"icon-space", "architecture-beta\nservice a(a b)[X]\n", false},
	{"icon-empty", "architecture-beta\nservice a()[X]\n", false},
	{"title-quoted", "architecture-beta\nservice a(server)[\"he said \\\"hi\\\"\"]\n", true},
	{"title-bracket", "architecture-beta\nservice a(server)[a[b]]\n", false},
	{"title-empty", "architecture-beta\nservice a(server)[]\n", false},
	{"junction-title", "architecture-beta\njunction j[T]\n", false},
	{"junction-icon", "architecture-beta\njunction j(server)\n", false},
	{"title-stmt", "architecture-beta\ntitle Hello\nservice a(server)\naccTitle: acc\naccDescr: d\n", true},
	{"title-empty-stmt", "architecture-beta\ntitle\nservice a(server)\n", true},
	{"accdescr-block", "architecture-beta\naccDescr {\n a\n b\n}\nservice a(server)\n", true},
	{"header-trailing", "architecture-beta  \nservice a(server)\n", true},
	{"header-then-stmt", "architecture-beta service a(server)\n", true},
	{"comment", "architecture-beta\n%% hi\nservice a(server) %% trailing\n", true},
	{"crlf", "architecture-beta\r\nservice a(server)\r\n", true},
	{"group-icon-title-in", "architecture-beta\ngroup a(cloud)[A]\ngroup b(cloud)[B] in a\n", true},
	{"repeated-edge", "architecture-beta\nservice a(server)\nservice b(server)\na:R -- L:b\na:R -- L:b\n", true},
	{"edge-spaces", "architecture-beta\nservice a(server)\nservice b(server)\na : R -- L : b\n", true},
	{"edge-nospaces", "architecture-beta\nservice a(server)\nservice b(server)\na:R--L:b\n", true},
	{"edge-gt-nospace", "architecture-beta\nservice a(server)\nservice b(server)\na:R-->L:b\n", true},
	{"group-after-edge-spaces", "architecture-beta\nservice a(server)\nservice b(server)\na {group} :R -- L: b\n", true},
	{"id-dash-tail", "architecture-beta\nservice a-(server)\n", false},
	{"id-dash-mid", "architecture-beta\nservice a-b(server)\nservice c(server)\na-b:R -- L:c\n", true},
	{"unicode-id", "architecture-beta\nservice é(server)\n", false},
	{"tab-sep", "architecture-beta\n\tservice\ta(server)\n", true},
	{"noparen-icon", "architecture-beta\nservice a server\n", false},
	{"service-no-id", "architecture-beta\nservice\n", false},
	{"unknown-stmt", "architecture-beta\nfoo bar\n", false},
	{"leading-blank", "\n\narchitecture-beta\nservice a(server)\n", true},
	{"eof-no-newline", "architecture-beta\nservice a(server)", true},
	{"title1-id", "architecture-beta\nservice title1(server)[X]\n", false},
	{"title-id", "architecture-beta\nservice title(server)[X]\n", false},
	{"acctitle-id", "architecture-beta\nservice accTitle1(server)[X]\n", true},
	{"acctitle-id2", "architecture-beta\nservice a:\n", false},
	{"accdescr-id", "architecture-beta\nservice accDescr1(server)[X]\n", true},
	{"float-id", "architecture-beta\nservice 1.5(server)[X]\n", false},
	{"edge-title-id", "architecture-beta\nservice title(server)\nservice b(server)\ntitle:R -- L:b\n", false},
	{"edge-from-title1", "architecture-beta\nservice b(server)\nservice a(server)\ntitle1:R -- L:b\n", false},
	{"edge-from-accTitle1", "architecture-beta\nservice b(server)\nservice accTitle1(server)\naccTitle1:R -- L:b\n", true},
	{"Title-case", "architecture-beta\nTitle x\n", false},
	{"Tid", "architecture-beta\nservice Tx(server)\n", false},
	{"Bid-after", "architecture-beta\nservice a(server)\nservice b(server)\na:R -- L:b\nBack:R -- L:b\n", false},
	{"id-first-kw-prefix", "architecture-beta\nservice groupx(server)\nservice b(server)\ngroupx:R -- L:b\n", true},
	{"id-in-prefix", "architecture-beta\nservice inx(server)\nservice b(server)\ninx:R -- L:b\n", true},
	{"service-in-kw", "architecture-beta\ngroup g[G]\nservice a(server) in g\nservice b(server) in g\n", true},
	{"in-glued", "architecture-beta\ngroup g[G]\nservice a(server)in g\n", true},
	{"title-glued-icon", "architecture-beta\nservice a(server)[X]in g\n", false},
	{"bracket-no-icon", "architecture-beta\nservice a[X]\n", true},
	{"icon-title-str-order", "architecture-beta\nservice a[X](server)\n", false},
	{"title-then-icon", "architecture-beta\ngroup a[X](cloud)\n", false},
	{"edge-gt", "architecture-beta\nservice a(server)\nservice b(server)\na:R > L:b\n", false},
	{"edge-dash-gt-space", "architecture-beta\nservice a(server)\nservice b(server)\na:R -- > L:b\n", true},
	{"edge-longdash", "architecture-beta\nservice a(server)\nservice b(server)\na:R --- L:b\n", false},
	{"edge-title-spaces", "architecture-beta\nservice a(server)\nservice b(server)\na:R - [x] - L:b\n", true},
	{"edge-title-nobracket", "architecture-beta\nservice a(server)\nservice b(server)\na:R -x- L:b\n", false},
	{"edge-title-quoted", "architecture-beta\nservice a(server)\nservice b(server)\na:R -[\"x y\"]- L:b\n", true},
	{"edge-title-sq", "architecture-beta\nservice a(server)\nservice b(server)\na:R -['x y']- L:b\n", true},
	{"edge-title-badquote", "architecture-beta\nservice a(server)\nservice b(server)\na:R -[\"x]- L:b\n", true},
	{"group-mod-spaced", "architecture-beta\nservice a(server)\nservice b(server)\na{ group }:R -- L:b\n", false},
	{"group-mod-after-dir", "architecture-beta\nservice a(server)\nservice b(server)\na:R{group} -- L:b\n", false},
	{"leading-ws-stmt", "architecture-beta\n   service a(server)\n", true},
	{"title-trailing-ws", "architecture-beta\nservice a(server)[ X ]\n", true},
	{"title-quoted-trailing", "architecture-beta\nservice a(server)[ \"X\" ]\n", true},
	{"str-quote-title", "architecture-beta\nservice a(server)[\"he said \\\"x\\\"\"]\n", true},
	{"junction-in", "architecture-beta\ngroup g[G]\njunction j in g\n", true},
	{"align-column", "architecture-beta\nservice a(server)\nservice b(server)\nalign column a b\n", true},
	{"align-3", "architecture-beta\nservice a(server)\nservice b(server)\nservice c(server)\nalign row a b c\n", true},
	{"align-kw-case", "architecture-beta\nservice a(server)\nservice b(server)\nalign Row a b\n", false},
	{"Group-case", "architecture-beta\nGroup g[G]\n", false},
	{"service-str-icon-both", "architecture-beta\nservice a \"t\" (server)\n", false},
	{"nl-in-title", "architecture-beta\nservice a(server)[a\nb]\n", false},
	{"nested-3", "architecture-beta\ngroup a[A]\ngroup b[B] in a\ngroup c[C] in b\nservice s(server) in c\n", true},
	{"edge-between-groups-ids", "architecture-beta\ngroup a[A]\ngroup b[B]\nservice s(server) in a\nservice t(server) in b\ns{group}:R -- L:t{group}\n", true},
	{"edge-modifier-nodeparent-null", "architecture-beta\ngroup a[A]\nservice s(server) in a\nservice t(server)\ns{group}:R -- L:t{group}\n", true},
	{"acc-title-nospace", "architecture-beta\naccTitle:abc\nservice a(server)\n", true},
	{"acc-title-nocolon", "architecture-beta\naccTitle abc\nservice a(server)\n", false},
	{"accdescr-nocolon", "architecture-beta\naccDescr abc\nservice a(server)\n", false},
	{"title-then-text-comment", "architecture-beta\ntitle A %% c\nservice a(server)\n", true},
	{"empty-service-edge-mixed", "architecture-beta\nservice a(server)\nservice b(server)\na:R -- L:b {group}\n", true},
	{"lone-group-kw", "architecture-beta\ngroup\n", false},
	{"many-newlines", "architecture-beta\n\n\n\nservice a(server)\n\n\n", true},
	{"service-dup-after-group", "architecture-beta\ngroup a[A]\nservice a(server)\n", false},
	{"edge-self-parent", "architecture-beta\nservice a(server) in a\n", false},
	{"lhs-into", "architecture-beta\nservice a(server)\nservice b(server)\na:R<-- L:b\n", true},
}
