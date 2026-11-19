package railroad_test

import (
	"strconv"
	"strings"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	model "github.com/gosuda/elegant-mermaid/internal/model/railroad"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/railroad"
)

func signature(node model.Node) string {
	switch v := node.(type) {
	case *model.Terminal:
		return "T(" + strconv.Quote(v.Value) + ")"
	case *model.NonTerminal:
		return "N(" + v.Name + ")"
	case *model.Special:
		return "S(" + strconv.Quote(v.Text) + ")"
	case *model.Sequence:
		return "seq[" + joinNodes(v.Elements) + "]"
	case *model.Choice:
		return "ch[" + joinNodes(v.Alternatives) + "]"
	case *model.Optional:
		return "opt(" + signature(v.Element) + ")"
	case *model.Repetition:
		max := "inf"
		if v.Max != model.Unbounded {
			max = strconv.FormatInt(v.Max, 10)
		}
		return "rep" + strconv.FormatInt(v.Min, 10) + "-" + max + "(" + signature(v.Element) + ")"
	}
	return "?"
}

func joinNodes(nodes []model.Node) string {
	parts := make([]string, len(nodes))
	for i, node := range nodes {
		parts[i] = signature(node)
	}
	return strings.Join(parts, " ")
}

func resolve(src string) (string, []diag.Diagnostic) {
	text := []byte(src)
	prep := syntax.Preprocess(text)
	ast, parsed := parser.Parse(text, prep.Removed)
	m, resolved := model.Resolve(ast)
	var out []string
	if m.Title != "" {
		out = append(out, "title="+strconv.Quote(m.Title))
	}
	if m.AccTitle != "" {
		out = append(out, "accT="+strconv.Quote(m.AccTitle))
	}
	if m.AccDescr != "" {
		out = append(out, "accD="+strconv.Quote(m.AccDescr))
	}
	for _, rule := range m.Rules {
		out = append(out, rule.Name+"="+signature(rule.Definition))
	}
	return strings.Join(out, " ; "), append(append(prep.Diags, parsed...), resolved...)
}

func hasError(ds []diag.Diagnostic) bool {
	for _, d := range ds {
		if d.Severity == diag.SeverityError {
			return true
		}
	}
	return false
}

const reject = "<reject>"

var upstreamCases = []struct {
	name, src, want string
}{
	{"constructor entity literal", "railroad-beta\nr = terminal(\"a#amp;b\") ;", `r=T("a#amp;b")`},
	{"constructor string spans lines", "railroad-beta\nr = terminal(\"a\nb\") ;", `r=T("a\nb")`},
	{"constructor escaped quote", "railroad-beta\nr = terminal(\"a\\\"b\") ;", `r=T("a\"b")`},
	{"constructor escaped newline", "railroad-beta\nr = terminal('a\\nb') ;", `r=T("a\nb")`},
	{"constructor unterminated string", "railroad-beta\nr = terminal(\"abc) ;", reject},
	{"constructor keyword as rule name", "railroad-beta\nsequence = terminal(\"a\") ;", reject},
	{"constructor keyword prefix is an identifier", "railroad-beta\nsequencex = terminal(\"a\") ;", `sequencex=T("a")`},
	{"title prefix splits an identifier", "railroad-beta\ntitles = terminal(\"a\") ;", `s=T("a")`},
	{"title", "railroad-beta\ntitle Foo\nr = terminal(\"a\") ;", `title="Foo" ; r=T("a")`},
	{"title after a rule", "railroad-beta\nr = terminal(\"a\") ;\ntitle Foo\n", reject},
	{"title on the header line", "railroad-beta title X\nr = terminal(\"a\") ;", `title="X" ; r=T("a")`},
	{"accessibility lines", "railroad-beta\naccTitle: T1\naccDescr: D1\nr = terminal(\"a\") ;", `accT="T1" ; accD="D1" ; r=T("a")`},
	{"accessibility block", "railroad-beta\naccDescr {\n  line1\n\n  line2\n}\nr = terminal(\"a\") ;", `accD="line1\nline2" ; r=T("a")`},
	{"accessibility block unterminated", "railroad-beta\naccDescr {\nnever closed\nr = terminal(\"a\") ;", reject},
	{"single-child sequence collapses", "railroad-beta\nr = sequence(terminal(\"a\")) ;", `r=T("a")`},
	{"single-child choice collapses", "railroad-beta\nr = choice(terminal(\"a\")) ;", `r=T("a")`},
	{"empty sequence", "railroad-beta\nr = sequence() ;", reject},
	{"two rules", "railroad-beta\nr = terminal(\"a\") ; q = nonterminal(\"r\") ;", `r=T("a") ; q=N(r)`},
	{"duplicate rules stay", "railroad-beta\nr = terminal(\"a\") ;\nr = terminal(\"b\") ;", `r=T("a") ; r=T("b")`},
	{"trailing percent comment", "railroad-beta\nr = terminal(\"a\") ; %% c\n", `r=T("a")`},
	{"block comment between tokens", "railroad-beta\nr = terminal(\"a\") /* c */ ;", `r=T("a")`},
	{"block comment inside call", "railroad-beta\nr = terminal(\"a\" /* c */ ) ;", `r=T("a")`},
	{"header only", "railroad-beta\n", ""},
	{"header without newline", "railroad-beta", ""},
	{"special", "railroad-beta\nr = special(\"x y\") ;", `r=S("x y")`},
	{"unquoted argument", "railroad-beta\nr = terminal(a) ;", reject},
	{"junk after the last rule", "railroad-beta\nr = terminal(\"a\") ; garbage", reject},
	{"stray characters", "railroad-beta\n@@\nr = terminal(\"a\") ;", reject},
	{"header comment", "railroad-beta %% c\nr = terminal(\"a\") ;", `r=T("a")`},
	{"frontmatter", "---\ntitle: x\n---\nrailroad-beta\nr = terminal(\"a\") ;", `r=T("a")`},
	{"yaml block between rules", "railroad-beta\nr = terminal(\"a\") ;\n---\nx\n---\ns = terminal(\"b\") ;", `r=T("a") ; s=T("b")`},
	{"title with escapes", "railroad-beta\ntitle \"a\\nb\"\nr = terminal(\"a\") ;", `title="a\nb" ; r=T("a")`},
	{"title with spaces", "railroad-beta\ntitle    spaced     out   \nr = terminal(\"a\") ;", `title="spaced out" ; r=T("a")`},
	{"title stops at percent comment", "railroad-beta\ntitle A %% c\nr = terminal(\"a\") ;", `title="A" ; r=T("a")`},
	{"later description wins", "railroad-beta\naccDescr: one  two\naccDescr: later\nr = terminal(\"a\") ;", `accD="later" ; r=T("a")`},
	{"inline description block", "railroad-beta\naccDescr{ a\n b }\nr = terminal(\"a\") ;", `accD="a\nb" ; r=T("a")`},
	{"description block after a newline", "railroad-beta\naccDescr\n{ a }\nr = terminal(\"a\") ;", `accD="a" ; r=T("a")`},
	{"accTitle collapses blanks", "railroad-beta\naccTitle : T  1 \nr = terminal(\"a\") ;", `accT="T 1" ; r=T("a")`},
	{"empty title", "railroad-beta\ntitle\nr = terminal(\"a\") ;", `r=T("a")`},
	{"later empty title wins", "railroad-beta title A\ntitle\nr = terminal(\"a\") ;", `r=T("a")`},
	{"escaped backslash", "railroad-beta\nr = terminal(\"a\\\\\") ;", `r=T("a\\")`},
	{"unknown escape drops the backslash", "railroad-beta\nr = terminal(\"a\\q\") ;", `r=T("aq")`},
	{"empty terminal", "railroad-beta\nr = terminal(\"\") ;", `r=T("")`},
	{"header with a dot", "railroad-beta.x\nr = terminal(\"a\") ;", reject},
	{"header reused as a rule name", "railroad-beta\nrailroad-beta = terminal(\"a\") ;", reject},
	{"ebnf equals", "railroad-ebnf-beta\nr = \"a\" \"b\" ;", `r=seq[T("a") T("b")]`},
	{"ebnf bare terms", "railroad-ebnf-beta\nr = a b c ;", `r=seq[N(a) N(b) N(c)]`},
	{"ebnf colon equals", "railroad-ebnf-beta\nr ::= a, b | c ;", `r=ch[seq[N(a) N(b)] N(c)]`},
	{"ebnf lone colon", "railroad-ebnf-beta\nr : \"a\" ;", reject},
	{"ebnf colon-equals typo", "railroad-ebnf-beta\nr := a ;", reject},
	{"ebnf postfix question", "railroad-ebnf-beta\nr = a ? ;", `r=opt(N(a))`},
	{"ebnf special beats question", "railroad-ebnf-beta\nr = a? , b? ;", `r=seq[N(a) S(", b")]`},
	{"ebnf special after question", "railroad-ebnf-beta\nr = a ? b ? ;", `r=seq[N(a) S("b")]`},
	{"ebnf special", "railroad-ebnf-beta\nr = ? x ? ;", `r=S("x")`},
	{"ebnf blank special", "railroad-ebnf-beta\nr = ?   ? ;", reject},
	{"ebnf iso comment", "railroad-ebnf-beta\nr = a (* c *) b ;", `r=seq[N(a) N(b)]`},
	{"ebnf slash comment", "railroad-ebnf-beta\nr = a /* c */ b ;", `r=seq[N(a) N(b)]`},
	{"ebnf unclosed iso comment", "railroad-ebnf-beta\nr = a (* unclosed b ;", reject},
	{"ebnf exception", "railroad-ebnf-beta\nr = (a | b)* - c ;", `r=seq[rep0-inf(ch[N(a) N(b)]) T("-") N(c)]`},
	{"ebnf chained exception", "railroad-ebnf-beta\nr = a - b - c ;", `r=seq[seq[N(a) T("-") N(b)] T("-") N(c)]`},
	{"ebnf postfix chain", "railroad-ebnf-beta\nr = a*+? ;", `r=opt(rep1-inf(rep0-inf(N(a))))`},
	{"ebnf group forms", "railroad-ebnf-beta\nr = [a] {b} (c) ;", `r=seq[opt(N(a)) rep0-inf(N(b)) N(c)]`},
	{"ebnf double bar", "railroad-ebnf-beta\nr = a | | b ;", reject},
	{"ebnf empty body", "railroad-ebnf-beta\nr = ;", reject},
	{"ebnf alternatives and next rule", "railroad-ebnf-beta\nr = \"a\" , \"b\" | 'c' ;\ns = r ;", `r=ch[seq[T("a") T("b")] T("c")] ; s=N(r)`},
	{"ebnf rule on one line", "railroad-ebnf-beta\nr ::= a ; s = b ;", `r=N(a) ; s=N(b)`},
	{"ebnf hyphenated identifier", "railroad-ebnf-beta\nr = a-b ;", `r=N(a-b)`},
	{"ebnf spaced exception", "railroad-ebnf-beta\nr = a - b ;", `r=seq[N(a) T("-") N(b)]`},
	{"ebnf unspaced exception", "railroad-ebnf-beta\nr = a -b ;", `r=seq[N(a) T("-") N(b)]`},
	{"ebnf trailing comma", "railroad-ebnf-beta\nr = a, ;", reject},
	{"ebnf unclosed group", "railroad-ebnf-beta\nr = (a ;", reject},
	{"ebnf yaml block", "railroad-ebnf-beta\nr = a ;\n---\nx\n---\ns = b ;", `r=N(a) ; s=N(b)`},
	{"abnf finite repeat", "railroad-abnf-beta\nr = 1*3a ;", `r=rep1-3(N(a))`},
	{"abnf repeat forms", "railroad-abnf-beta\nr = 2a 3\"b\" *c 0*1d 1*e 3*2f ;", `r=seq[rep2-2(N(a)) rep3-3(T("b")) rep0-inf(N(c)) opt(N(d)) rep1-inf(N(e)) rep3-2(N(f))]`},
	{"abnf numeric values", "railroad-abnf-beta\nr = %x41 %x41-5A %x41.42.43 %d65 %b1010 ;", `r=seq[T("%x41") T("%x41-5A") T("%x41.42.43") T("%d65") T("%b1010")]`},
	{"abnf alternation", "railroad-abnf-beta\nr = a / b c / d ;", `r=ch[N(a) seq[N(b) N(c)] N(d)]`},
	{"abnf backslash stays", "railroad-abnf-beta\nr = \"a\\b\" ;", `r=T("a\\b")`},
	{"abnf comment line between rules", "railroad-abnf-beta\nr = a ;\n; comment\ns = b ;", `r=N(a) ; s=N(b)`},
	{"abnf terminator on its own line", "railroad-abnf-beta\nr = a\n  ;\ns = b ;", `r=N(a) ; s=N(b)`},
	{"abnf crlf", "railroad-abnf-beta\nr = a ;\r\ns = b ;", `r=N(a) ; s=N(b)`},
	{"abnf groups", "railroad-abnf-beta\nr = ( a / b ) [ c ] ;", `r=seq[ch[N(a) N(b)] opt(N(c))]`},
	{"abnf repeat on groups", "railroad-abnf-beta\nr = 1*(a) 2[b] ;", `r=seq[rep1-inf(N(a)) rep2-2(opt(N(b)))]`},
	{"abnf numval stops at a non-hex digit", "railroad-abnf-beta\nr = %x4G ;", `r=seq[T("%x4") N(G)]`},
	{"abnf zero maximum", "railroad-abnf-beta\nr = 0*0a ;", `r=rep0-0(N(a))`},
	{"abnf bare star", "railroad-abnf-beta\nr = *a ;", `r=rep0-inf(N(a))`},
	{"abnf leading zeros", "railroad-abnf-beta\nr = 007*0009 a ;", `r=rep7-9(N(a))`},
	{"abnf comment after terminator", "railroad-abnf-beta\nr = \"a\" ; \nq = \"b\" ; x\n", reject},
	{"abnf comment swallows the next line start", "railroad-abnf-beta\nr = \"a\" ; c\nq = \"b\" ;\n", reject},
	{"abnf title keeps backslashes", "railroad-abnf-beta\ntitle \"a\\nb\"\nr = a ;", `title="a\\nb" ; r=N(a)`},
	{"peg rule", "railroad-peg-beta\nr <- a ;", `r=N(a)`},
	{"peg predicates and suffixes", "railroad-peg-beta\nr <- &a b !c d? e* f+ ;", `r=seq[S("&a") N(b) S("!c") opt(N(d)) rep0-inf(N(e)) rep1-inf(N(f))]`},
	{"peg lookahead labels", "railroad-peg-beta\nr <- &(a / b) !\"x\" &. ;", `r=seq[S("&(...)") S("!\"x\"") S("&.")]`},
	{"peg group suffix", "railroad-peg-beta\nr <- (a b)+ / c ;", `r=ch[rep1-inf(seq[N(a) N(b)]) N(c)]`},
	{"peg any", "railroad-peg-beta\nr <- . ;", `r=S(".")`},
	{"peg comment", "railroad-peg-beta\nr <- a # comment\n b ;", `r=seq[N(a) N(b)]`},
	{"peg double prefix", "railroad-peg-beta\nr <- &&a ;", reject},
	{"peg double suffix", "railroad-peg-beta\nr <- a?* ;", reject},
	{"peg wrong arrow", "railroad-peg-beta\nr = a ;", reject},
	{"peg empty body", "railroad-peg-beta\nr <- ;", reject},
	{"peg title escapes", "railroad-peg-beta\ntitle \"a\\tb\"\nr <- a ;", `title="a\tb" ; r=N(a)`},
}

func TestMatchesUpstream(t *testing.T) {
	for _, c := range upstreamCases {
		t.Run(c.name, func(t *testing.T) {
			got, ds := resolve(c.src)
			if c.want == reject {
				if !hasError(ds) {
					t.Fatalf("accepted, want a rejection; model %s", got)
				}
				return
			}
			if hasError(ds) {
				t.Fatalf("rejected: %v", ds)
			}
			if got != c.want {
				t.Fatalf("got  %s\nwant %s", got, c.want)
			}
		})
	}
}

func errorsOf(ds []diag.Diagnostic) []diag.Diagnostic {
	var out []diag.Diagnostic
	for _, d := range ds {
		if d.Severity == diag.SeverityError {
			out = append(out, d)
		}
	}
	return out
}

func codes(ds []diag.Diagnostic) string {
	out := make([]string, len(ds))
	for i, d := range ds {
		out[i] = d.Code + "@" + strconv.Itoa(d.Span.Start) + "-" + strconv.Itoa(d.Span.End)
	}
	return strings.Join(out, " ")
}

func span(src, text string) string {
	start := strings.Index(src, text)
	return strconv.Itoa(start) + "-" + strconv.Itoa(start+len(text))
}

func TestNoRulesWarning(t *testing.T) {
	_, ds := resolve("railroad-beta\ntitle Empty")
	if got := codes(ds); got != "railroad/no-rules@0-13" {
		t.Fatalf("diagnostics %s", got)
	}
	if ds[0].Severity != diag.SeverityWarning {
		t.Fatalf("severity %v", ds[0].Severity)
	}
}

func TestRepeatMaximumNotice(t *testing.T) {
	src := "railroad-abnf-beta\nr = 1*3a 0*1b *c 2d ;"
	_, ds := resolve(src)
	got := make([]string, len(ds))
	for i, d := range ds {
		got[i] = d.Code + "|" + d.Message + "|" + strconv.Itoa(int(d.Severity)) + "|" + strconv.Itoa(d.Span.Start) + "-" + strconv.Itoa(d.Span.End)
	}
	info := strconv.Itoa(int(diag.SeverityInfo))
	exact := strings.Index(src, "2d")
	want := []string{
		"railroad/repeat-max-ignored|finite repetition maximum 3 is not drawn|" + info + "|" + span(src, "1*3"),
		"railroad/repeat-max-ignored|finite repetition maximum 2 is not drawn|" + info + "|" + strconv.Itoa(exact) + "-" + strconv.Itoa(exact+1),
	}
	if strings.Join(got, "\n") != strings.Join(want, "\n") {
		t.Fatalf("got\n%s\nwant\n%s", strings.Join(got, "\n"), strings.Join(want, "\n"))
	}
}

func TestRecoveryKeepsLaterRules(t *testing.T) {
	got, ds := resolve("railroad-beta\nbad = sequence( ;\nr = terminal(\"a\") ;\nbad2 = terminal(a) ;\ns = terminal(\"b\") ;")
	if got != `r=T("a") ; s=T("b")` {
		t.Fatalf("model %s", got)
	}
	if len(ds) != 2 || ds[0].Code != "railroad/unexpected-token" || ds[1].Code != "railroad/unexpected-token" {
		t.Fatalf("diagnostics %s", codes(ds))
	}
}

func TestUnknownStatements(t *testing.T) {
	src := "railroad-beta\nr = terminal(\"a\") ;\naccTitle: x\n= ;\ns = terminal(\"b\") ;"
	_, ds := resolve(src)
	want := "railroad/unknown-statement@" + span(src, "accTitle: x") + " railroad/unknown-statement@" + span(src, "= ;")
	if got := codes(errorsOf(ds)); got != want {
		t.Fatalf("got %s want %s", got, want)
	}
	if ds[0].Message != "unknown statement accTitle: x" {
		t.Fatalf("message %q", ds[0].Message)
	}
}

func TestUnterminatedNames(t *testing.T) {
	for _, c := range []struct{ src, opener string }{
		{"railroad-beta\nr = terminal(\"abc", `"`},
		{"railroad-beta\nr = terminal('abc", `'`},
		{"railroad-beta\nr = /* abc", "/*"},
		{"railroad-beta\naccDescr {\nabc", "{"},
		{"railroad-abnf-beta\nr = \"abc", `"`},
	} {
		_, ds := resolve(c.src)
		errs := errorsOf(ds)
		if len(errs) != 1 || errs[0].Code != "railroad/unterminated" || errs[0].Message != "unterminated "+c.opener {
			t.Fatalf("%q: %s", c.src, codes(ds))
		}
		if errs[0].Span.End != len(c.src) {
			t.Fatalf("%q: span %v", c.src, errs[0].Span)
		}
	}
}

func TestUnexpectedTokenListsSortedKinds(t *testing.T) {
	for _, c := range []struct{ src, want string }{
		{"railroad-beta\nr = ;", "unexpected ;, expected one of: choice, nonterminal, oneOrMore, optional, sequence, special, terminal, zeroOrMore"},
		{"railroad-peg-beta\nr = a ;", "unexpected =, expected one of: <-"},
		{"railroad-ebnf-beta\nr = a", "unexpected EOF, expected one of: ;"},
		{"railroad-ebnf-beta\nr =", "unexpected EOF, expected one of: (, EBNF_ID, EBNF_SPECIAL_SEQUENCE, EBNF_STRING, [, {"},
	} {
		_, ds := resolve(c.src)
		errs := errorsOf(ds)
		if len(errs) != 1 || errs[0].Message != c.want {
			t.Fatalf("%q: %v", c.src, errs)
		}
	}
}

func TestNestingLimit(t *testing.T) {
	deep := func(levels int) string {
		return "railroad-beta\nr = " + strings.Repeat("optional(", levels) + `terminal("a")` + strings.Repeat(")", levels) + " ;"
	}
	if _, ds := resolve(deep(64)); hasError(ds) {
		t.Fatalf("64 levels rejected: %v", ds)
	}
	_, ds := resolve(deep(65))
	if errs := errorsOf(ds); len(errs) != 1 || errs[0].Code != "limit/nesting-depth" {
		t.Fatalf("65 levels: %s", codes(ds))
	}
	postfix := "railroad-ebnf-beta\nr = a" + strings.Repeat("*+", 33) + " ;"
	if _, ds := resolve(postfix); len(errorsOf(ds)) != 1 || errorsOf(ds)[0].Code != "limit/nesting-depth" {
		t.Fatalf("66 postfix levels: %s", codes(ds))
	}
	groups := "railroad-ebnf-beta\nr = " + strings.Repeat("(", 65) + "a" + strings.Repeat(")", 65) + " ;"
	if _, ds := resolve(groups); len(errorsOf(ds)) != 1 || errorsOf(ds)[0].Code != "limit/nesting-depth" {
		t.Fatalf("65 groups: %s", codes(ds))
	}
}

func TestHeaderCaseFolds(t *testing.T) {
	for _, header := range []string{"RAILROAD-BETA", "Railroad-Beta"} {
		got, ds := resolve(header + "\nr = terminal(\"a\") ;")
		if hasError(ds) || got != `r=T("a")` {
			t.Fatalf("%s: %s %v", header, got, ds)
		}
	}
}
