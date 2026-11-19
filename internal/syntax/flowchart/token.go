package flowchart

import "github.com/gosuda/elegant-mermaid/internal/source"

type TokenKind uint8

const (
	TokNone TokenKind = iota
	TokGraph
	TokNoDir
	TokDir
	TokDirectionTB
	TokDirectionBT
	TokDirectionRL
	TokDirectionLR
	TokDirectionTD
	TokSubgraph
	TokEnd
	TokLinkTarget
	TokLinkID
	TokLink
	TokStartLink
	TokEdgeText
	TokText
	TokStr
	TokMDStr
	TokShapeData
	TokNum
	TokBrkt
	TokStyleSeparator
	TokColon
	TokAmp
	TokSemi
	TokComma
	TokMult
	TokMinus
	TokPS
	TokPE
	TokSQS
	TokSQE
	TokDiamondStart
	TokDiamondStop
	TokTagStart
	TokTagEnd
	TokUp
	TokDown
	TokPipe
	TokEllipseStart
	TokEllipseEnd
	TokStadiumStart
	TokStadiumEnd
	TokSubroutineStart
	TokSubroutineEnd
	TokCylinderStart
	TokCylinderEnd
	TokDoubleCircleStart
	TokDoubleCircleEnd
	TokTrapStart
	TokInvTrapStart
	TokTrapEnd
	TokInvTrapEnd
	TokVertexWithPropsStart
	TokStyle
	TokDefault
	TokLinkStyle
	TokInterpolate
	TokClassDef
	TokClass
	TokHref
	TokClick
	TokCallbackName
	TokCallbackArgs
	TokAccTitle
	TokAccTitleValue
	TokAccDescr
	TokAccDescrValue
	TokAccDescrMultilineValue
	TokNodeString
	TokUnicodeText
	TokNewline
	TokSpace
	TokEOF
)

type Token struct {
	Kind       TokenKind
	Text       string
	Span       source.Span
	BRs        []BRPoint
	StringOpen int
}

func (k TokenKind) Name() string {
	switch {
	case k <= TokEnd:
		return headerTokenName(k)
	case k <= TokNum:
		return linkTokenName(k)
	case k <= TokPS:
		return punctuationTokenName(k)
	case k <= TokPipe:
		return basicShapeTokenName(k)
	case k <= TokVertexWithPropsStart:
		return compoundShapeTokenName(k)
	case k <= TokCallbackArgs:
		return statementTokenName(k)
	case k <= TokEOF:
		return annotationTokenName(k)
	}
	return ""
}

func directionName(k TokenKind) string {
	switch k {
	case TokDirectionTB:
		return "direction_tb"
	case TokDirectionBT:
		return "direction_bt"
	case TokDirectionRL:
		return "direction_rl"
	case TokDirectionLR:
		return "direction_lr"
	case TokDirectionTD:
		return "direction_td"
	}
	return ""
}

func graphKeywordName(k TokenKind) string {
	switch k {
	case TokNone:
		return ""
	case TokGraph:
		return "GRAPH"
	case TokNoDir:
		return "NODIR"
	case TokDir:
		return "DIR"
	case TokSubgraph:
		return "subgraph"
	case TokEnd:
		return "end"
	}
	return ""
}

func headerTokenName(k TokenKind) string {
	if name := directionName(k); name != "" {
		return name
	}
	return graphKeywordName(k)
}

func edgeTokenName(k TokenKind) string {
	switch k {
	case TokLinkTarget:
		return "LINK_TARGET"
	case TokLinkID:
		return "LINK_ID"
	case TokLink:
		return "LINK"
	case TokStartLink:
		return "START_LINK"
	case TokEdgeText:
		return "EDGE_TEXT"
	}
	return ""
}

func labelTokenName(k TokenKind) string {
	switch k {
	case TokText:
		return "TEXT"
	case TokStr:
		return "STR"
	case TokMDStr:
		return "MD_STR"
	case TokShapeData:
		return "SHAPE_DATA"
	case TokNum:
		return "NUM"
	}
	return ""
}

func linkTokenName(k TokenKind) string {
	if name := edgeTokenName(k); name != "" {
		return name
	}
	return labelTokenName(k)
}

func separatorTokenName(k TokenKind) string {
	switch k {
	case TokBrkt:
		return "BRKT"
	case TokStyleSeparator:
		return "STYLE_SEPARATOR"
	case TokColon:
		return "COLON"
	case TokAmp:
		return "AMP"
	case TokSemi:
		return "SEMI"
	}
	return ""
}

func operatorTokenName(k TokenKind) string {
	switch k {
	case TokComma:
		return "COMMA"
	case TokMult:
		return "MULT"
	case TokMinus:
		return "MINUS"
	case TokPS:
		return "PS"
	}
	return ""
}

func punctuationTokenName(k TokenKind) string {
	if name := separatorTokenName(k); name != "" {
		return name
	}
	return operatorTokenName(k)
}

func basicShapeTokenNameOpen(k TokenKind) string {
	switch k {
	case TokSQS:
		return "SQS"
	case TokDiamondStart:
		return "DIAMOND_START"
	case TokTagStart:
		return "TAGSTART"
	case TokUp:
		return "UP"
	}
	return ""
}

func basicShapeTokenNameClose(k TokenKind) string {
	switch k {
	case TokPE:
		return "PE"
	case TokSQE:
		return "SQE"
	case TokDiamondStop:
		return "DIAMOND_STOP"
	case TokTagEnd:
		return "TAGEND"
	case TokDown:
		return "DOWN"
	case TokPipe:
		return "PIPE"
	}
	return ""
}

func basicShapeTokenName(k TokenKind) string {
	if name := basicShapeTokenNameOpen(k); name != "" {
		return name
	}
	return basicShapeTokenNameClose(k)
}

func compoundShapeTokenNameOpen(k TokenKind) string {
	switch k {
	case TokEllipseStart:
		return "ELLIPSE_START"
	case TokStadiumStart:
		return "STADIUMSTART"
	case TokSubroutineStart:
		return "SUBROUTINESTART"
	case TokCylinderStart:
		return "CYLINDERSTART"
	case TokDoubleCircleStart:
		return "DOUBLECIRCLESTART"
	case TokTrapStart:
		return "TRAPSTART"
	case TokInvTrapStart:
		return "INVTRAPSTART"
	case TokVertexWithPropsStart:
		return "VERTEX_WITH_PROPS_START"
	}
	return ""
}

func compoundShapeTokenNameClose(k TokenKind) string {
	switch k {
	case TokEllipseEnd:
		return "ELLIPSE_END"
	case TokStadiumEnd:
		return "STADIUMEND"
	case TokSubroutineEnd:
		return "SUBROUTINEEND"
	case TokCylinderEnd:
		return "CYLINDEREND"
	case TokDoubleCircleEnd:
		return "DOUBLECIRCLEEND"
	case TokTrapEnd:
		return "TRAPEND"
	case TokInvTrapEnd:
		return "INVTRAPEND"
	}
	return ""
}

func compoundShapeTokenName(k TokenKind) string {
	if name := compoundShapeTokenNameOpen(k); name != "" {
		return name
	}
	return compoundShapeTokenNameClose(k)
}

func styleTokenName(k TokenKind) string {
	switch k {
	case TokStyle:
		return "STYLE"
	case TokDefault:
		return "DEFAULT"
	case TokLinkStyle:
		return "LINKSTYLE"
	case TokInterpolate:
		return "INTERPOLATE"
	case TokClassDef:
		return "CLASSDEF"
	case TokClass:
		return "CLASS"
	}
	return ""
}

func interactionTokenName(k TokenKind) string {
	switch k {
	case TokHref:
		return "HREF"
	case TokClick:
		return "CLICK"
	case TokCallbackName:
		return "CALLBACKNAME"
	case TokCallbackArgs:
		return "CALLBACKARGS"
	}
	return ""
}

func statementTokenName(k TokenKind) string {
	if name := styleTokenName(k); name != "" {
		return name
	}
	return interactionTokenName(k)
}

func accessibilityTokenName(k TokenKind) string {
	switch k {
	case TokAccTitle:
		return "acc_title"
	case TokAccTitleValue:
		return "acc_title_value"
	case TokAccDescr:
		return "acc_descr"
	case TokAccDescrValue:
		return "acc_descr_value"
	case TokAccDescrMultilineValue:
		return "acc_descr_multiline_value"
	}
	return ""
}

func sourceTokenName(k TokenKind) string {
	switch k {
	case TokNodeString:
		return "NODE_STRING"
	case TokUnicodeText:
		return "UNICODE_TEXT"
	case TokNewline:
		return "NEWLINE"
	case TokSpace:
		return "SPACE"
	case TokEOF:
		return "EOF"
	}
	return ""
}

func annotationTokenName(k TokenKind) string {
	if name := accessibilityTokenName(k); name != "" {
		return name
	}
	return sourceTokenName(k)
}
