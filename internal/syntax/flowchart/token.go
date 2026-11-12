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

var tokenNames = [...]string{
	TokNone:                   "",
	TokGraph:                  "GRAPH",
	TokNoDir:                  "NODIR",
	TokDir:                    "DIR",
	TokDirectionTB:            "direction_tb",
	TokDirectionBT:            "direction_bt",
	TokDirectionRL:            "direction_rl",
	TokDirectionLR:            "direction_lr",
	TokDirectionTD:            "direction_td",
	TokSubgraph:               "subgraph",
	TokEnd:                    "end",
	TokLinkTarget:             "LINK_TARGET",
	TokLinkID:                 "LINK_ID",
	TokLink:                   "LINK",
	TokStartLink:              "START_LINK",
	TokEdgeText:               "EDGE_TEXT",
	TokText:                   "TEXT",
	TokStr:                    "STR",
	TokMDStr:                  "MD_STR",
	TokShapeData:              "SHAPE_DATA",
	TokNum:                    "NUM",
	TokBrkt:                   "BRKT",
	TokStyleSeparator:         "STYLE_SEPARATOR",
	TokColon:                  "COLON",
	TokAmp:                    "AMP",
	TokSemi:                   "SEMI",
	TokComma:                  "COMMA",
	TokMult:                   "MULT",
	TokMinus:                  "MINUS",
	TokPS:                     "PS",
	TokPE:                     "PE",
	TokSQS:                    "SQS",
	TokSQE:                    "SQE",
	TokDiamondStart:           "DIAMOND_START",
	TokDiamondStop:            "DIAMOND_STOP",
	TokTagStart:               "TAGSTART",
	TokTagEnd:                 "TAGEND",
	TokUp:                     "UP",
	TokDown:                   "DOWN",
	TokPipe:                   "PIPE",
	TokEllipseStart:           "ELLIPSE_START",
	TokEllipseEnd:             "ELLIPSE_END",
	TokStadiumStart:           "STADIUMSTART",
	TokStadiumEnd:             "STADIUMEND",
	TokSubroutineStart:        "SUBROUTINESTART",
	TokSubroutineEnd:          "SUBROUTINEEND",
	TokCylinderStart:          "CYLINDERSTART",
	TokCylinderEnd:            "CYLINDEREND",
	TokDoubleCircleStart:      "DOUBLECIRCLESTART",
	TokDoubleCircleEnd:        "DOUBLECIRCLEEND",
	TokTrapStart:              "TRAPSTART",
	TokInvTrapStart:           "INVTRAPSTART",
	TokTrapEnd:                "TRAPEND",
	TokInvTrapEnd:             "INVTRAPEND",
	TokVertexWithPropsStart:   "VERTEX_WITH_PROPS_START",
	TokStyle:                  "STYLE",
	TokDefault:                "DEFAULT",
	TokLinkStyle:              "LINKSTYLE",
	TokInterpolate:            "INTERPOLATE",
	TokClassDef:               "CLASSDEF",
	TokClass:                  "CLASS",
	TokHref:                   "HREF",
	TokClick:                  "CLICK",
	TokCallbackName:           "CALLBACKNAME",
	TokCallbackArgs:           "CALLBACKARGS",
	TokAccTitle:               "acc_title",
	TokAccTitleValue:          "acc_title_value",
	TokAccDescr:               "acc_descr",
	TokAccDescrValue:          "acc_descr_value",
	TokAccDescrMultilineValue: "acc_descr_multiline_value",
	TokNodeString:             "NODE_STRING",
	TokUnicodeText:            "UNICODE_TEXT",
	TokNewline:                "NEWLINE",
	TokSpace:                  "SPACE",
	TokEOF:                    "EOF",
}

type Token struct {
	Kind              TokenKind
	Text              string
	Span              source.Span
	BRs               []BRPoint
	SplitContinuation bool
	StringOpen        int
}

func (k TokenKind) Name() string {
	if int(k) < len(tokenNames) {
		return tokenNames[k]
	}
	return ""
}
