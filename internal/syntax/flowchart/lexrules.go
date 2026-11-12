package flowchart

import "slices"

type modeSet uint32

func modeBits(ms ...lexMode) modeSet {
	var s modeSet
	for _, m := range ms {
		s |= 1 << m
	}
	return s
}

var everyMode = modeBits(
	modeInitial, modeString, modeMDString, modeAccTitle, modeAccDescr, modeAccDescrMultiline,
	modeDir, modeText, modeEllipseText, modeTrapText, modeEdgeText, modeThickEdgeText,
	modeDottedEdgeText, modeClick, modeCallbackName, modeCallbackArgs, modeShapeData, modeShapeDataStr,
)

type lexRule struct {
	match      func(l *lexer, limit int) int
	kind       TokenKind
	act        lexAct
	push       lexMode
	pushOnPush bool
	pop        bool
	allowEmpty bool
	modes      modeSet
}

var globalRules = []lexRule{
	{match: keywordSpacesColonSpaces("accTitle"), kind: TokAccTitle, pushOnPush: true, push: modeAccTitle, modes: modeBits(modeInitial)},
	{match: accValueRun, kind: TokAccTitleValue, pop: true, allowEmpty: true, modes: modeBits(modeAccTitle)},
	{match: keywordSpacesColonSpaces("accDescr"), kind: TokAccDescr, pushOnPush: true, push: modeAccDescr, modes: modeBits(modeInitial)},
	{match: accValueRun, kind: TokAccDescrValue, pop: true, allowEmpty: true, modes: modeBits(modeAccDescr)},
	{match: keywordSpacesBrace("accDescr"), act: actAccBlockOpen, modes: modeBits(modeInitial)},
	{match: lit("}"), act: actAccBlockClose, modes: modeBits(modeAccDescrMultiline)},
	{match: accBlockRun, kind: TokAccDescrMultilineValue, modes: modeBits(modeAccDescrMultiline)},
	{match: lit("@{"), kind: TokShapeData, act: actShapeOpen, modes: modeBits(modeInitial)},
	{match: lit("\""), kind: TokShapeData, pushOnPush: true, push: modeShapeDataStr, modes: modeBits(modeShapeData)},
	{match: lit("\""), kind: TokShapeData, pop: true, modes: modeBits(modeShapeDataStr)},
	{match: shapeQuotedRun, kind: TokShapeData, act: actShapeRun, modes: modeBits(modeShapeDataStr)},
	{match: shapePlainRun, kind: TokShapeData, modes: modeBits(modeShapeData)},
	{match: lit("}"), act: actLeaveOnly, modes: modeBits(modeShapeData)},
	{match: keywordThenSpace("call"), pushOnPush: true, push: modeCallbackName, modes: modeBits(modeInitial)},
	{match: emptyCallArgs, act: actLeaveOnly, modes: modeBits(modeCallbackName)},
	{match: lit("("), act: actBeginCallbackArgs, modes: modeBits(modeCallbackName)},
	{match: callbackNameRun, kind: TokCallbackName, modes: modeBits(modeCallbackName)},
	{match: lit(")"), act: actLeaveOnly, modes: modeBits(modeCallbackArgs)},
	{match: callbackArgsRun, kind: TokCallbackArgs, modes: modeBits(modeCallbackArgs)},
	{match: mdStringRun, kind: TokMDStr, modes: modeBits(modeMDString)},
	{match: lit("`\""), act: actCloseMDString, modes: modeBits(modeMDString)},
	{match: lit("\"`"), act: actOpenMDString, modes: everyMode},
	{match: stringRun, kind: TokStr, modes: modeBits(modeString)},
	{match: lit("\""), act: actCloseString, modes: modeBits(modeString)},
	{match: lit("\""), act: actOpenString, modes: everyMode},
	{match: lit("style"), kind: TokStyle, modes: modeBits(modeInitial)},
	{match: lit("default"), kind: TokDefault, modes: modeBits(modeInitial)},
	{match: lit("linkStyle"), kind: TokLinkStyle, modes: modeBits(modeInitial)},
	{match: lit("interpolate"), kind: TokInterpolate, modes: modeBits(modeInitial)},
	{match: lit("classDef"), kind: TokClassDef, modes: modeBits(modeInitial)},
	{match: lit("class"), kind: TokClass, modes: modeBits(modeInitial)},
	{match: hrefKeyword, kind: TokHref, modes: modeBits(modeInitial)},
	{match: keywordThenSpace("click"), pushOnPush: true, push: modeClick, modes: modeBits(modeInitial)},
	{match: anySpaceByte, act: actLeaveOnly, modes: modeBits(modeClick)},
	{match: anyNonSpace, kind: TokClick, modes: modeBits(modeClick)},
	{match: lit("flowchart-elk"), kind: TokGraph, act: actGraph, modes: modeBits(modeInitial)},
	{match: lit("graph"), kind: TokGraph, act: actGraph, modes: modeBits(modeInitial)},
	{match: lit("flowchart"), kind: TokGraph, act: actGraph, modes: modeBits(modeInitial)},
	{match: lit("subgraph"), kind: TokSubgraph, modes: modeBits(modeInitial)},
	{match: endKeyword, kind: TokEnd, modes: modeBits(modeInitial)},
	{match: lit("_self"), kind: TokLinkTarget, modes: modeBits(modeInitial)},
	{match: lit("_blank"), kind: TokLinkTarget, modes: modeBits(modeInitial)},
	{match: lit("_parent"), kind: TokLinkTarget, modes: modeBits(modeInitial)},
	{match: lit("_top"), kind: TokLinkTarget, modes: modeBits(modeInitial)},
	{match: dirNoDir, kind: TokNoDir, pop: true, modes: modeBits(modeDir)},
	{match: dirKeywordRule("LR"), kind: TokDir, pop: true, modes: modeBits(modeDir)},
	{match: dirKeywordRule("RL"), kind: TokDir, pop: true, modes: modeBits(modeDir)},
	{match: dirKeywordRule("TB"), kind: TokDir, pop: true, modes: modeBits(modeDir)},
	{match: dirKeywordRule("BT"), kind: TokDir, pop: true, modes: modeBits(modeDir)},
	{match: dirKeywordRule("TD"), kind: TokDir, pop: true, modes: modeBits(modeDir)},
	{match: dirKeywordRule("BR"), kind: TokDir, pop: true, modes: modeBits(modeDir)},
	{match: dirKeywordRule("<"), kind: TokDir, pop: true, modes: modeBits(modeDir)},
	{match: dirKeywordRule(">"), kind: TokDir, pop: true, modes: modeBits(modeDir)},
	{match: dirKeywordRule("^"), kind: TokDir, pop: true, modes: modeBits(modeDir)},
	{match: dirKeywordRule("v"), kind: TokDir, pop: true, modes: modeBits(modeDir)},
	{match: directionStatement("TB"), kind: TokDirectionTB, modes: modeBits(modeInitial)},
	{match: directionStatement("BT"), kind: TokDirectionBT, modes: modeBits(modeInitial)},
	{match: directionStatement("RL"), kind: TokDirectionRL, modes: modeBits(modeInitial)},
	{match: directionStatement("LR"), kind: TokDirectionLR, modes: modeBits(modeInitial)},
	{match: directionStatement("TD"), kind: TokDirectionTD, modes: modeBits(modeInitial)},
	{match: linkIDRule, kind: TokLinkID, modes: modeBits(modeInitial)},
	{match: numRule, kind: TokNum, modes: modeBits(modeInitial)},
	{match: lit("#"), kind: TokBrkt, modes: modeBits(modeInitial)},
	{match: colonRun, kind: TokStyleSeparator, modes: modeBits(modeInitial)},
	{match: lit(":"), kind: TokColon, modes: modeBits(modeInitial)},
	{match: lit("&"), kind: TokAmp, modes: modeBits(modeInitial)},
	{match: lit(";"), kind: TokSemi, modes: modeBits(modeInitial)},
	{match: lit(","), kind: TokComma, modes: modeBits(modeInitial)},
	{match: lit("*"), kind: TokMult, modes: modeBits(modeInitial)},
	{match: linkRule, kind: TokLink, pop: true, modes: modeBits(modeInitial, modeEdgeText)},
	{match: startLinkRule, kind: TokStartLink, pushOnPush: true, push: modeEdgeText, modes: modeBits(modeInitial)},
	{match: oneByteUnless('-'), kind: TokEdgeText, modes: modeBits(modeEdgeText)},
	{match: thickLinkRule, kind: TokLink, pop: true, modes: modeBits(modeInitial, modeThickEdgeText)},
	{match: thickStartLinkRule, kind: TokStartLink, pushOnPush: true, push: modeThickEdgeText, modes: modeBits(modeInitial)},
	{match: oneByteUnless('='), kind: TokEdgeText, modes: modeBits(modeThickEdgeText)},
	{match: dottedLinkRule, kind: TokLink, pop: true, modes: modeBits(modeInitial, modeDottedEdgeText)},
	{match: dottedStartLinkRule, kind: TokStartLink, pushOnPush: true, push: modeDottedEdgeText, modes: modeBits(modeInitial)},
	{match: oneByteUnless('.'), kind: TokEdgeText, modes: modeBits(modeDottedEdgeText)},
	{match: invisibleLinkRule, kind: TokLink, modes: everyMode},
	{match: ellipseEndRule, kind: TokEllipseEnd, pop: true, modes: modeBits(modeEllipseText)},
	{match: ellipseTextRun, kind: TokText, modes: modeBits(modeEllipseText)},
	{match: lit("(-"), kind: TokEllipseStart, pushOnPush: true, push: modeEllipseText, modes: everyMode},
	{match: lit("])"), kind: TokStadiumEnd, pop: true, modes: modeBits(modeText)},
	{match: lit("(["), kind: TokStadiumStart, pushOnPush: true, push: modeText, modes: everyMode},
	{match: lit("]]"), kind: TokSubroutineEnd, pop: true, modes: modeBits(modeText)},
	{match: lit("[["), kind: TokSubroutineStart, pushOnPush: true, push: modeText, modes: everyMode},
	{match: lit("[|"), kind: TokVertexWithPropsStart, modes: modeBits(modeInitial)},
	{match: lit(")]"), kind: TokCylinderEnd, pop: true, modes: modeBits(modeText)},
	{match: lit("[("), kind: TokCylinderStart, pushOnPush: true, push: modeText, modes: everyMode},
	{match: lit(")))"), kind: TokDoubleCircleEnd, pop: true, modes: modeBits(modeText)},
	{match: lit("((("), kind: TokDoubleCircleStart, pushOnPush: true, push: modeText, modes: everyMode},
	{match: trapEndRule, kind: TokTrapEnd, pop: true, modes: modeBits(modeTrapText)},
	{match: invTrapEndRule, kind: TokInvTrapEnd, pop: true, modes: modeBits(modeTrapText)},
	{match: trapTextRun, kind: TokText, modes: modeBits(modeTrapText)},
	{match: lit("[/"), kind: TokTrapStart, pushOnPush: true, push: modeTrapText, modes: everyMode},
	{match: lit("[\\"), kind: TokInvTrapStart, pushOnPush: true, push: modeTrapText, modes: everyMode},
	{match: lit(">"), kind: TokTagEnd, pushOnPush: true, push: modeText, modes: everyMode},
	{match: lit("<"), kind: TokTagStart, modes: modeBits(modeInitial)},
	{match: lit("^"), kind: TokUp, modes: modeBits(modeInitial)},
	{match: lit("v"), kind: TokDown, modes: modeBits(modeInitial)},
	{match: nodeStringRule, kind: TokNodeString, modes: modeBits(modeInitial)},
	{match: lit("-"), kind: TokMinus, modes: modeBits(modeInitial)},
	{match: unicodeTextRule, kind: TokUnicodeText, modes: modeBits(modeInitial)},
	{match: lit("|"), kind: TokPipe, pop: true, modes: modeBits(modeText)},
	{match: lit("|"), kind: TokPipe, pushOnPush: true, push: modeText, modes: everyMode},
	{match: lit(")"), kind: TokPE, pop: true, modes: modeBits(modeText)},
	{match: lit("("), kind: TokPS, pushOnPush: true, push: modeText, modes: everyMode},
	{match: lit("]"), kind: TokSQE, pop: true, modes: modeBits(modeText)},
	{match: lit("["), kind: TokSQS, pushOnPush: true, push: modeText, modes: everyMode},
	{match: lit("}"), kind: TokDiamondStop, pop: true, modes: modeBits(modeText)},
	{match: lit("{"), kind: TokDiamondStart, pushOnPush: true, push: modeText, modes: everyMode},
	{match: textRun, kind: TokText, modes: modeBits(modeText)},
	{match: newlineRule, kind: TokNewline, modes: modeBits(modeInitial)},
	{match: spaceRule, kind: TokSpace, modes: modeBits(modeInitial)},
}

var perModeRules [modeShapeDataStr + 1][]lexRule

var perModeExpected [modeShapeDataStr + 1][]string

func rulesFor(m lexMode) []lexRule {
	if int(m) > int(modeShapeDataStr) {
		return nil
	}
	if perModeRules[modeInitial] == nil {
		buildModeTables()
	}
	return perModeRules[m]
}

func expectedFor(m lexMode) []string {
	if int(m) > int(modeShapeDataStr) {
		return nil
	}
	if perModeExpected[modeInitial] == nil {
		buildModeTables()
	}
	return perModeExpected[m]
}

func buildModeTables() {
	for m := lexMode(0); m <= modeShapeDataStr; m++ {
		bit := modeSet(1) << m
		var rules []lexRule
		var names []string
		for _, r := range globalRules {
			if r.modes&bit == 0 {
				continue
			}
			rules = append(rules, r)
			if r.kind != TokNone && !slices.Contains(names, r.kind.Name()) {
				names = append(names, r.kind.Name())
			}
		}
		slices.Sort(names)
		perModeRules[m] = rules
		perModeExpected[m] = names
	}
}
