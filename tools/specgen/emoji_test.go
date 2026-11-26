package main

import (
	"go/format"
	"os"
	"path/filepath"
	"testing"

	"github.com/stretchr/testify/require"
	"golang.org/x/image/font/sfnt"
)

func loadEmojiFont(t *testing.T, root string) []byte {
	t.Helper()
	data, err := os.ReadFile(filepath.Join(root, "spec", "data", "fonts", "NotoEmoji-Regular.ttf"))
	require.NoError(t, err)
	require.NotEmpty(t, data)
	return data
}

func collectEmojiForTest(t *testing.T) (*emojiSeqTable, *emojiPresentationTable) {
	t.Helper()
	root := dataRoot(t)
	in := &inputs{root: root}
	in.emoji = loadUCDBytes(t, root, "emoji-data.txt")
	in.emojiTTF = loadEmojiFont(t, root)
	seq, pres, err := collectEmojiTables(in)
	require.NoError(t, err)
	return seq, pres
}

func findEmojiSequence(seqs []emojiSequence, scalars ...uint32) (uint16, bool) {
	for _, s := range seqs {
		if len(s.scalars) != len(scalars) {
			continue
		}
		match := true
		for i, cp := range scalars {
			if s.scalars[i] != cp {
				match = false
				break
			}
		}
		if match {
			return s.glyph, true
		}
	}
	return 0, false
}

func flagJapanGlyph(t *testing.T, fontBytes []byte) uint16 {
	t.Helper()
	font, err := sfnt.Parse(fontBytes)
	require.NoError(t, err)
	for g := 0; g < font.NumGlyphs(); g++ {
		name, err := font.GlyphName(nil, sfnt.GlyphIndex(g))
		require.NoError(t, err)
		if name == "flagJapan" {
			return uint16(g)
		}
	}
	t.Fatal("glyph flagJapan not found")
	return 0
}

func TestEmojiSequencesFlagJapan(t *testing.T) {
	root := dataRoot(t)
	seq, _ := collectEmojiForTest(t)
	glyph, ok := findEmojiSequence(seq.sequences, 0x1F1EF, 0x1F1F5)
	require.True(t, ok, "flag sequence missing")
	require.Equal(t, flagJapanGlyph(t, loadEmojiFont(t, root)), glyph)
}

func TestEmojiSequencesFamily(t *testing.T) {
	seq, _ := collectEmojiForTest(t)
	_, ok := findEmojiSequence(seq.sequences, 0x1F468, 0x200D, 0x1F469, 0x200D, 0x1F467)
	require.True(t, ok, "family sequence missing")
}

func TestEmojiSequencesThumbTone(t *testing.T) {
	seq, _ := collectEmojiForTest(t)
	_, ok := findEmojiSequence(seq.sequences, 0x1F44D, 0x1F3FD)
	require.True(t, ok, "thumb with skin tone missing")
}

func TestEmojiSequencesSortedUnique(t *testing.T) {
	seq, _ := collectEmojiForTest(t)
	require.NotEmpty(t, seq.sequences)
	seen := make(map[string]struct{}, len(seq.sequences))
	for i, s := range seq.sequences {
		require.GreaterOrEqual(t, len(s.scalars), 2, "sequence %d below length 2", i)
		if i > 0 {
			require.Equal(t, -1, compareEmojiSequences(seq.sequences[i-1], s), "table not strictly sorted at %d", i)
		}
		key := glyphKey(s.scalars)
		_, dup := seen[key]
		require.False(t, dup, "duplicate sequence %s", key)
		seen[key] = struct{}{}
	}
}

func TestEmojiPresentationHeart(t *testing.T) {
	_, pres := collectEmojiForTest(t)
	require.True(t, inEmojiPresentation(pres.ranges, 0x1F600), "U+1F600 must have Emoji_Presentation")
	require.False(t, inEmojiPresentation(pres.ranges, 0x2764), "U+2764 must not have Emoji_Presentation")
}

func TestEmojiGeneratedFilesMatch(t *testing.T) {
	root := dataRoot(t)
	seq, pres := collectEmojiForTest(t)
	compareGeneratedGo(t, root, seq)
	compareGeneratedGo(t, root, pres)
	compareGeneratedRust(t, root, seq)
	compareGeneratedRust(t, root, pres)
	for _, table := range []renderable{seq, pres} {
		lean, err := table.renderLean()
		require.NoError(t, err)
		require.Empty(t, lean, "%s must declare no Lean output", table.fileName())
	}
	require.NoFileExists(t, filepath.Join(root, "proofs", "Elegant", "Gen", "Emojiseq.lean"))
	require.NoFileExists(t, filepath.Join(root, "proofs", "Elegant", "Gen", "Emojipresentation.lean"))
}

func compareGeneratedGo(t *testing.T, root string, table renderable) {
	t.Helper()
	raw, err := table.renderGo()
	require.NoError(t, err)
	formatted, err := format.Source(raw)
	require.NoError(t, err)
	onDisk, err := os.ReadFile(filepath.Join(root, "internal", "gen", table.fileName()+".go"))
	require.NoError(t, err)
	require.Equal(t, string(formatted), string(onDisk), "internal/gen/%s.go differs", table.fileName())
}

func compareGeneratedRust(t *testing.T, root string, table renderable) {
	t.Helper()
	raw, err := table.renderRust()
	require.NoError(t, err)
	formatted, err := formatRust(raw)
	require.NoError(t, err)
	onDisk, err := os.ReadFile(filepath.Join(root, "crates", "elegant-mermaid", "src", "gen", table.fileName()+".rs"))
	require.NoError(t, err)
	require.Equal(t, string(formatted), string(onDisk), "src/gen/%s.rs differs", table.fileName())
}

func glyphKey(scalars []uint32) string {
	key := make([]byte, 0, len(scalars)*5)
	for _, cp := range scalars {
		key = append(key, byte(cp), byte(cp>>8), byte(cp>>16), byte(cp>>24), ';')
	}
	return string(key)
}

func inEmojiPresentation(ranges []tableRange, cp uint32) bool {
	for _, r := range ranges {
		if cp >= r.Lo && cp <= r.Hi {
			return true
		}
	}
	return false
}
