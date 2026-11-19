package termgfx

import "strconv"

const (
	sixelRegisters = 216
	sixelCube      = 6
	sixelBand      = 6
	sixelCharBase  = 63
	sixelMinRun    = 4
	sixelLevels    = 5
	sixelRound     = 127
	sixelMax       = 255
)

const sixelHeader = "\x1bP7;0;0q\"1;1;"

type sixelImage struct {
	indices []int
	width   int
	height  int
}

func AppendSixel(dst, rgba []byte, width, height int) ([]byte, error) {
	if width < 0 || height < 0 {
		return dst, ErrSize
	}
	if height != 0 && width > len(rgba)/4/height {
		return dst, ErrBuffer
	}
	image := sixelImage{indices: sixelIndices(rgba, width*height), width: width, height: height}
	dst = appendSixelHeader(dst, width, height)
	for band := range image.bandCount() {
		dst = image.appendBand(dst, band)
		if band != image.bandCount()-1 {
			dst = append(dst, '-')
		}
	}
	return append(dst, stSeq...), nil
}

func appendSixelHeader(dst []byte, width, height int) []byte {
	dst = append(dst, sixelHeader...)
	dst = strconv.AppendInt(dst, int64(width), 10)
	dst = append(dst, ';')
	dst = strconv.AppendInt(dst, int64(height), 10)
	return append(dst, sixelPalette...)
}

func sixelIndices(rgba []byte, pixels int) []int {
	indices := make([]int, pixels)
	for pixel := range pixels {
		base := pixel * 4
		indices[pixel] = sixelIndex(rgba[base], rgba[base+1], rgba[base+2])
	}
	return indices
}

func sixelIndex(r, g, b byte) int {
	return sixelCube*sixelCube*sixelQuantise(r) + sixelCube*sixelQuantise(g) + sixelQuantise(b)
}

func sixelQuantise(v byte) int {
	return (int(v)*sixelLevels + sixelRound) / sixelMax
}

func (s sixelImage) bandCount() int {
	return max((s.height+sixelBand-1)/sixelBand, 1)
}

func (s sixelImage) bandRows(band int) int {
	return min(sixelBand, s.height-band*sixelBand)
}

func (s sixelImage) appendBand(dst []byte, band int) []byte {
	written := false
	for register := range sixelRegisters {
		masks := s.columnMasks(band, register)
		if allZero(masks) {
			continue
		}
		if written {
			dst = append(dst, '$')
		}
		dst = append(dst, '#')
		dst = strconv.AppendInt(dst, int64(register), 10)
		dst = appendColumns(dst, masks)
		written = true
	}
	return dst
}

func allZero(masks []byte) bool {
	for _, mask := range masks {
		if mask != 0 {
			return false
		}
	}
	return true
}

func (s sixelImage) columnMasks(band, register int) []byte {
	masks := make([]byte, s.width)
	first := band * sixelBand
	for row := range s.bandRows(band) {
		line := (first + row) * s.width
		for column := range s.width {
			if s.indices[line+column] == register {
				masks[column] |= 1 << row
			}
		}
	}
	return masks
}

func appendColumns(dst, masks []byte) []byte {
	for start := 0; start < len(masks); {
		length := runLength(masks[start:])
		dst = appendRun(dst, masks[start], length)
		start += length
	}
	return dst
}

func runLength(masks []byte) int {
	length := 1
	for length < len(masks) && masks[length] == masks[0] {
		length++
	}
	return length
}

func appendRun(dst []byte, mask byte, length int) []byte {
	glyph := sixelCharBase + mask
	if length >= sixelMinRun {
		dst = append(dst, '!')
		dst = strconv.AppendInt(dst, int64(length), 10)
		return append(dst, glyph)
	}
	for range length {
		dst = append(dst, glyph)
	}
	return dst
}
