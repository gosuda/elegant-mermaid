package termgfx

import "encoding/base64"

const kittyChunkSize = 4096

const (
	apcIntro    = "\x1b_G"
	kittyDelete = "\x1b_Ga=d,d=A,q=2\x1b\\"
)

type kittyChunk struct {
	text string
	more byte
}

func AppendKitty(dst, png []byte) []byte {
	dst = append(dst, kittyDelete...)
	return appendKittyChunks(dst, base64.StdEncoding.EncodeToString(png))
}

func appendKittyChunks(dst []byte, text string) []byte {
	chunks := kittyChunks(text)
	dst = appendKittyImage(dst, chunks[0])
	for _, chunk := range chunks[1:] {
		dst = appendKittyMore(dst, chunk)
	}
	return dst
}

func kittyChunks(text string) []kittyChunk {
	size := max((len(text)+kittyChunkSize-1)/kittyChunkSize, 1)
	chunks := make([]kittyChunk, size)
	for index := range size {
		start := index * kittyChunkSize
		end := min(start+kittyChunkSize, len(text))
		chunks[index] = kittyChunk{text: text[start:end], more: kittyMore(end, len(text))}
	}
	return chunks
}

func kittyMore(end, total int) byte {
	if end < total {
		return '1'
	}
	return '0'
}

func appendKittyImage(dst []byte, chunk kittyChunk) []byte {
	dst = append(dst, apcIntro...)
	dst = append(dst, "a=T,f=100,i=1,q=2,m="...)
	dst = append(dst, chunk.more, ';')
	dst = append(dst, chunk.text...)
	return append(dst, stSeq...)
}

func appendKittyMore(dst []byte, chunk kittyChunk) []byte {
	dst = append(dst, apcIntro...)
	dst = append(dst, "m="...)
	dst = append(dst, chunk.more, ';')
	dst = append(dst, chunk.text...)
	return append(dst, stSeq...)
}
