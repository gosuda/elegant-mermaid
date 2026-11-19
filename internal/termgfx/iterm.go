package termgfx

import (
	"encoding/base64"
	"strconv"
)

const itermIntro = "\x1b]1337;File=inline=1;size="

func AppendITerm(dst, png []byte, width, height int) ([]byte, error) {
	if width < 0 || height < 0 {
		return dst, ErrSize
	}
	dst = append(dst, itermIntro...)
	dst = strconv.AppendInt(dst, int64(len(png)), 10)
	dst = append(dst, ";width="...)
	dst = strconv.AppendInt(dst, int64(width), 10)
	dst = append(dst, "px;height="...)
	dst = strconv.AppendInt(dst, int64(height), 10)
	dst = append(dst, "px;preserveAspectRatio=0:"...)
	dst = base64.StdEncoding.AppendEncode(dst, png)
	return append(dst, belByte), nil
}
