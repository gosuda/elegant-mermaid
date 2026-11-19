package scene

const radiusToken = 512
const neoRadius = 768

type LookKind uint8

const (
	LookClassic LookKind = iota

	LookNeo

	LookHandDrawn
)

type Look struct {
	Kind LookKind
	Seed uint32
}

func (l Look) Width(w Width) Width {
	if l.Kind == LookNeo && w.Kind == WidthNormal {
		w.Kind = WidthEmphasis
	}
	return w
}

func (l Look) Radius(r int32) int32 {
	if l.Kind == LookNeo && r == radiusToken {
		return neoRadius
	}
	return r
}
