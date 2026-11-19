package layered

type AttachmentSide uint8

const (
	AttachLeft AttachmentSide = iota
	AttachRight
)

type Attachment struct {
	Target, Note int
	Side         AttachmentSide
}

type RegionSet struct {
	Parent  int
	Regions []int
}
