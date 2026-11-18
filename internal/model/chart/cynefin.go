package chart

type CynefinDomain struct {
	Name  string
	Items []string
}

type CynefinTransition struct {
	From  string
	To    string
	Label string
}

type Cynefin struct {
	Title       string
	Config      []ConfigEntry
	Domains     []CynefinDomain
	Transitions []CynefinTransition
}

func (c *Cynefin) Integer(key string) (int64, bool) {
	return (&Chart{Config: c.Config}).Integer(key)
}

type Info struct {
	Text string
}
