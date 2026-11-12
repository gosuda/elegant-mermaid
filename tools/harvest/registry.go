package main

import (
	"encoding/json"
	"errors"
	"fmt"
	"os"
	"slices"
)

type keyword struct {
	Text string `json:"text"`
	Case string `json:"case"`
}

type kindEntry struct {
	ID       string    `json:"id"`
	Keywords []keyword `json:"keywords"`
	Aliases  []string  `json:"aliases"`
}

type registry struct {
	exact  map[string]string
	folded map[string]string
	byName map[string]string
}

func loadRegistry(name string) (*registry, error) {
	data, err := os.ReadFile(name)
	if err != nil {
		return nil, fmt.Errorf("read kind registry %s: %w", name, err)
	}
	var kinds []kindEntry
	if err := json.Unmarshal(data, &kinds); err != nil {
		return nil, fmt.Errorf("parse kind registry %s: %w", name, err)
	}
	if len(kinds) == 0 {
		return nil, fmt.Errorf("kind registry %s declares no kind", name)
	}
	r := &registry{
		exact:  make(map[string]string, len(kinds)),
		folded: make(map[string]string, len(kinds)),
		byName: make(map[string]string, 2*len(kinds)),
	}
	for _, k := range kinds {
		if err := r.addKind(k); err != nil {
			return nil, err
		}
	}
	for _, k := range kinds {
		for _, name := range kindNames(k) {
			if err := bindName(r.byName, name, k.ID); err != nil {
				return nil, err
			}
		}
	}
	return r, nil
}

func kindNames(k kindEntry) []string {
	names := slices.Clone(k.Aliases)
	for _, kw := range k.Keywords {
		names = append(names, kw.Text)
	}
	return names
}

func (r *registry) addKind(k kindEntry) error {
	if k.ID == "" {
		return errors.New("kind registry declares a kind with no id")
	}
	if err := bindName(r.byName, k.ID, k.ID); err != nil {
		return err
	}
	for _, kw := range k.Keywords {
		table, key := r.exact, kw.Text
		switch kw.Case {
		case "sensitive":
		case "insensitive":
			table, key = r.folded, asciiLower(kw.Text)
		default:
			return fmt.Errorf("kind %q keyword %q carries case rule %q", k.ID, kw.Text, kw.Case)
		}
		if prev, ok := table[key]; ok && prev != k.ID {
			return fmt.Errorf("keyword %q belongs to both %q and %q", kw.Text, prev, k.ID)
		}
		table[key] = k.ID
	}
	return nil
}

func bindName(table map[string]string, name, id string) error {
	key := normalizeName(name)
	if key == "" {
		return fmt.Errorf("kind %q carries a name with no letter or digit: %q", id, name)
	}
	if prev, ok := table[key]; ok && prev != id {
		return fmt.Errorf("name %q resolves to both %q and %q", name, prev, id)
	}
	table[key] = id
	return nil
}

func normalizeName(s string) string {
	out := make([]byte, 0, len(s))
	for i := 0; i < len(s); i++ {
		c := s[i]
		switch {
		case c >= 'A' && c <= 'Z':
			out = append(out, c+('a'-'A'))
		case c >= 'a' && c <= 'z', c >= '0' && c <= '9':
			out = append(out, c)
		}
	}
	return string(out)
}

func (r *registry) kindOfToken(token string) (string, bool) {
	if id, ok := r.exact[token]; ok {
		return id, true
	}
	id, ok := r.folded[asciiLower(token)]
	return id, ok
}

func (r *registry) kindOfDirectory(name string) (string, bool) {
	for _, candidate := range directoryCandidates(name) {
		if id, ok := r.byName[normalizeName(candidate)]; ok {
			return id, true
		}
	}
	return r.kindOfUniquePrefix(name)
}

func directoryCandidates(name string) []string {
	candidates := []string{name}
	if len(name) > 1 {
		candidates = append(candidates, name[:len(name)-1])
	}
	return candidates
}

func (r *registry) kindOfUniquePrefix(name string) (string, bool) {
	key := normalizeName(name)
	if len(key) < 3 {
		return "", false
	}
	found, distinct := "", 0
	for candidate, id := range r.byName {
		if len(candidate) < len(key) || candidate[:len(key)] != key || id == found {
			continue
		}
		found = id
		distinct++
	}
	return found, distinct == 1
}

func (r *registry) classify(src []byte) string {
	token := headerToken(src)
	if asciiLower(token) == zenumlHeader {
		return outOfScopeKind
	}
	if id, ok := r.kindOfToken(token); ok {
		return id
	}
	return unknownKind
}
