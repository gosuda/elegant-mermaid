package layout

import (
	"bytes"
	"errors"
	"fmt"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
)

var ErrSiteConfig = errors.New("invalid config")

func ParseSiteConfig(text []byte) (syntax.ConfigValue, error) {
	if len(bytes.TrimSpace(text)) == 0 {
		return syntax.ConfigValue{}, nil
	}
	value, ds := syntax.ParseConfigYAML(text, 0, len(text))
	if len(ds) != 0 {
		return syntax.ConfigValue{}, fmt.Errorf("%w: %s", ErrSiteConfig, ds[0].Message)
	}
	if value.Kind != syntax.ValueMapping {
		return syntax.ConfigValue{}, fmt.Errorf("%w: config must be a mapping", ErrSiteConfig)
	}
	_, ds = syntax.ReadEffectiveConfig(value)
	for _, diagnostic := range ds {
		if diagnostic.Severity == diag.SeverityError {
			return syntax.ConfigValue{}, fmt.Errorf("%w: %s", ErrSiteConfig, diagnostic.Message)
		}
	}
	return value, nil
}

func (d *Diagram) configMappings() []syntax.ConfigValue {
	var out []syntax.ConfigValue
	if d.Preprocessing.HasConfig {
		out = append(out, d.Preprocessing.Config)
	}
	if d.Preprocessing.HasInit {
		out = append(out, d.Preprocessing.Init)
	}
	return out
}

func (d *Diagram) Look(site syntax.ConfigValue) (scene.Look, error) {
	config, err := d.EffectiveConfig(site)
	if err != nil {
		return scene.Look{}, err
	}
	return SceneLook(config.Look), nil
}

func SceneLook(parsed syntax.Look) scene.Look {
	look := scene.Look{Seed: parsed.Seed}
	switch parsed.Value {
	case "neo":
		look.Kind = scene.LookNeo
	case "handDrawn":
		look.Kind = scene.LookHandDrawn
	}
	return look
}
