package svg

import (
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func TestMarkerOutlines(t *testing.T) {
	for _, c := range []struct {
		name string
		axis scene.Axis
		want string
	}{
		{"circle", scene.Axis(0), "<polygon class='emd-s-mark' points='10,10 9.97,10.55 9.89,11.08 9.77,11.59 9.58,12.11 9.34,12.59 9.08,13.06 8.75,13.48 8.39,13.89 7.98,14.25 7.56,14.58 7.09,14.84 6.61,15.08 6.09,15.27 5.58,15.39 5.05,15.47 4.5,15.5 3.95,15.47 3.42,15.39 2.91,15.27 2.39,15.08 1.91,14.84 1.44,14.58 1.02,14.25 0.61,13.89 0.25,13.48 -0.08,13.06 -0.34,12.59 -0.58,12.11 -0.77,11.59 -0.89,11.08 -0.97,10.55 -1,10 -0.97,9.45 -0.89,8.92 -0.77,8.41 -0.58,7.89 -0.34,7.41 -0.08,6.94 0.25,6.52 0.61,6.11 1.02,5.75 1.44,5.42 1.91,5.16 2.39,4.92 2.91,4.73 3.42,4.61 3.95,4.53 4.5,4.5 5.05,4.53 5.58,4.61 6.09,4.73 6.61,4.92 7.09,5.16 7.56,5.42 7.98,5.75 8.39,6.11 8.75,6.52 9.08,6.94 9.34,7.41 9.58,7.89 9.77,8.41 9.89,8.92 9.97,9.45 10,10' stroke-width='1'/>\n"},
		{"circle", scene.Axis(1), "<polygon class='emd-s-mark' points='10,10 10.03,9.45 10.11,8.92 10.23,8.41 10.42,7.89 10.66,7.41 10.92,6.94 11.25,6.52 11.61,6.11 12.02,5.75 12.44,5.42 12.91,5.16 13.39,4.92 13.91,4.73 14.42,4.61 14.95,4.53 15.5,4.5 16.05,4.53 16.58,4.61 17.09,4.73 17.61,4.92 18.09,5.16 18.56,5.42 18.98,5.75 19.39,6.11 19.75,6.52 20.08,6.94 20.34,7.41 20.58,7.89 20.77,8.41 20.89,8.92 20.97,9.45 21,10 20.97,10.55 20.89,11.08 20.77,11.59 20.58,12.11 20.34,12.59 20.08,13.06 19.75,13.48 19.39,13.89 18.98,14.25 18.56,14.58 18.09,14.84 17.61,15.08 17.09,15.27 16.58,15.39 16.05,15.47 15.5,15.5 14.95,15.47 14.42,15.39 13.91,15.27 13.39,15.08 12.91,14.84 12.44,14.58 12.02,14.25 11.61,13.89 11.25,13.48 10.92,13.06 10.66,12.59 10.42,12.11 10.23,11.59 10.11,11.08 10.03,10.55 10,10' stroke-width='1'/>\n"},
		{"circle", scene.Axis(2), "<polygon class='emd-s-mark' points='10,10 9.45,9.97 8.92,9.89 8.41,9.77 7.89,9.58 7.41,9.34 6.94,9.08 6.52,8.75 6.11,8.39 5.75,7.98 5.42,7.56 5.16,7.09 4.92,6.61 4.73,6.09 4.61,5.58 4.53,5.05 4.5,4.5 4.53,3.95 4.61,3.42 4.73,2.91 4.92,2.39 5.16,1.91 5.42,1.44 5.75,1.02 6.11,0.61 6.52,0.25 6.94,-0.08 7.41,-0.34 7.89,-0.58 8.41,-0.77 8.92,-0.89 9.45,-0.97 10,-1 10.55,-0.97 11.08,-0.89 11.59,-0.77 12.11,-0.58 12.59,-0.34 13.06,-0.08 13.48,0.25 13.89,0.61 14.25,1.02 14.58,1.44 14.84,1.91 15.08,2.39 15.27,2.91 15.39,3.42 15.47,3.95 15.5,4.5 15.47,5.05 15.39,5.58 15.27,6.09 15.08,6.61 14.84,7.09 14.58,7.56 14.25,7.98 13.89,8.39 13.48,8.75 13.06,9.08 12.59,9.34 12.11,9.58 11.59,9.77 11.08,9.89 10.55,9.97 10,10' stroke-width='1'/>\n"},
		{"circle", scene.Axis(3), "<polygon class='emd-s-mark' points='10,10 10.55,10.03 11.08,10.11 11.59,10.23 12.11,10.42 12.59,10.66 13.06,10.92 13.48,11.25 13.89,11.61 14.25,12.02 14.58,12.44 14.84,12.91 15.08,13.39 15.27,13.91 15.39,14.42 15.47,14.95 15.5,15.5 15.47,16.05 15.39,16.58 15.27,17.09 15.08,17.61 14.84,18.09 14.58,18.56 14.25,18.98 13.89,19.39 13.48,19.75 13.06,20.08 12.59,20.34 12.11,20.58 11.59,20.77 11.08,20.89 10.55,20.97 10,21 9.45,20.97 8.92,20.89 8.41,20.77 7.89,20.58 7.41,20.34 6.94,20.08 6.52,19.75 6.11,19.39 5.75,18.98 5.42,18.56 5.16,18.09 4.92,17.61 4.73,17.09 4.61,16.58 4.53,16.05 4.5,15.5 4.53,14.95 4.61,14.42 4.73,13.91 4.92,13.39 5.16,12.91 5.42,12.44 5.75,12.02 6.11,11.61 6.52,11.25 6.94,10.92 7.41,10.66 7.89,10.42 8.41,10.23 8.92,10.11 9.45,10.03 10,10' stroke-width='1'/>\n"},
		{"cross", scene.Axis(0), "<polyline class='emd-s-edge' points='2,6 10,14' stroke-width='1'/>\n<polyline class='emd-s-edge' points='10,6 2,14' stroke-width='1'/>\n"},
		{"cross", scene.Axis(1), "<polyline class='emd-s-edge' points='18,14 10,6' stroke-width='1'/>\n<polyline class='emd-s-edge' points='10,14 18,6' stroke-width='1'/>\n"},
		{"cross", scene.Axis(2), "<polyline class='emd-s-edge' points='14,2 6,10' stroke-width='1'/>\n<polyline class='emd-s-edge' points='14,10 6,2' stroke-width='1'/>\n"},
		{"cross", scene.Axis(3), "<polyline class='emd-s-edge' points='6,18 14,10' stroke-width='1'/>\n<polyline class='emd-s-edge' points='6,10 14,18' stroke-width='1'/>\n"},
		{"extension", scene.Axis(0), "<polygon class='emd-s-mark-hollow' points='10,10 2,12.83 2,7.17' stroke-width='1'/>\n"},
		{"extension", scene.Axis(1), "<polygon class='emd-s-mark-hollow' points='10,10 18,7.17 18,12.83' stroke-width='1'/>\n"},
		{"extension", scene.Axis(2), "<polygon class='emd-s-mark-hollow' points='10,10 7.17,2 12.83,2' stroke-width='1'/>\n"},
		{"extension", scene.Axis(3), "<polygon class='emd-s-mark-hollow' points='10,10 12.83,18 7.17,18' stroke-width='1'/>\n"},
		{"composition", scene.Axis(0), "<polygon class='emd-s-mark' points='10,10 5.77,12.83 2,10 5.77,7.17' stroke-width='1'/>\n"},
		{"composition", scene.Axis(1), "<polygon class='emd-s-mark' points='10,10 14.23,7.17 18,10 14.23,12.83' stroke-width='1'/>\n"},
		{"composition", scene.Axis(2), "<polygon class='emd-s-mark' points='10,10 7.17,5.77 10,2 12.83,5.77' stroke-width='1'/>\n"},
		{"composition", scene.Axis(3), "<polygon class='emd-s-mark' points='10,10 12.83,14.23 10,18 7.17,14.23' stroke-width='1'/>\n"},
		{"openArrow", scene.Axis(0), "<polyline class='emd-s-edge' points='2,6 10,10 2,14' stroke-width='1'/>\n"},
		{"openArrow", scene.Axis(1), "<polyline class='emd-s-edge' points='18,14 10,10 18,6' stroke-width='1'/>\n"},
		{"openArrow", scene.Axis(2), "<polyline class='emd-s-edge' points='14,2 10,10 6,2' stroke-width='1'/>\n"},
		{"openArrow", scene.Axis(3), "<polyline class='emd-s-edge' points='6,18 10,10 14,18' stroke-width='1'/>\n"},
	} {
		r := renderer{used: make(map[string]bool)}
		got, err := r.marker(&scene.MarkerRef{Marker: c.name, At: geom.Point{X: 640, Y: 640}, Axis: c.axis}, 0)
		if err != nil || got != c.want {
			t.Errorf("%s/%d: got %q, want %q (%v)", c.name, c.axis, got, c.want, err)
		}
	}
}
