import Elegant.Gen.Alphanumeric

set_option autoImplicit false

namespace Elegant.Label

/-! # Styled label tokenizer (spec/math.md math-01 through math-08)

Pure, total Lean 4 reference implementation of the Mermaid styled-label scanner,
mirroring the Go scanner in `internal/measure/styled.go` with exact parity:
- Escapes (`\*`, `\_`, `\\`, `\$`, etc.) drop the backslash and inherit active style
- `<br>`, `<br/>`, `<br />` (case-insensitive) end regions and store the exact separator
- Intraword underscore detection uses the pinned Unicode Alphanumeric table
- Emphasis (`**` bold, `*` and `_` italic) does not nest and closes on the same line
- CR/LF are emphasis boundaries but not forced line breaks
- Matched `$$...$$` math is opaque and regular (cleared style)
- Unmatched `$$` and other unsupported markup remain literal text
-/

structure Run where
  text : List Char
  bold : Bool := false
  italic : Bool := false
  math : Bool := false
deriving Repr, BEq, Inhabited

structure Region where
  runs : List Run
  separator : List Char := []
deriving Repr, BEq, Inhabited

/-! ### Alphanumeric classification -/

def isASCIIAlnum (c : Char) : Bool :=
  (c >= '0' && c <= '9') || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')

/-- Binary search for the least index below `n` where `p` holds, or `n`. -/
def partitionPoint (n : Nat) (p : Nat → Bool) : Nat :=
  go 64 0 n
where
  go : Nat → Nat → Nat → Nat
    | 0, lo, _ => lo
    | fuel + 1, lo, hi =>
      if lo < hi then
        let mid := (lo + hi) / 2
        if p mid then go fuel lo mid else go fuel (mid + 1) hi
      else lo

def isAlphanumeric (c : Char) : Bool :=
  let cp := c.toNat
  if cp < 128 then
    isASCIIAlnum c
  else
    let idx := partitionPoint _root_.alphanumeric.size fun i =>
      match _root_.alphanumeric[i]? with
      | some r => decide (cp ≤ r.hi)
      | none => true
    match _root_.alphanumeric[idx]? with
    | some r => decide (r.lo ≤ cp)
    | none => false

/-! ### Helpers on Char arrays -/

def getChar (s : Array Char) (cursor : Nat) : Char :=
  match s[cursor]? with
  | some c => c
  | none => '\x00'

def slice (s : Array Char) (start stop : Nat) : List Char :=
  if start ≥ stop then []
  else (s.extract start stop).toList

/-! ### Constructs and delimiters -/

/-- Backslash before ASCII punctuation (ASCII 33..126 except alphanumeric). -/
def styledEscape (s : Array Char) (cursor : Nat) : Bool :=
  if cursor + 1 ≥ s.size then
    false
  else if getChar s cursor ≠ '\\' then
    false
  else
    let c := getChar s (cursor + 1)
    let n := c.toNat
    n ≥ 33 && n ≤ 126 && !isASCIIAlnum c

/-- Recognized case-insensitive line break tags: `<br>`, `<br/>`, `<br />`. -/
def styledBreakLen (s : Array Char) (cursor : Nat) : Nat :=
  if cursor + 4 > s.size then 0
  else
    let c0 := getChar s cursor
    let c1 := getChar s (cursor + 1)
    let c2 := getChar s (cursor + 2)
    if c0 == '<' && (c1 == 'b' || c1 == 'B') && (c2 == 'r' || c2 == 'R') then
      let c3 := getChar s (cursor + 3)
      if c3 == '>' then 4
      else if c3 == '/' then
        if cursor + 5 ≤ s.size && getChar s (cursor + 4) == '>' then 5 else 0
      else if c3 == ' ' then
        if cursor + 6 ≤ s.size && getChar s (cursor + 4) == '/' && getChar s (cursor + 5) == '>' then 6 else 0
      else 0
    else 0

/-- Underscore between two alphanumeric characters is intraword and literal. -/
def styledIntraword (s : Array Char) (cursor : Nat) : Bool :=
  if cursor == 0 || cursor + 1 ≥ s.size then
    false
  else
    let before := getChar s (cursor - 1)
    let after := getChar s (cursor + 1)
    isAlphanumeric before && isAlphanumeric after

inductive Delim where
  | none
  | starStar
  | star
  | underscore
deriving BEq, DecidableEq, Inhabited

def Delim.len : Delim → Nat
  | .none => 0
  | .starStar => 2
  | .star => 1
  | .underscore => 1

def Delim.isBold : Delim → Bool
  | .starStar => true
  | _ => false

def Delim.isItalic : Delim → Bool
  | .star => true
  | .underscore => true
  | _ => false

def styledDelimiter (s : Array Char) (cursor : Nat) : Delim :=
  if cursor ≥ s.size then .none
  else
    let c := getChar s cursor
    if c == '*' then
      if cursor + 1 < s.size && getChar s (cursor + 1) == '*' then
        .starStar
      else
        .star
    else if c == '_' then
      if styledIntraword s cursor then
        .none
      else
        .underscore
    else
      .none

def styledMathEnd (s : Array Char) (cursor : Nat) : Option Nat :=
  go (s.size - cursor + 1) cursor
where
  go : Nat → Nat → Option Nat
    | 0, _ => none
    | fuel + 1, cursor =>
      if cursor ≥ s.size then none
      else if styledEscape s cursor then
        go fuel (cursor + 2)
      else if cursor + 1 < s.size && getChar s cursor == '$' && getChar s (cursor + 1) == '$' then
        some cursor
      else
        go fuel (cursor + 1)

def styledOpaqueEnd (s : Array Char) (cursor : Nat) : Nat :=
  if styledEscape s cursor then
    cursor + 2
  else if !(cursor + 1 < s.size && getChar s cursor == '$' && getChar s (cursor + 1) == '$') then
    cursor
  else
    match styledMathEnd s (cursor + 2) with
    | none => cursor + 2
    | some close => close + 2

def styledEmphasisBoundary (s : Array Char) (cursor : Nat) : Bool :=
  if cursor ≥ s.size then false
  else
    let c := getChar s cursor
    c == '\r' || c == '\n' || styledBreakLen s cursor ≠ 0

def styledEmphasisClose (s : Array Char) (cursor : Nat) (d : Delim) : Bool :=
  match d with
  | .none => false
  | .starStar =>
    cursor + 1 < s.size && getChar s cursor == '*' && getChar s (cursor + 1) == '*'
  | .star =>
    cursor < s.size && getChar s cursor == '*'
  | .underscore =>
    cursor < s.size && getChar s cursor == '_' && !styledIntraword s cursor

def styledEmphasisEnd (s : Array Char) (cursor : Nat) (d : Delim) : Option Nat :=
  go (s.size - cursor + 1) cursor
where
  go : Nat → Nat → Option Nat
    | 0, _ => none
    | fuel + 1, cursor =>
      if cursor ≥ s.size then none
      else if styledEmphasisBoundary s cursor then none
      else
        let next := styledOpaqueEnd s cursor
        if next ≠ cursor then
          go fuel next
        else if styledEmphasisClose s cursor d then
          some cursor
        else
          go fuel (cursor + 1)

/-! ### Scanning loops -/

/-- Scans emphasis content without nesting. Delimiters are not recognized. -/
def scanInner (s : Array Char) (lo hi : Nat) (bold italic : Bool) (initRuns : List Run) : List Run :=
  go (hi - lo + 1) lo lo initRuns
where
  go : Nat → Nat → Nat → List Run → List Run
    | 0, _, _, runs => runs
    | fuel + 1, cursor, plain, runs =>
      if cursor ≥ hi then
        if plain < hi then
          { text := slice s plain hi, bold := bold, italic := italic } :: runs
        else
          runs
      else if styledEscape s cursor && cursor + 2 ≤ hi then
        let runs1 :=
          if plain < cursor then
            { text := slice s plain cursor, bold := bold, italic := italic } :: runs
          else
            runs
        let escChar := getChar s (cursor + 1)
        let runs2 := { text := [escChar], bold := bold, italic := italic } :: runs1
        go fuel (cursor + 2) (cursor + 2) runs2
      else if cursor + 1 < hi && getChar s cursor == '$' && getChar s (cursor + 1) == '$' then
        match styledMathEnd s (cursor + 2) with
        | some close =>
          if close + 2 ≤ hi then
            let runs1 :=
              if plain < cursor then
                { text := slice s plain cursor, bold := bold, italic := italic } :: runs
              else
                runs
            let mathText := slice s cursor (close + 2)
            let runs2 := { text := mathText, bold := false, italic := false, math := true } :: runs1
            go fuel (close + 2) (close + 2) runs2
          else
            go fuel (cursor + 1) plain runs
        | none =>
          go fuel (cursor + 1) plain runs
      else
        go fuel (cursor + 1) plain runs

/-- Top-level scanner: parses breaks, escapes, math, and emphasis into regions. -/
def scanTop (s : Array Char) : List Region :=
  let (curRuns, finishedRegions) := go (s.size + 1) 0 0 [] []
  let finalRegion : Region := { runs := curRuns.reverse, separator := [] }
  (finalRegion :: finishedRegions).reverse
where
  go : Nat → Nat → Nat → List Run → List Region → (List Run × List Region)
    | 0, _, _, runs, regions => (runs, regions)
    | fuel + 1, cursor, plain, runs, regions =>
      if cursor ≥ s.size then
        let finalRuns :=
          if plain < s.size then
            { text := slice s plain s.size, bold := false, italic := false } :: runs
          else
            runs
        (finalRuns, regions)
      else if styledEscape s cursor && cursor + 2 ≤ s.size then
        let runs1 :=
          if plain < cursor then
            { text := slice s plain cursor, bold := false, italic := false } :: runs
          else
            runs
        let escChar := getChar s (cursor + 1)
        let runs2 := { text := [escChar], bold := false, italic := false } :: runs1
        go fuel (cursor + 2) (cursor + 2) runs2 regions
      else
        let brLen := styledBreakLen s cursor
        if brLen ≠ 0 && cursor + brLen ≤ s.size then
          let runs1 :=
            if plain < cursor then
              { text := slice s plain cursor, bold := false, italic := false } :: runs
            else
              runs
          let sep := slice s cursor (cursor + brLen)
          let reg : Region := { runs := runs1.reverse, separator := sep }
          go fuel (cursor + brLen) (cursor + brLen) [] (reg :: regions)
        else if cursor + 1 < s.size && getChar s cursor == '$' && getChar s (cursor + 1) == '$' then
          match styledMathEnd s (cursor + 2) with
          | some close =>
            if close + 2 ≤ s.size then
              let runs1 :=
                if plain < cursor then
                  { text := slice s plain cursor, bold := false, italic := false } :: runs
                else
                  runs
              let mathText := slice s cursor (close + 2)
              let runs2 := { text := mathText, bold := false, italic := false, math := true } :: runs1
              go fuel (close + 2) (close + 2) runs2 regions
            else
              go fuel (cursor + 1) plain runs regions
          | none =>
            go fuel (cursor + 1) plain runs regions
        else
          let d := styledDelimiter s cursor
          if d ≠ .none then
            match styledEmphasisEnd s (cursor + d.len) d with
            | some close =>
              if close + d.len ≤ s.size then
                let runs1 :=
                  if plain < cursor then
                    { text := slice s plain cursor, bold := false, italic := false } :: runs
                  else
                    runs
                let runs2 := scanInner s (cursor + d.len) close d.isBold d.isItalic runs1
                go fuel (close + d.len) (close + d.len) runs2 regions
              else
                go fuel (cursor + d.len) plain runs regions
            | none =>
              go fuel (cursor + d.len) plain runs regions
          else
            go fuel (cursor + 1) plain runs regions

/-- Partitions a source label into regions at `<br>`, `<br/>`, and `<br />` tags,
parsing Markdown emphasis and math runs within each region. -/
def regions (source : List Char) : List Region :=
  scanTop source.toArray

end Elegant.Label
