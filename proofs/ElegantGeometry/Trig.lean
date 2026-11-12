import Elegant.Gen.Sine

/-!
Fixed-point sine and cosine over the generated table. The angle unit is 1/65536 turn and
the result is in `[-32768, 32768]`. The steps follow `spec/geometry-kernel.md`,
requirements geometry-kernel-50 and geometry-kernel-51.
-/

def sineEntry (i : Int) : Int := sineTable.getD i.toNat 0

def sineLookup (k : Int) : Int :=
  let i := Int.fdiv k 16
  let f := k - 16 * i
  if f = 0 then sineEntry i
  else sineEntry i + Int.fdiv ((sineEntry (i + 1) - sineEntry i) * f + 8) 16

def sinAt (r : Int) : Int :=
  let q := Int.fdiv r 16384
  let u := r - 16384 * q
  if q = 1 then sineLookup (16384 - u)
  else if q = 2 then -sineLookup u
  else if q = 3 then -sineLookup (16384 - u)
  else sineLookup u

def sinQ15 (a : Int) : Int := sinAt (Int.fmod a 65536)

def cosQ15 (a : Int) : Int := sinAt (Int.fmod (a + 16384) 65536)

