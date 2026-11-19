import Elegant.Model

set_option autoImplicit false

namespace Elegant.Grid.Architecture

private def hex (v : UInt8) : Option Nat :=
  let n := v.toNat
  if 48 ≤ n ∧ n ≤ 57 then some (n-48)
  else if 65 ≤ n ∧ n ≤ 70 then some (n-55)
  else if 97 ≤ n ∧ n ≤ 102 then some (n-87) else none

private def unescapeBytes : List UInt8 → List UInt8
  | a :: b :: c :: rest =>
    if a.toNat = 37 then
      match hex b,hex c with
      | some x,some y => UInt8.ofNat (16*x+y) :: unescapeBytes rest
      | _,_ => a :: unescapeBytes (b :: c :: rest)
    else a :: unescapeBytes (b :: c :: rest)
  | bytes => bytes

private def decodeBytes (bytes : ByteArray) : Nat → Nat → List Char
  | 0,_ => []
  | fuel+1,index =>
    if index ≥ bytes.size then [] else
    match bytes.utf8DecodeChar? index with
    | some c => c :: decodeBytes bytes fuel (index+c.utf8Size)
    | none => '�' :: decodeBytes bytes fuel (index+1)

/-- Decode the percent-escaped bytes of architecture icon text. Invalid UTF-8
bytes follow Go's scalar iteration rule: one replacement scalar per bad byte. -/
def unescapeShape (text : String) : String :=
  let bytes := (unescapeBytes text.toByteArray.data.toList).foldl ByteArray.push ByteArray.empty
  String.ofList (decodeBytes bytes bytes.size 0)

end Elegant.Grid.Architecture
