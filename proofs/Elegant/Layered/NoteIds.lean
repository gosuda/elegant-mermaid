import Elegant.Model

set_option autoImplicit false

/-! Note-attachment identity parsing shared by the family guards. `attachedNotes` mirrors
`PipelineImpl.attachmentsOf` in `AttachPipeline.lean`; the two copies must stay in step because
the family entry cannot import the attach pipeline (it would be a cycle). -/

namespace Elegant
namespace Layered

/-- `(target index, note index, right)` for every note box that `attachmentsOf` would pair. -/
def attachedNotes (boxes : List ModelBox) : List (Nat × Nat × Bool) :=
  let dropSuffix (cs suffix : List Char) : Option (List Char) :=
    if suffix.isSuffixOf cs then some (cs.take (cs.length - suffix.length)) else none
  let noteTargetId (id : String) : Option String :=
    let cs := id.toList
    let note := ".note".toList
    let found :=
      match dropSuffix cs note with
      | some target => some target
      | none =>
        let reversed := cs.reverse
        if (reversed.takeWhile Char.isDigit).isEmpty then none
        else (dropSuffix (reversed.dropWhile Char.isDigit).reverse ['.']).bind (dropSuffix · note)
    found.map String.ofList
  boxes.zipIdx.filterMap fun q =>
    if q.1.shape == "note" && (q.1.direction == "left" || q.1.direction == "right") then
      (noteTargetId q.1.id).bind fun target =>
        (boxes.findIdx? (·.id == target)).map fun t => (t, q.2, q.1.direction == "right")
    else none

end Layered
end Elegant
