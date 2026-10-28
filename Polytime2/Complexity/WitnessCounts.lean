import Polytime2.Complexity.ParsedPair
import Polytime2.Complexity.UnarySize
import Polytime2.Arithmetic.UnaryToIndex

/-! # The two field lengths used by nested-witness normalization

The outer input length is the first field's exact stored length. The inner
witness length is its padded field's parsed prefix count. Both remain ordinary
bounded natural data; no application size parameter is introduced.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity

open EncodedDomain Polytime2.Computation

/-- Read outer-input and inner-witness lengths from the parsed outer fields. -/
noncomputable def witnessCounts : Computation Unit Unit where
  inputDomains _ := pairFields.outputDomain
  outputDomain := (boundedIndex (MvPolynomial.X () + 1)).prod (boundedIndex (MvPolynomial.X () + 1))
  precondition _ _ := True
  compute sizes arguments :=
    ((boundedUnaryToIndex (MvPolynomial.X ())).compute sizes
      ⟨(fun _ => (arguments.val ()).1.1), trivial⟩,
     (boundedUnaryToIndex (MvPolynomial.X ())).compute sizes
      ⟨(fun _ => fieldVariableCount.compute sizes ⟨(fun _ => (arguments.val ()).2), trivial⟩), trivial⟩)

theorem witnessCounts_realizable : witnessCounts.Realizable := by
  let context := witnessCounts.inputDomains
  have fields := Realizable.argument context () (fun _ _ => True)
  have first := (fields.fst.followedBy (boundedArrayCount_realizable letterDomain (MvPolynomial.X ()))
    rfl (by intros; trivial)).followedBy (boundedUnaryToIndex_realizable (MvPolynomial.X ())) rfl (by intros; trivial)
  have second := (fields.snd.followedBy fieldVariableCount_realizable rfl (by intros; trivial)).followedBy
    (boundedUnaryToIndex_realizable (MvPolynomial.X ())) rfl (by intros; trivial)
  exact first.prodMk second

/-- The first count is exactly the actual outer input length. -/
theorem witnessCounts_input (sizes : Unit → ℕ) (fields : pairFields.outputDomain.Carrier sizes) :
    (witnessCounts.compute sizes ⟨(fun _ => fields), trivial⟩).1.val = (List.ofFn fields.1.2).length := by
  simp [witnessCounts, boundedUnaryToIndex, unaryMap]

/-- Successful inner pair decoding fixes the second count to the witness length. -/
theorem witnessCounts_witness (sizes : Unit → ℕ) (fields : pairFields.outputDomain.Carrier sizes)
    (witness padding : Word) (decoded : decodePair (List.ofFn fields.2.2) = some (witness, padding)) :
    (witnessCounts.compute sizes ⟨(fun _ => fields), trivial⟩).2.val = witness.length := by
  have header : readPairHeader (List.ofFn fields.2.2) = some (witness.length, witness ++ padding) := by
    rw [decodePair_canonical decoded]
    simp [encodePair, List.append_assoc, readPairHeader_prefix]
  exact fieldVariableCount_parsed sizes fields.2 witness.length (witness ++ padding) header

end Polytime2.Complexity
