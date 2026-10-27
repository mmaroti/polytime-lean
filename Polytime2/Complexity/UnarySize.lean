import Polytime2.Complexity.UnaryHeader
import Polytime2.Computation.ComputedSizes
import Polytime2.Arrays.FixedArrayCall
import Polytime2.Computation.RetainUnary

/-! # Unary size preparation from word headers

The actual leading count-symbol prefix supplies a bounded unary runtime size.
Separator validation remains separate: malformed words still have a defined
prefix length, so preparation is total and never invents an accepted header.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity

open EncodedDomain Polytime2.Computation

/-- Prepare the actual prefix length in the unary codec used by computed calls. -/
noncomputable def unaryHeaderSize : Computation Unit Unit :=
  unaryCountFlags.followedBy (leadingUnarySize (MvPolynomial.X ())) rfl (by intros; trivial)

theorem unaryHeaderSize_realizable : unaryHeaderSize.Realizable :=
  unaryCountFlags_realizable.followedBy (leadingUnarySize_realizable (MvPolynomial.X ()))
    rfl (by intros; trivial)

/-- Unary size preparation counts precisely the initial count symbols. -/
theorem unaryHeaderSize_correct (sizes : Unit → ℕ)
    (letters : Fin (MvPolynomial.eval sizes (MvPolynomial.X ())) → Letter) :
    (unaryHeaderSize.compute sizes ⟨(fun _ => letters), trivial⟩).val =
      (List.ofFn letters).findIdx (fun letter : Letter => decide (letter ≠ .inr 1)) := by
  let predicate : Letter → Bool := fun letter => decide (letter = .inr 1)
  have mapped : List.ofFn (fun index => predicate (letters index)) =
      (List.ofFn letters).map predicate := by rw [List.map_ofFn]; rfl
  change (List.ofFn (fun index => predicate (letters index))).findIdx (! ·) = _
  rw [mapped, List.findIdx_map]
  congr 1

private noncomputable def namedUnaryHeaderSize : Computation Unit Unit :=
  unaryHeaderSize.reinterpretInputs (fun _ : Unit => letterDomain.array ())
    (fun _ sizes => arrayParameterEquiv letterDomain () sizes) (fun _ _ => True) (by intros; trivial)

private theorem namedUnaryHeaderSize_realizable : namedUnaryHeaderSize.Realizable :=
  unaryHeaderSize_realizable.reinterpretInputs (fun _ : Unit => letterDomain.array ())
    (fun _ sizes => arrayParameterEquiv letterDomain () sizes) (by intros; rfl)
    (fun _ sizes value => array_X_encode_bits letterDomain () sizes value)
    (fun _ _ => True) (by intros; trivial)

/-- Prepare a header's unary count at a stored field's actual length. The result
retains that length, and capacity padding never contributes count symbols. -/
noncomputable def fieldUnaryHeaderSize : Computation Unit Unit :=
  callFixedArray (fixed (Fintype.equivFin Letter)) (MvPolynomial.X ()) namedUnaryHeaderSize
    rfl (by intros; trivial)

theorem fieldUnaryHeaderSize_realizable : fieldUnaryHeaderSize.Realizable :=
  namedUnaryHeaderSize_realizable.callFixedArray (fixed (Fintype.equivFin Letter)) (MvPolynomial.X ())
    rfl (by intros; trivial)

/-- The prepared unary value counts the exact stored field contents. -/
theorem fieldUnaryHeaderSize_correct (sizes : Unit → ℕ)
    (field : (boundedArray letterDomain (MvPolynomial.X ())).Carrier sizes) :
    (fieldUnaryHeaderSize.compute sizes ⟨(fun _ => field), trivial⟩).2.val =
      (List.ofFn field.2).findIdx (fun letter : Letter => decide (letter ≠ .inr 1)) := by
  let actual : Unit → ℕ := fun _ => field.1.val
  let letters := arrayParameterEquiv letterDomain () actual field.2
  have counted := unaryHeaderSize_correct actual letters
  have sameLetters : List.ofFn letters = List.ofFn field.2 :=
    (List.ofFn_congr (MvPolynomial.eval_X (f := actual) ()).symm field.2).symm
  exact counted.trans (congrArg (List.findIdx (fun letter : Letter => decide (letter ≠ .inr 1))) sameLetters)

/-- On a successfully parsed header, size preparation returns its actual
variable count. This does not assert validity of any unparsed header. -/
theorem fieldUnaryHeaderSize_parsed (sizes : Unit → ℕ)
    (field : (boundedArray letterDomain (MvPolynomial.X ())).Carrier sizes)
    (count : ℕ) (payload : Word)
    (parsed : readPairHeader (List.ofFn field.2) = some (count, payload)) :
    (fieldUnaryHeaderSize.compute sizes ⟨(fun _ => field), trivial⟩).2.val = count :=
  (fieldUnaryHeaderSize_correct sizes field).trans (readPairHeader_count parsed)

/-- Prepare the stored field's prefix count in the host's unary size domain.
The actual field length is internal to this computed-size call. -/
noncomputable def fieldVariableCount : Computation Unit Unit :=
  fieldUnaryHeaderSize.followedBy (retainComputedUnarySize (MvPolynomial.X ()))
    rfl (by intros; trivial)

theorem fieldVariableCount_realizable : fieldVariableCount.Realizable :=
  fieldUnaryHeaderSize_realizable.followedBy (retainComputedUnarySize_realizable (MvPolynomial.X ()))
    rfl (by intros; trivial)

/-- Host-capacity preparation preserves the actual count on all field contents. -/
theorem fieldVariableCount_correct (sizes : Unit → ℕ)
    (field : (boundedArray letterDomain (MvPolynomial.X ())).Carrier sizes) :
    (fieldVariableCount.compute sizes ⟨(fun _ => field), trivial⟩).val =
      (List.ofFn field.2).findIdx (fun letter : Letter => decide (letter ≠ .inr 1)) :=
  fieldUnaryHeaderSize_correct sizes field

/-- A valid instance header supplies precisely its parsed variable count. -/
theorem fieldVariableCount_parsed (sizes : Unit → ℕ)
    (field : (boundedArray letterDomain (MvPolynomial.X ())).Carrier sizes)
    (count : ℕ) (payload : Word)
    (parsed : readPairHeader (List.ofFn field.2) = some (count, payload)) :
    (fieldVariableCount.compute sizes ⟨(fun _ => field), trivial⟩).val = count :=
  fieldUnaryHeaderSize_parsed sizes field count payload parsed

end Polytime2.Complexity
