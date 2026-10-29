import Polytime2.Arrays.Queue
import Polytime2.Arrays.Snoc
import Mathlib.Computability.TuringMachine.Tape

/-! # Array shifts with a supplied boundary value

Both directions preserve the array length and canonical element codec. The
finite TM0 interpreter uses blank boundary values for its local tape window.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def arrayCons (element : EncodedDomain.{0, 0} Parameter)
    (length : MvPolynomial Parameter ℕ) : Computation Parameter Bool where
  inputDomains | false => element.arrayOfLength length | true => element
  outputDomain := element.arrayOfLength (length + 1)
  precondition _ _ := True
  compute sizes arguments index := Fin.cons
    (α := fun _ : Fin (MvPolynomial.eval sizes length + 1) => element.Carrier sizes)
    (arguments.val true) (arguments.val false)
    (index.cast (show MvPolynomial.eval sizes (length + 1) = MvPolynomial.eval sizes length + 1 by simp))

private theorem arrayCons_realizable (element : EncodedDomain.{0, 0} Parameter)
    (length : MvPolynomial Parameter ℕ) : (arrayCons element length).Realizable := by
  have pair := (Realizable.argument (arrayCons element length).inputDomains true (fun _ _ => True)).prodMk
    (Realizable.argument (arrayCons element length).inputDomains false (fun _ _ => True))
  apply pair.withEncodedOutput (arrayCons element length).outputDomain (arrayCons element length).compute
  · intro sizes; simp [arrayCons, width]; ring
  · intro sizes arguments
    apply congrArg CallingConvention.tape
    change ArrayEncoding.bits (((element.arrayOfLength (length + 1))).encode sizes _) = _
    rw [arrayOfLength_encode_bits, ArrayEncoding.bits_encode]
    rw [List.ofFn_congr (show MvPolynomial.eval sizes (length + 1) = MvPolynomial.eval sizes length + 1 by simp)]
    simp [arrayCons, ArrayEncoding.bits_append, arrayOfLength_encode_bits, ArrayEncoding.bits_encode, List.ofFn_succ]

/-- Read the neighbor in the fixed direction, using the true input beyond the
boundary. False names the original array; the length is preserved. -/
noncomputable def arrayShift (element : EncodedDomain.{0, 0} Parameter) (length : MvPolynomial Parameter ℕ)
    (direction : Turing.Dir) : Computation Parameter Bool where
  inputDomains | false => element.arrayOfLength length | true => element
  outputDomain := element.arrayOfLength length
  precondition _ _ := True
  compute sizes arguments index := match direction with
    | .left => if first : index.val = 0 then arguments.val true
      else arguments.val false ⟨index.val - 1, by omega⟩
    | .right => if last : index.val + 1 < MvPolynomial.eval sizes length then
        arguments.val false ⟨index.val + 1, last⟩ else arguments.val true

theorem arrayShift_realizable (element : EncodedDomain.{0, 0} Parameter) (length : MvPolynomial Parameter ℕ)
    (direction : Turing.Dir) : (arrayShift element length direction).Realizable := by
  cases direction with
  | left =>
    have complete := (arrayCons_realizable element length).followedBy (arrayInit_realizable element length)
      (show (arrayInit element length).inputDomains () = (arrayCons element length).outputDomain from rfl)
      (by intros; trivial)
    apply complete.withSpecification (fun _ _ => True) (arrayShift element length .left).compute (by intros; trivial)
    intro sizes arguments valid
    funext index
    rcases index with ⟨index, bounded⟩
    cases index with
    | zero => simp [followedBy, arrayCons, arrayInit, arrayUnsnoc, pairProjection,
        unaryMap, encodingMap, successorValues, arrayShift, Fin.cons, Fin.cases]
    | succ index =>
      simp only [followedBy, arrayCons, arrayInit, arrayUnsnoc, pairProjection,
      unaryMap, encodingMap, successorValues, arrayShift, Fin.cons, Fin.cases]
      change Fin.cons (α := fun _ : Fin (MvPolynomial.eval sizes length + 1) => element.Carrier sizes)
        (arguments true) (arguments false) (Fin.succ ⟨index, by omega⟩) = _
      rw [Fin.cons_succ]
      simp
  | right =>
    have complete := (arraySnoc_realizable element length).followedBy (arrayTail_realizable element length)
      (show (arrayTail element length).inputDomains () = (arraySnoc element length).outputDomain from rfl)
      (by intros; trivial)
    apply complete.withSpecification (fun _ _ => True) (arrayShift element length .right).compute (by intros; trivial)
    intro sizes arguments valid
    funext index
    change Fin.snoc (α := fun _ : Fin (MvPolynomial.eval sizes length + 1) => element.Carrier sizes)
      (arguments false) (arguments true) index.succ = _
    simp only [Fin.snoc, arrayShift, Fin.val_succ]
    split_ifs <;> rfl

end Polytime2.Computation
