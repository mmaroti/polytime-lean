import Polytime2.Circuit.GateSplice
import Polytime2.Arrays.Transform

/-! # Relocating a canonical gate array through shared input aliases -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Circuit

open EncodedDomain Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

/-- Relocate all gates of a source program using one immutable alias array.
The left input is the alias array; the right input is the source program. -/
noncomputable def spliceProgram (source target count : MvPolynomial Parameter ℕ) :
    Computation Parameter (Unit ⊕ Unit) :=
  arrayTransform (fun _ : Unit => (arrayPosition target).arrayOfLength source)
    (gateDomain (source + count)) (gateDomain (target + count)) count
    (fun sizes aliases gate => (gateSplice source target count).compute sizes
      ⟨(fun name => match name with | false => gate | true => aliases ()), trivial⟩)

theorem spliceProgram_realizable (source target count : MvPolynomial Parameter ℕ) :
    (spliceProgram source target count).Realizable := by
  apply arrayTransform_realizable
  let inputs : Unit ⊕ Unit → EncodedDomain Parameter :=
    Sum.elim (fun _ => (arrayPosition target).arrayOfLength source) (fun _ => gateDomain (source + count))
  have prepared := (gateSplice_realizable source target count).onArguments inputs (fun _ _ => True)
    (fun name => if name then .inl () else .inr ()) (by intro name; cases name <;> rfl) (by intros; trivial)
  apply prepared.withSpecification (fun _ _ => True) _ (by intros; trivial)
  intro sizes arguments valid
  apply congrArg ((gateSplice source target count).compute sizes)
  apply Subtype.ext
  funext name
  cases name <;> rfl

/-- Relocation preserves the program order and agrees with mathematical
composition on the complete gate list. -/
theorem spliceProgram_value (source target count : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (spliceProgram source target count).Arguments sizes // True}) :
    List.ofFn (fun index => gateValue ((spliceProgram source target count).compute sizes arguments index)) =
      (List.ofFn (fun index => gateValue (arguments.val (.inr ()) index))).map
        (Gate.rename (spliceNames (MvPolynomial.eval sizes source) (MvPolynomial.eval sizes target)
          (fun index => (arguments.val (.inl ()) index).val))) := by
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext index
  exact gateSplice_value source target count sizes
    ⟨(fun name => match name with
      | false => arguments.val (.inr ()) index
      | true => arguments.val (.inl ())), trivial⟩

end Polytime2.Circuit
