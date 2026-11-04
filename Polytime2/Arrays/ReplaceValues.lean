import Polytime2.Computation.Equality
import Polytime2.Computation.Conditional
import Polytime2.Arrays.Transform

/-! # Replacing a value throughout an array

The two context values are the old and new values. Equality and conditional
selection certify the scalar operation, and array transformation lifts it.
This is the merge operation needed for equation-class label tables.
-/

namespace Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def replaceElement (domain : EncodedDomain.{0, 0} Parameter) :
    Computation Parameter (Fin 3) := by
  classical
  exact {
    inputDomains := fun _ => domain
    outputDomain := domain
    precondition := fun _ _ => True
    compute := fun _ arguments => if arguments.val 2 = arguments.val 0 then arguments.val 1 else arguments.val 2 }

private theorem replaceElement_realizable (domain : EncodedDomain.{0, 0} Parameter) :
    (replaceElement domain).Realizable := by
  classical
  let inputs : Fin 3 → EncodedDomain Parameter := fun _ => domain
  have compare := (elementsEqual_realizable domain).onArguments inputs (fun _ _ => True)
    (fun choice => if choice then 0 else 2) (by intro choice; cases choice <;> rfl) (by intros; trivial)
  have selected := Realizable.conditional inputs domain (fun _ _ => True)
    (fun _ arguments => decide (arguments.val 2 = arguments.val 0))
    (fun _ arguments => arguments.val 1) (fun _ arguments => arguments.val 2)
    compare (Realizable.argument inputs 1 (fun _ _ => True)) (Realizable.argument inputs 2 (fun _ _ => True))
  exact selected.withSpecification (replaceElement domain).precondition (replaceElement domain).compute
    (by intros; trivial) (by intros; simp [replaceElement])

/-- Replace every occurrence of the first context value by the second. -/
noncomputable def arrayReplaceValues (domain : EncodedDomain.{0, 0} Parameter)
    (length : MvPolynomial Parameter ℕ) := by
  classical
  exact arrayTransform (fun _ : Bool => domain) domain domain length
    (fun _ context value => if value = context false then context true else value)

theorem arrayReplaceValues_realizable (domain : EncodedDomain.{0, 0} Parameter)
    (length : MvPolynomial Parameter ℕ) : (arrayReplaceValues domain length).Realizable := by
  classical
  let operation sizes (context : Bool → domain.Carrier sizes) (value : domain.Carrier sizes) :=
    if value = context false then context true else value
  apply arrayTransform_realizable (fun _ : Bool => domain) domain domain length operation
  let step := arrayTransformStep (fun _ : Bool => domain) domain domain operation
  apply (replaceElement_realizable domain).onResults step.inputDomains step.precondition
    (fun name _ arguments => match name with
      | 0 => arguments.val (.inl false)
      | 1 => arguments.val (.inl true)
      | 2 => arguments.val (.inr ())) (by intros; trivial)
  intro name
  fin_cases name
  · exact Realizable.argument step.inputDomains (.inl false) step.precondition
  · exact Realizable.argument step.inputDomains (.inl true) step.precondition
  · exact Realizable.argument step.inputDomains (.inr ()) step.precondition

end Polytime2.Computation
