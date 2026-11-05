import Polytime2.Encoding.FiniteSubsets
import Polytime2.Arrays.Operations
import Polytime2.Computation.Reindex

/-! # Certified access to ordinary finite subsets

Membership reuses Boolean array lookup through the existing canonical codec.
The subset carrier remains an ordinary finset throughout the public contract.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Read membership at an actual coordinate of the finite interval. -/
noncomputable def finiteSubsetContains (length : MvPolynomial Parameter ℕ) : Computation Parameter Bool where
  inputDomains choice := if choice then finiteSubsets length else boundedIndex length
  outputDomain := booleans
  precondition _ _ := True
  compute sizes arguments := by
    let index : Fin (MvPolynomial.eval sizes length) := arguments.val false
    let selected : Finset (Fin (MvPolynomial.eval sizes length)) := arguments.val true
    exact decide (index ∈ selected)

theorem finiteSubsetContains_realizable (length : MvPolynomial Parameter ℕ) :
    (finiteSubsetContains length).Realizable := by
  let computation := finiteSubsetContains length
  have viewed := (arrayLookup_realizable booleans length).reinterpretInputs computation.inputDomains
    (fun choice sizes value => match choice with
      | false => value
      | true => finiteSubsetEquiv _ value)
    (by intro choice sizes; cases choice <;> rfl)
    (by intro choice sizes value; cases choice <;> rfl)
    computation.precondition (by intros; trivial)
  exact viewed.withSpecification computation.precondition computation.compute
    (by intros; trivial) (by intros; rfl)


/-- Retain all and only the coordinates whose supplied flags are true. -/
noncomputable def finiteSubsetFromFlags (length : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  encodingMap (booleans.arrayOfLength length) (finiteSubsets length)
    (fun sizes flags => (finiteSubsetEquiv (MvPolynomial.eval sizes length)).symm flags)

/-- Changing flags to the ordinary finset carrier copies identical bits. -/
theorem finiteSubsetFromFlags_realizable (length : MvPolynomial Parameter ℕ) :
    (finiteSubsetFromFlags length).Realizable := by
  apply encodingMap_realizable
  · intros; rfl
  · intro sizes flags
    change _ = ArrayEncoding.bits ((booleans.arrayOfLength length).encode sizes
      ((finiteSubsetEquiv _) ((finiteSubsetEquiv _).symm flags)))
    rw [Equiv.apply_symm_apply]

/-- Membership records exactly the supplied mathematical predicate. -/
theorem finiteSubsetFromFlags_mem (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (flags : Fin (MvPolynomial.eval sizes length) → Bool)
    (index : Fin (MvPolynomial.eval sizes length)) :
    index ∈ (show Finset (Fin (MvPolynomial.eval sizes length)) from
      (finiteSubsetFromFlags length).compute sizes ⟨fun _ => flags, trivial⟩) ↔ flags index = true := by
  classical
  change index ∈ (Finset.univ.filter (fun position => flags position = true)) ↔ _
  simp

end Polytime2.Computation
