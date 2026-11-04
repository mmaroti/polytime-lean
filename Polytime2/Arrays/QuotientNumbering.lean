import Polytime2.Arrays.QuotientLabels
import Polytime2.Arrays.PackingResult
import Polytime2.Arrays.ZipWith

/-! # Stable numbering of equation classes

Pack exactly the fixed class labels in increasing coordinate order. The
packing count is the number of quotient classes, and the existing packing
rank gives their dense numbering. All capacities remain internal to codecs.
-/

namespace Polytime2.ArrayQuotient

variable {vertices : ℕ}

def representativeFlags (equations : List (Fin vertices × Fin vertices)) (value : Fin vertices) : Bool :=
  decide (labels equations value = value)

/-- Stable packing identifies precisely the quotient classes with the dense
interval of the actual class count. -/
noncomputable def numberingEquiv (equations : List (Fin vertices × Fin vertices)) :
    Quot (equationRelation equations) ≃ Fin (ArrayPacking.count (representativeFlags equations)) :=
  (representativeEquiv equations).trans
    ((Equiv.subtypeEquivRight (fun _ => by simp [representativeFlags])).trans
      (ArrayPacking.selection (representativeFlags equations)).toEquiv.symm)

theorem numbering_count (equations : List (Fin vertices × Fin vertices)) :
    Nat.card (Quot (equationRelation equations)) = ArrayPacking.count (representativeFlags equations) := by
  simpa using Nat.card_congr (numberingEquiv equations)

theorem numbering_apply (equations : List (Fin vertices × Fin vertices)) (value : Fin vertices) :
    numberingEquiv equations (Quot.mk (equationRelation equations) value) =
      ArrayPacking.rank (representativeFlags equations)
        ⟨labels equations value, by simp [representativeFlags, labels_idempotent]⟩ := rfl

theorem selection_numbering (equations : List (Fin vertices × Fin vertices)) (value : Fin vertices) :
    (ArrayPacking.selection (representativeFlags equations)
      (numberingEquiv equations (Quot.mk (equationRelation equations) value))).val = labels equations value := by
  rw [numbering_apply]
  exact ArrayPacking.selection_rank _ _

end Polytime2.ArrayQuotient

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Mark exactly the coordinates that are their own class representatives. -/
noncomputable def fixedPointFlags (vertices : MvPolynomial Parameter ℕ) : Computation Parameter Unit := by
  classical
  exact unaryMap ((boundedIndex vertices).arrayOfLength vertices) (booleans.arrayOfLength vertices)
    (fun _ _ => True) (fun _ arguments index => decide (arguments.val index = index))

theorem fixedPointFlags_realizable (vertices : MvPolynomial Parameter ℕ) :
    (fixedPointFlags vertices).Realizable := by
  let index := boundedIndex vertices
  let computation := fixedPointFlags vertices
  have positions := (arrayBoundedPositions_realizable vertices).withArguments computation.inputDomains
    ⟨Empty.elim, by intro name; exact name.elim⟩ (by intro name; exact name.elim)
  have compared := (elementsEqual_realizable index).zipWith vertices
  have prepared := compared.onResults computation.inputDomains computation.precondition
    (fun name _ arguments => match name with
      | .inl empty => empty.elim
      | .inr false => arguments.val ()
      | .inr true => id) (by intros; trivial) (by
        intro name
        rcases name with empty | side
        · exact empty.elim
        · cases side
          · exact Realizable.argument computation.inputDomains () computation.precondition
          · exact positions)
  exact prepared.withSpecification computation.precondition computation.compute
    (by intros; trivial) (by
      intro sizes arguments valid
      funext position
      apply Bool.eq_iff_iff.mpr
      simp [onResults, arrayZipWith, computation, fixedPointFlags, unaryMap])

/-- Return the actual count and increasing list of fixed class labels. -/
noncomputable def fixedPointRepresentatives (vertices : MvPolynomial Parameter ℕ) :=
  (arrayPack (boundedIndex vertices) vertices).onResults (fixedPointFlags vertices).inputDomains
    (fun _ _ => True)
    (fun name sizes arguments => match name with
      | false => (fixedPointFlags vertices).compute sizes arguments
      | true => id) (by intros; trivial)

theorem fixedPointRepresentatives_realizable (vertices : MvPolynomial Parameter ℕ) :
    (fixedPointRepresentatives vertices).Realizable := by
  apply (arrayPack_realizable (boundedIndex vertices) vertices).onResults
  intro name
  cases name
  · exact fixedPointFlags_realizable vertices
  · exact (arrayBoundedPositions_realizable vertices).withArguments _
      ⟨Empty.elim, by intro name; exact name.elim⟩ (by intro name; exact name.elim)

/-- Identify equation classes and retain exactly one representative per class.
The result's dependent count is the actual quotient size. -/
noncomputable def quotientRepresentatives (vertices equations : MvPolynomial Parameter ℕ) :=
  (quotientLabels vertices equations).followedBy (fixedPointRepresentatives vertices) rfl (by intros; trivial)

theorem quotientRepresentatives_realizable (vertices equations : MvPolynomial Parameter ℕ) :
    (quotientRepresentatives vertices equations).Realizable :=
  (quotientLabels_realizable vertices equations).followedBy
    (fixedPointRepresentatives_realizable vertices) rfl (by intros; trivial)

/-- The result is precisely the increasing enumeration of fixed labels, with
its actual mathematical count. -/
theorem quotientRepresentatives_compute (vertices equations : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (input : Fin (MvPolynomial.eval sizes equations) →
      Fin (MvPolynomial.eval sizes vertices) × Fin (MvPolynomial.eval sizes vertices)) :
    (quotientRepresentatives vertices equations).compute sizes ⟨fun _ => input, trivial⟩ =
      ⟨⟨ArrayPacking.count (ArrayQuotient.representativeFlags (List.ofFn input)),
        Nat.lt_succ_of_le (ArrayPacking.count_le _)⟩,
        fun index => (ArrayPacking.selection (ArrayQuotient.representativeFlags (List.ofFn input)) index).val⟩ := by
  have flagsEquality : (fixedPointFlags vertices).compute sizes
      ⟨fun _ => ArrayQuotient.labels (List.ofFn input), trivial⟩ =
      ArrayQuotient.representativeFlags (List.ofFn input) := by
    funext position
    apply Bool.eq_iff_iff.mpr
    simp only [fixedPointFlags, unaryMap, ArrayQuotient.representativeFlags, decide_eq_true_eq]
  simp only [quotientRepresentatives, followedBy, fixedPointRepresentatives, onResults,
    arrayPack, quotientLabels, unaryMap]
  rw [flagsEquality]
  rfl

/-- The packed result has exactly one entry per mathematical quotient class. -/
theorem quotientRepresentatives_count (vertices equations : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (input : Fin (MvPolynomial.eval sizes equations) →
      Fin (MvPolynomial.eval sizes vertices) × Fin (MvPolynomial.eval sizes vertices)) :
    ((quotientRepresentatives vertices equations).compute sizes ⟨fun _ => input, trivial⟩).1.val =
      Nat.card (Quot (ArrayQuotient.equationRelation (List.ofFn input))) := by
  rw [ArrayQuotient.numbering_count]
  rw [quotientRepresentatives_compute]

end Polytime2.Computation
