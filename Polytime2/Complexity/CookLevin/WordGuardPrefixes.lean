import Polytime2.Complexity.CookLevin.WordGuardPrefix
import Polytime2.Arrays.Tabulate
import Polytime2.Arrays.FlattenRecords

/-! # Tabulating every prefix block of the word-code guard -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity.CookLevin

open Circuit EncodedDomain Polytime2.Computation

private noncomputable def prefixRows (base : MvPolynomial Bool ℕ)
    (available : ∀ sizes, sizes true * Fintype.card Letter ≤ MvPolynomial.eval sizes base) :
    Computation Bool Empty :=
  arrayTabulate Empty.elim (wordGuardPrefix base available).outputDomain (MvPolynomial.X true)
    (fun sizes _ position => (wordGuardPrefix base available).compute sizes ⟨(fun _ => position), trivial⟩)

private theorem prefixRows_realizable (base : MvPolynomial Bool ℕ)
    (available : ∀ sizes, sizes true * Fintype.card Letter ≤ MvPolynomial.eval sizes base) :
    (prefixRows base available).Realizable := by
  apply arrayTabulate_realizable
  let inputs : Empty ⊕ Unit → EncodedDomain Bool :=
    Sum.elim Empty.elim (fun _ => arrayPosition (MvPolynomial.X true))
  have selected := (wordGuardPrefix_realizable base available).onArguments inputs (fun _ _ => True)
    (fun _ => .inr ()) (by intros; rfl) (by intros; trivial)
  exact selected.withSpecification (fun _ _ => True) _ (by intros; trivial) (by intros; rfl)

/-- Emit the first copy of every letter-code test in increasing word order. -/
noncomputable def wordGuardPrefixes (base : MvPolynomial Bool ℕ)
    (available : ∀ sizes, sizes true * Fintype.card Letter ≤ MvPolynomial.eval sizes base) :
    Computation Bool Empty :=
  (prefixRows base available).followedBy
    (arrayFlattenRecords (gateDomain (wordGuardWires base)) letterExpression.gateCount (MvPolynomial.X true))
    rfl (by intros; trivial)

theorem wordGuardPrefixes_realizable (base : MvPolynomial Bool ℕ)
    (available : ∀ sizes, sizes true * Fintype.card Letter ≤ MvPolynomial.eval sizes base) :
    (wordGuardPrefixes base available).Realizable :=
  (prefixRows_realizable base available).followedBy
    (arrayFlattenRecords_realizable (gateDomain (wordGuardWires base)) letterExpression.gateCount (MvPolynomial.X true))
    rfl (by intros; trivial)

/-- The entire flat prefix array is the exact mathematical compiler prefix. -/
theorem wordGuardPrefixes_value (base : MvPolynomial Bool ℕ)
    (available : ∀ sizes, sizes true * Fintype.card Letter ≤ MvPolynomial.eval sizes base)
    (sizes : Bool → ℕ)
    (arguments : {arguments : (wordGuardPrefixes base available).Arguments sizes // True}) :
    List.ofFn (fun index => gateValue ((wordGuardPrefixes base available).compute sizes arguments index)) =
      (List.ofFn (fun position : Fin (MvPolynomial.eval sizes (MvPolynomial.X true)) =>
        ((wordLetterExpression _ position).compile
          (MvPolynomial.eval sizes base + letterExpression.gateCount * position.val)).1)).flatten := by
  simp only [wordGuardPrefixes, followedBy]
  rw [List.ofFn_comp' _ gateValue, arrayFlattenRecords_list]
  simp only [List.map_flatten, List.map_ofFn, Function.comp_def]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext position
  exact wordGuardPrefix_value base available sizes ⟨(fun _ => position), trivial⟩

end Polytime2.Complexity.CookLevin
