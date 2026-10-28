import Polytime2.Complexity.CookLevin.WordInput
import Mathlib.Data.List.OfFn

/-! # Prefixes in the existing one-hot word encoding

Fixing complete initial letter blocks is exactly fixing the corresponding
word prefix. No condition is imposed on the remaining letters.
-/

namespace Polytime2.Complexity.CookLevin

/-- Restricting initial one-hot blocks commutes with restricting word positions. -/
theorem encodeWordBits_restrict {small large : ℕ} (bounded : small ≤ large)
    (word : Fin large → Letter) (index : Fin (small * Fintype.card Letter)) :
    encodeWordBits word (index.castLE (Nat.mul_le_mul_right _ bounded)) =
      encodeWordBits (fun position => word (position.castLE bounded)) index := by
  have position :
      (finProdFinEquiv.symm (index.castLE (Nat.mul_le_mul_right _ bounded))).1 =
        (finProdFinEquiv.symm index).1.castLE bounded := Fin.ext rfl
  have letter :
      (finProdFinEquiv.symm (index.castLE (Nat.mul_le_mul_right _ bounded))).2 =
        (finProdFinEquiv.symm index).2 := Fin.ext rfl
  simp only [encodeWordBits]
  apply Bool.decide_congr
  rw [position, letter]

/-- All bits of an initial block agree precisely when all its letters agree. -/
theorem encodeWordBits_prefix_iff {small large : ℕ} (bounded : small ≤ large)
    (word : Fin large → Letter) (fixedWord : Fin small → Letter) :
    (∀ index : Fin (small * Fintype.card Letter),
      encodeWordBits word (index.castLE (Nat.mul_le_mul_right _ bounded)) = encodeWordBits fixedWord index) ↔
      ∀ position : Fin small, word (position.castLE bounded) = fixedWord position := by
  constructor
  · intro agrees
    have equal : encodeWordBits (fun position => word (position.castLE bounded)) = encodeWordBits fixedWord := by
      funext index
      rw [← encodeWordBits_restrict bounded word index]
      exact agrees index
    exact congrFun (encodeWordBits_injective equal)
  · intro agrees index
    have equal : (fun position => word (position.castLE bounded)) = fixedWord := funext agrees
    rw [encodeWordBits_restrict bounded word index, equal]

/-- Agreement at initial word coordinates is ordinary list-prefix equality. -/
theorem word_prefix_take_iff {small large : ℕ} (bounded : small ≤ large)
    (word : Fin large → Letter) (fixedWord : Fin small → Letter) :
    (∀ position : Fin small, word (position.castLE bounded) = fixedWord position) ↔
      (List.ofFn word).take small = List.ofFn fixedWord := by
  constructor
  · intro agrees
    apply List.ext_getElem
    · simp [Nat.min_eq_left bounded]
    · intro index firstBound secondBound
      simp only [List.length_take, List.length_ofFn] at firstBound secondBound
      simp only [List.getElem_take, List.getElem_ofFn]
      exact agrees ⟨index, secondBound⟩
  · intro equal position
    have point := congrArg (fun source : Word => source[position.val]?) equal
    have within := position.isLt.trans_le bounded
    simp [position.isLt, within] at point
    exact point

/-- Passing between a finite word and its list leaves the one-hot bits unchanged. -/
theorem encodeWordBits_ofFn {length : ℕ} (word : Fin length → Letter) :
    List.ofFn (encodeWordBits word) = List.ofFn (encodeWordBits (List.ofFn word).get) := by
  have letters : (List.ofFn word).get = fun index => word (index.cast List.length_ofFn) := by
    funext index
    rw [List.get_ofFn]
  have bits (index : Fin ((List.ofFn word).length * Fintype.card Letter)) :
      encodeWordBits (List.ofFn word).get index =
        encodeWordBits word (index.cast (congrArg (fun count => count * Fintype.card Letter) List.length_ofFn)) := by
    rw [letters]
    exact encodeWordBits_cast List.length_ofFn.symm word index
  rw [List.ofFn_congr (congrArg (fun count => count * Fintype.card Letter) (List.length_ofFn (f := word)).symm)]
  apply congrArg List.ofFn
  funext index
  exact (bits index).symm

end Polytime2.Complexity.CookLevin
