import Polytime2.Arrays.Packing
import Mathlib.Data.List.Sort

/-! # Stable packing of a prefix and a later interval

The selected coordinates retain the source prefix and one subsequent interval.
This mathematical contract supports removing an internal header and trailing
padding while preserving all retained elements and their order.
-/

namespace Polytime2.ArrayPacking

/-- Retain a prefix and a disjoint subsequent half-open interval. -/
def prefixIntervalFlags {length : ℕ} (prefixLength offset count : ℕ) (index : Fin length) : Bool :=
  decide (index.val < prefixLength ∨ offset ≤ index.val ∧ index.val < offset + count)

/-- Packing a prefix and a later interval concatenates exactly those arrays. -/
theorem pack_prefix_interval {Element : Type*} {length : ℕ} (prefixLength offset count : ℕ)
    (separated : prefixLength ≤ offset) (bounded : offset + count ≤ length) (values : Fin length → Element) :
    List.ofFn (pack (prefixIntervalFlags prefixLength offset count) values) =
      List.ofFn (fun index : Fin prefixLength => values ⟨index.val, by omega⟩) ++
        List.ofFn (fun index : Fin count => values ⟨offset + index.val, by omega⟩) := by
  let flags := prefixIntervalFlags (length := length) prefixLength offset count
  let first : Fin prefixLength → Fin length := fun index => ⟨index.val, by omega⟩
  let second : Fin count → Fin length := fun index => ⟨offset + index.val, by omega⟩
  have indices : List.ofFn (fun position => (selection flags position).val) =
      List.ofFn first ++ List.ofFn second := by
    apply List.Pairwise.eq_of_mem_iff (r := fun left right : Fin length => left < right)
    · exact List.pairwise_ofFn.mpr (selection_strictMono flags)
    · apply List.pairwise_append.mpr
      refine ⟨List.pairwise_ofFn.mpr ?_, List.pairwise_ofFn.mpr ?_, ?_⟩
      · intro left right ordered
        exact ordered
      · intro left right ordered
        change offset + left.val < offset + right.val
        exact Nat.add_lt_add_left ordered offset
      · intro left leftMember right rightMember
        obtain ⟨leftIndex, rfl⟩ := List.mem_ofFn.mp leftMember
        obtain ⟨rightIndex, rfl⟩ := List.mem_ofFn.mp rightMember
        change leftIndex.val < offset + rightIndex.val
        omega
    · intro index
      simp only [List.mem_ofFn, List.mem_append]
      constructor
      · rintro ⟨position, rfl⟩
        have active := selection_active flags position
        change decide (_ < prefixLength ∨ offset ≤ _ ∧ _ < offset + count) = true at active
        rcases of_decide_eq_true active with before | inside
        · exact Or.inl ⟨⟨_, before⟩, Fin.ext rfl⟩
        · exact Or.inr ⟨⟨(selection flags position).val.val - offset, by omega⟩,
            Fin.ext (by dsimp [second]; omega)⟩
      · intro member
        have active : flags index = true := by
          rcases member with ⟨position, rfl⟩ | ⟨position, rfl⟩
          · simp only [flags, prefixIntervalFlags, first, decide_eq_true_eq]
            exact Or.inl position.isLt
          · simp only [flags, prefixIntervalFlags, second, decide_eq_true_eq]
            exact Or.inr ⟨by omega, by omega⟩
        exact ⟨rank flags ⟨index, active⟩, selection_rank flags ⟨index, active⟩⟩
  have mapped := congrArg (List.map values) indices
  simp only [List.map_append, List.map_ofFn, Function.comp_def] at mapped
  exact mapped

private theorem ofFn_segment {Element : Type*} {length : ℕ} (values : Fin length → Element)
    (offset count : ℕ) (bounded : offset + count ≤ length) :
    List.ofFn (fun index : Fin count => values ⟨offset + index.val, by omega⟩) =
      ((List.ofFn values).drop offset).take count := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_take, List.length_drop]
    omega
  · intro index firstBound secondBound
    simp only [List.getElem_ofFn, List.getElem_take, List.getElem_drop]

/-- Stable packing agrees with ordinary list take/drop/take on finite arrays. -/
theorem pack_prefix_interval_ofFn {Element : Type*} {length : ℕ} (values : Fin length → Element)
    (prefixLength offset count : ℕ) (separated : prefixLength ≤ offset)
    (bounded : offset + count ≤ length) :
    List.ofFn (pack (prefixIntervalFlags prefixLength offset count) values) =
      (List.ofFn values).take prefixLength ++ ((List.ofFn values).drop offset).take count := by
  rw [pack_prefix_interval prefixLength offset count separated bounded]
  have first := ofFn_segment values 0 prefixLength (by omega)
  simp only [Nat.zero_add, List.drop_zero] at first
  exact congrArg₂ List.append first (ofFn_segment values offset count bounded)

/-- The same two-interval selection on a list is ordinary take/drop/take. -/
theorem pack_prefix_interval_list {Element : Type*} (source : List Element)
    (prefixLength offset count : ℕ) (separated : prefixLength ≤ offset)
    (bounded : offset + count ≤ source.length) :
    List.ofFn (pack (prefixIntervalFlags prefixLength offset count) source.get) =
      source.take prefixLength ++ (source.drop offset).take count := by
  simpa only [List.ofFn_get] using pack_prefix_interval_ofFn source.get prefixLength offset count separated bounded

end Polytime2.ArrayPacking
