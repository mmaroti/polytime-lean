import Mathlib.Data.List.OfFn

/-! # Mathematical arrays padded to a larger capacity -/

namespace Polytime2.Computation

/-- Retain every live element and fill the remaining coordinates. -/
def padArrayValues {Element : Type} {length capacity : ℕ}
    (fits : length ≤ capacity) (filler : Element) (values : Fin length → Element) :
    Fin capacity → Element :=
  fun index => Fin.append values (fun _ => filler)
    (Fin.cast (Nat.add_sub_of_le fits).symm index)

theorem padArrayValues_list {Element : Type} {length capacity : ℕ}
    (fits : length ≤ capacity) (filler : Element) (values : Fin length → Element) :
    List.ofFn (padArrayValues fits filler values) =
      List.ofFn values ++ List.replicate (capacity - length) filler := by
  unfold padArrayValues
  rw [List.ofFn_congr (Nat.add_sub_of_le fits).symm]
  simp only [Fin.cast_cast, Fin.cast_refl, id_eq, List.ofFn_fin_append, List.ofFn_const]

/-- Pointwise maps commute with padding, including the filler. -/
theorem map_padArrayValues {Element Target : Type} {length capacity : ℕ}
    (fits : length ≤ capacity) (filler : Element) (values : Fin length → Element)
    (map : Element → Target) :
    (fun index => map (padArrayValues fits filler values index)) =
      padArrayValues fits (map filler) (fun index => map (values index)) := by
  funext index
  unfold padArrayValues
  generalize Fin.cast (Nat.add_sub_of_le fits).symm index = position
  cases position using Fin.addCases <;> simp

end Polytime2.Computation
