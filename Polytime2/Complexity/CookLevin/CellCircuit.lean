import Polytime2.Circuit.Local
import Polytime2.Complexity.CookLevin.LocalMachine
import Mathlib.Data.Fintype.EquivFin

/-! # Boolean circuits for finite marked-cell dynamics

The machine alphabet and states are fixed. Each marked tape cell is encoded
by one bit for each possible cell value. A radius-one update consequently
reads a fixed number of bits, independent of the input length or time bound.
This connects finite cell dynamics to the local Boolean circuit construction.
The finite decoder is used only in a specialization-fixed truth table.
-/

namespace Polytime2.Complexity.CookLevin

open Turing Circuit

variable {Symbol State : Type} [Inhabited Symbol]
variable [Fintype Symbol] [Fintype State]

/-- Number of bits in the one-hot representation of a marked tape cell. -/
abbrev cellWidth (Symbol State : Type) [Fintype Symbol] [Fintype State] :=
  Fintype.card (Cell Symbol State)

/-- One-hot encoding; the finite ordering is fixed with the machine. -/
noncomputable def encodeCell (cell : Cell Symbol State) : Fin (cellWidth Symbol State) → Bool :=
  fun bit => by
    classical
    exact decide (cell = (Fintype.equivFin (Cell Symbol State)).symm bit)

omit [Inhabited Symbol] in
theorem encodeCell_injective : Function.Injective (encodeCell (Symbol := Symbol) (State := State)) := by
  classical
  intro first second equal
  have secondHit : encodeCell second ((Fintype.equivFin (Cell Symbol State)) first) = true := by
    rw [← equal]
    simp [encodeCell]
  have same : second = first := by simpa [encodeCell] using secondHit
  exact same.symm

/-- Decode valid one-hot words. Other bit patterns have an arbitrary fixed
default interpretation, sufficient for the finite local truth table. -/
noncomputable def decodeCell (bits : Fin (cellWidth Symbol State) → Bool) : Cell Symbol State := by
  classical
  exact if existsCell : ∃ cell, encodeCell cell = bits then existsCell.choose else (default, none)

theorem decodeCell_encode (cell : Cell Symbol State) : decodeCell (encodeCell cell) = cell := by
  classical
  have existsCell : ∃ other, encodeCell other = encodeCell cell := ⟨cell, rfl⟩
  simp only [decodeCell, dite_eq_left existsCell]
  exact encodeCell_injective existsCell.choose_spec

/-- Flatten a finite array of ordinary marked cells into Boolean inputs. -/
noncomputable def encodeCells {positions : ℕ} (contents : Fin positions → Cell Symbol State) :
    Fin (positions * cellWidth Symbol State) → Bool :=
  fun index => encodeCell (contents (finProdFinEquiv.symm index).1) (finProdFinEquiv.symm index).2

/-- Read the three cell arguments from the local Boolean input block. -/
noncomputable def decodeNeighborhood
    (bits : Fin (3 * cellWidth Symbol State) → Bool) : Fin 3 → Cell Symbol State :=
  fun position => decodeCell (fun bit => bits (finProdFinEquiv (position, bit)))

/-- The Boolean sources for every output bit select three neighboring cells,
with all bits of each selected cell retained. -/
def cellSources (positions : ℕ) (neighbors : Fin positions → Fin 3 → Fin positions) :
    Fin (positions * cellWidth Symbol State) →
      Fin (3 * cellWidth Symbol State) → Fin (positions * cellWidth Symbol State) :=
  fun output argument => finProdFinEquiv
    (neighbors (finProdFinEquiv.symm output).1 (finProdFinEquiv.symm argument).1,
      (finProdFinEquiv.symm argument).2)

/-- The fixed local cell transition, expanded to one Boolean table per bit.
Position dependence permits boundary cells to supply blank neighbors. -/
noncomputable def cellTables (positions : ℕ)
    (update : Fin positions → (Fin 3 → Cell Symbol State) → Cell Symbol State) :
    Fin (positions * cellWidth Symbol State) → (Fin (3 * cellWidth Symbol State) → Bool) → Bool :=
  fun output bits => encodeCell (update (finProdFinEquiv.symm output).1 (decodeNeighborhood bits))
    (finProdFinEquiv.symm output).2

/-- Ordinary mathematical dynamics of a finite array of marked cells. -/
def cellTransition {positions : ℕ} (neighbors : Fin positions → Fin 3 → Fin positions)
    (update : Fin positions → (Fin 3 → Cell Symbol State) → Cell Symbol State)
    (contents : Fin positions → Cell Symbol State) : Fin positions → Cell Symbol State :=
  fun position => update position (fun argument => contents (neighbors position argument))

theorem cellTables_encode (positions : ℕ) (neighbors : Fin positions → Fin 3 → Fin positions)
    (update : Fin positions → (Fin 3 → Cell Symbol State) → Cell Symbol State)
    (contents : Fin positions → Cell Symbol State)
    (output : Fin (positions * cellWidth Symbol State)) :
    cellTables positions update output
      (fun argument => encodeCells contents (cellSources positions neighbors output argument)) =
      encodeCells (cellTransition neighbors update contents) output := by
  simp only [cellTables, cellSources, encodeCells, Equiv.symm_apply_apply]
  congr 2
  funext argument
  simp only [decodeNeighborhood, Equiv.symm_apply_apply]
  exact decodeCell_encode _

/-- Finite cell dynamics commute with their Boolean encoding. -/
theorem cellTransition_iterate_encode (positions steps : ℕ)
    (neighbors : Fin positions → Fin 3 → Fin positions)
    (update : Fin positions → (Fin 3 → Cell Symbol State) → Cell Symbol State)
    (contents : Fin positions → Cell Symbol State) :
    (fun current output => cellTables positions update output
      (fun argument => current (cellSources positions neighbors output argument)))^[steps]
        (encodeCells contents) = encodeCells ((cellTransition neighbors update)^[steps] contents) := by
  induction steps with
  | zero => rfl
  | succ steps induction =>
    rw [Function.iterate_succ_apply', induction, Function.iterate_succ_apply']
    funext output
    exact cellTables_encode positions neighbors update _ output

end Polytime2.Complexity.CookLevin
