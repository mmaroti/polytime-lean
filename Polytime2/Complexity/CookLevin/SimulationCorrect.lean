import Polytime2.Complexity.CookLevin.SimulationProgram

/-! # Agreement of uniform construction with mathematical unrolling

The constructor's time/cell/bit blocks are exactly the corresponding blocks of
the shared-wire circuit compiler, including boundary cells and time zero.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity.CookLevin

open Turing Circuit EncodedDomain Polytime2.Computation

variable {Symbol State : Type} [Inhabited Symbol] [Inhabited State]
variable [Fintype Symbol] [Fintype State]

private theorem layoutPositions_window (sizes : Unit → ℕ) :
    MvPolynomial.eval sizes layoutPositions = 2 * (2 * sizes ()) + 1 := by
  simp only [layoutPositions, map_add, map_mul, map_ofNat, map_one, MvPolynomial.eval_X]
  omega

/-- A tabulated block is the corresponding expression block in the unrolled
finite-window machine circuit. -/
theorem cellProgram_unroll_block (machine : TM0.Machine Symbol State) (sizes : Unit → ℕ)
    (time : Fin (MvPolynomial.eval sizes (MvPolynomial.X ())))
    (cell : Fin (MvPolynomial.eval sizes layoutPositions)) (bit : Fin (cellWidth Symbol State)) :
    let positions := 2 * (2 * sizes ()) + 1
    let width := positions * cellWidth Symbol State
    let output := finProdFinEquiv (cell.cast (layoutPositions_window sizes), bit)
    let expressions := localExpressions width (3 * cellWidth Symbol State)
      (cellSources positions (windowNeighbors (2 * sizes ())))
      (cellTables positions (windowUpdate machine (2 * sizes ())))
    List.ofFn (fun slot => gateValue ((cellProgram machine bit).compute sizes
      ⟨(show ∀ name, (blockBaseInputs name).Carrier sizes from
        fun name => match name with | false => time | true => cell), trivial⟩ slot)) =
      (((expressions output).rename (layerNames (stepInputWire width (cellBlockSize Symbol State) time.val))).compile
        (width + time.val * (width * cellBlockSize Symbol State) + output.val * cellBlockSize Symbol State)).1 := by
  dsimp only
  rw [cellProgram_value, localCellExpression_eq,
    Expression.rename_layerNames_comp (cellExpression_valid machine _) (cellSources _ _ _) _]
  have tag : cellTemplateAt (2 * sizes ()) (finProdFinEquiv (cell.cast (layoutPositions_window sizes), bit)) =
      ((decide (cell.val = 0), decide (cell.val = 4 * sizes ())), bit) := by
    have radius : 2 * (2 * sizes ()) = 4 * sizes () := by omega
    simp [cellTemplateAt, radius]
  rw [tag]
  have sources : ∀ port : Fin (3 * cellWidth Symbol State),
      ((sourceWire (Symbol := Symbol) (State := State) (finProdFinEquiv.symm port).2).compute sizes
        ⟨(fun name => match name with
          | false => time
          | true => (neighborCoordinate (finProdFinEquiv.symm port).1).compute sizes
              ⟨(fun _ => cell), trivial⟩), trivial⟩).val =
      stepInputWire ((2 * (2 * sizes ()) + 1) * cellWidth Symbol State)
        (cellBlockSize Symbol State) time.val
        (cellSources (2 * (2 * sizes ()) + 1) (windowNeighbors (2 * sizes ()))
          (finProdFinEquiv (cell.cast (layoutPositions_window sizes), bit)) port) := by
    intro port
    rw [sourceWire_stepInputWire]
    have neighbor :
        ((neighborCoordinate (finProdFinEquiv.symm port).1).compute sizes ⟨(fun _ => cell), trivial⟩).val =
          (windowNeighbors (2 * sizes ()) (cell.cast (layoutPositions_window sizes))
            (finProdFinEquiv.symm port).1).val :=
      neighborCoordinate_correct (finProdFinEquiv.symm port).1 sizes (fun _ => cell)
    simp only [finProdFinEquiv] at neighbor
    simp only [cellSources, Equiv.symm_apply_apply]
    cases step : time.val <;>
      simp only [stepInputWire, finProdFinEquiv, Equiv.coe_fn_mk,
        layoutPositions_window, neighbor]
  have base : ((blockBase bit).compute sizes
      ⟨(show ∀ name, (blockBaseInputs name).Carrier sizes from
        fun name => match name with | false => time | true => cell), trivial⟩).val =
      (2 * (2 * sizes ()) + 1) * cellWidth Symbol State +
        time.val * ((2 * (2 * sizes ()) + 1) * cellWidth Symbol State * cellBlockSize Symbol State) +
        (finProdFinEquiv (cell.cast (layoutPositions_window sizes), bit)).val * cellBlockSize Symbol State := by
    rw [blockBase_correct]
    simp only [layoutWidth, layoutLayerGates, map_mul, MvPolynomial.eval_C,
      layoutPositions_window, finProdFinEquiv, Equiv.coe_fn_mk, Fin.val_cast]
    ring
  congr 2
  congr 1
  funext wire
  by_cases bound : wire < 3 * cellWidth Symbol State
  · simp only [layerNames, dite_eq_left bound]
    convert sources ⟨wire, bound⟩ using 1; congr 2
  · simp only [layerNames, dite_eq_right bound]

/-- Forget the nested canonical storage, retaining the program's gate order. -/
noncomputable def simulationGates (machine : TM0.Machine Symbol State) (sizes : Unit → ℕ) : List Gate :=
  let program := (simulationProgram machine).compute sizes ⟨(fun empty => nomatch empty), trivial⟩
  (List.ofFn (fun time : Fin (sizes ()) =>
    (List.ofFn (fun cell : Fin (2 * (2 * sizes ()) + 1) =>
      (List.ofFn (fun bit : Fin (cellWidth Symbol State) =>
        List.ofFn (fun slot => gateValue (program (time.cast (by simp))
          (cell.cast (layoutPositions_window sizes).symm) bit slot)))).flatten)).flatten)).flatten

/-- The complete gate array has exactly the shared-wire unrolling gate list. -/
theorem simulationGates_eq (machine : TM0.Machine Symbol State) (sizes : Unit → ℕ) :
    simulationGates machine sizes =
      (unroll (localExpressions ((2 * (2 * sizes ()) + 1) * cellWidth Symbol State) (3 * cellWidth Symbol State)
        (cellSources (2 * (2 * sizes ()) + 1) (windowNeighbors (2 * sizes ())))
        (cellTables (2 * (2 * sizes ()) + 1) (windowUpdate machine (2 * sizes ())))) (sizes ())).1 := by
  let expressions := localExpressions ((2 * (2 * sizes ()) + 1) * cellWidth Symbol State) (3 * cellWidth Symbol State)
    (cellSources (2 * (2 * sizes ()) + 1) (windowNeighbors (2 * sizes ())))
    (cellTables (2 * (2 * sizes ()) + 1) (windowUpdate machine (2 * sizes ())))
  have uniform : ∀ index, (expressions index).gateCount = cellBlockSize Symbol State := by
    intro index
    rw [show expressions index = _ from localCellExpression_eq machine (2 * sizes ()) index,
      Expression.rename_gateCount, cellExpression_gateCount]
  rw [unroll_uniform_gates expressions (cellBlockSize Symbol State) uniform cellBlockSize_positive]
  unfold simulationGates
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext time
  rw [List.ofFn_mul]
  rw [List.flatten_flatten, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext cell
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext bit
  rw [simulationProgram_block]
  have block := cellProgram_unroll_block machine sizes (time.cast (by simp))
    (cell.cast (layoutPositions_window sizes).symm) bit
  dsimp only at block
  simp only [Fin.val_cast, Fin.cast_cast, Fin.cast_refl, id_eq] at block
  have indexEqual : finProdFinEquiv (cell, bit) =
      (⟨cell.val * cellWidth Symbol State + bit.val, by
        have bounded := (finProdFinEquiv (cell, bit)).isLt
        simpa only [finProdFinEquiv, Equiv.coe_fn_mk, Nat.mul_comm, Nat.add_comm] using bounded⟩ :
        Fin ((2 * (2 * sizes ()) + 1) * cellWidth Symbol State)) := by
    apply Fin.ext
    simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  convert block using 1 <;> congr 2
  all_goals rw [indexEqual]

end Polytime2.Complexity.CookLevin
