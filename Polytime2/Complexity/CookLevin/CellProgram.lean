import Polytime2.Complexity.CookLevin.SourceWire
import Polytime2.Complexity.CookLevin.NeighborCoordinates
import Polytime2.Complexity.CookLevin.BoundaryTag

/-! # Certified local transition block construction

The constructor receives mathematical time and cell coordinates. It prepares
the block base, all predecessor references, and the boundary tag through
certified computations, then emits the fixed machine template.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity.CookLevin

open Turing Circuit EncodedDomain Polytime2.Computation

variable {Symbol State : Type} [Inhabited Symbol] [Inhabited State]
variable [Fintype Symbol] [Fintype State]

private noncomputable def neighborSource (direction : Fin 3) (bit : Fin (cellWidth Symbol State)) :
    Computation Unit Bool :=
  (sourceWire bit).onResults blockBaseInputs (fun _ _ => True)
    (fun name sizes arguments => match name with
      | false => arguments.val false
      | true => (neighborCoordinate direction).compute sizes ⟨(fun _ => arguments.val true), trivial⟩)
    (by intros; trivial)

omit [Inhabited State] in
private theorem neighborSource_realizable (direction : Fin 3) (bit : Fin (cellWidth Symbol State)) :
    (neighborSource direction bit).Realizable := by
  unfold neighborSource
  apply (sourceWire_realizable bit).onResults
  intro name
  cases name
  · exact Realizable.argument blockBaseInputs false (fun _ _ => True)
  · exact (neighborCoordinate_realizable direction).withArguments
      blockBaseInputs (MultiTape.oneTape true) (fun _ => rfl)

/-- Emit the gates for a chosen output bit of the current time/cell block. -/
noncomputable def cellProgram (machine : TM0.Machine Symbol State) (bit : Fin (cellWidth Symbol State)) :
    Computation Unit Bool :=
  (emitCellProgramAt machine (layoutWires Symbol State)).onResults blockBaseInputs (fun _ _ => True)
    (fun name sizes arguments => match name with
      | .inl (.inl _) => (blockBase bit).compute sizes arguments
      | .inl (.inr port) =>
          (neighborSource (finProdFinEquiv.symm port).1 (finProdFinEquiv.symm port).2).compute sizes arguments
      | .inr _ => (boundaryTag bit).compute sizes ⟨(fun _ => arguments.val true), trivial⟩)
    (by intro sizes arguments; exact blockBase_result_fits bit sizes arguments.val)

theorem cellProgram_realizable (machine : TM0.Machine Symbol State) (bit : Fin (cellWidth Symbol State)) :
    (cellProgram machine bit).Realizable := by
  unfold cellProgram
  apply (emitCellProgramAt_realizable machine (layoutWires Symbol State)).onResults
  intro name
  cases name with
  | inl coordinate =>
    cases coordinate with
    | inl singleton =>
      cases singleton
      exact blockBase_realizable bit
    | inr port => exact neighborSource_realizable (finProdFinEquiv.symm port).1 (finProdFinEquiv.symm port).2
  | inr singleton =>
    cases singleton
    exact (boundaryTag_realizable bit).withArguments blockBaseInputs (MultiTape.oneTape true) (fun _ => rfl)

/-- The emitted block is exactly the mathematical local-expression compiler,
with the prepared predecessor wires and the actual window boundary flags. -/
theorem cellProgram_value (machine : TM0.Machine Symbol State) (bit : Fin (cellWidth Symbol State))
    (sizes : Unit → ℕ) (arguments : (cellProgram machine bit).Arguments sizes) :
    List.ofFn (fun index => gateValue ((cellProgram machine bit).compute sizes ⟨arguments, trivial⟩ index)) =
      (((cellExpression machine
        ((decide ((arguments true).val = 0), decide ((arguments true).val = 4 * sizes ())), bit)).rename
        (layerNames (fun port =>
          ((sourceWire (Symbol := Symbol) (State := State) (finProdFinEquiv.symm port).2).compute sizes
            ⟨(fun name => match name with
              | false => arguments false
              | true => (neighborCoordinate (finProdFinEquiv.symm port).1).compute sizes
                  ⟨(fun _ => arguments true), trivial⟩), trivial⟩).val))).compile
        ((blockBase bit).compute sizes ⟨arguments, trivial⟩).val).1 := by
  have emitted := emitCellProgramAt_value machine (layoutWires Symbol State) sizes
    ((boundaryTag bit).compute sizes ⟨(fun _ => arguments true), trivial⟩)
    ((blockBase bit).compute sizes ⟨arguments, trivial⟩)
    (fun port => (neighborSource (finProdFinEquiv.symm port).1 (finProdFinEquiv.symm port).2).compute
      sizes ⟨arguments, trivial⟩) (blockBase_result_fits bit sizes arguments)
  convert emitted using 1 <;>
    simp [cellProgram, onResults, neighborSource, boundaryTag, unaryMap]
  funext index
  congr 2

end Polytime2.Complexity.CookLevin
