import Polytime2.Complexity.CookLevin.FiniteWindow
import Polytime2.Circuit.ExpressionTemplate
import Polytime2.Circuit.TemplateChoice
import Polytime2.Circuit.UniformUnroll

/-! # The fixed finite templates of a word verifier

A local gate block depends only on the chosen output bit and two boundary
flags. All of those choices are fixed finite data of the machine. Every
template has the same positive gate count, independently of tape dimensions.
The certified emitter selects that finite data and substitutes wire indices.
-/

namespace Polytime2.Complexity.CookLevin

open Turing Circuit EncodedDomain Polytime2.Computation

variable {Symbol State : Type} [Inhabited Symbol] [Inhabited State]
variable [Fintype Symbol] [Fintype State]

/-- Two boundary flags and the chosen bit of the marked-cell alphabet. -/
abbrev CellTemplateTag (Symbol State : Type) [Fintype Symbol] [Fintype State] :=
  (Bool × Bool) × Fin (cellWidth Symbol State)

/-- A specialization-fixed local Boolean table, including both boundaries
when the finite window contains just one cell. -/
noncomputable def fixedCellTable (machine : TM0.Machine Symbol State)
    (tag : CellTemplateTag Symbol State) (bits : Fin (3 * cellWidth Symbol State) → Bool) : Bool :=
  let neighbors := decodeNeighborhood bits
  encodeCell (localStep machine (if tag.1.1 then (default, none) else neighbors 0) (neighbors 1)
    (if tag.1.2 then (default, none) else neighbors 2)) tag.2

noncomputable def cellExpression (machine : TM0.Machine Symbol State) (tag : CellTemplateTag Symbol State) :
    Expression :=
  Expression.truthTable (3 * cellWidth Symbol State) 0 (fixedCellTable machine tag)

/-- One machine-fixed gate count, shared by every local output table. -/
noncomputable def cellBlockSize (Symbol State : Type) [Fintype Symbol] [Fintype State] : ℕ :=
  (Expression.truthTable (3 * cellWidth Symbol State) 0 (fun _ => false)).gateCount

theorem cellExpression_valid (machine : TM0.Machine Symbol State) (tag : CellTemplateTag Symbol State) :
    (cellExpression machine tag).Valid (3 * cellWidth Symbol State) :=
  Expression.truthTable_valid _ 0 _ _ (by omega)

theorem cellExpression_gateCount (machine : TM0.Machine Symbol State) (tag : CellTemplateTag Symbol State) :
    (cellExpression machine tag).gateCount = cellBlockSize Symbol State := by
  have first := Expression.truthTable_gateCount (3 * cellWidth Symbol State) 0 (fixedCellTable machine tag)
  have second := Expression.truthTable_gateCount (3 * cellWidth Symbol State) 0 (fun _ => false)
  change (Expression.truthTable (3 * cellWidth Symbol State) 0 (fixedCellTable machine tag)).gateCount = (Expression.truthTable (3 * cellWidth Symbol State) 0 (fun _ => false)).gateCount
  omega

omit [Inhabited Symbol] [Inhabited State] in
theorem cellBlockSize_positive : 0 < cellBlockSize Symbol State := by
  have count := Expression.truthTable_gateCount (3 * cellWidth Symbol State) 0 (fun _ => false)
  have power : 1 ≤ 2 ^ (3 * cellWidth Symbol State) := Nat.one_le_pow _ _ (by decide)
  change 0 < (Expression.truthTable (3 * cellWidth Symbol State) 0 (fun _ => false)).gateCount
  omega

/-- The finite template selected at a mathematical window coordinate. -/
noncomputable def cellTemplateAt (radius : ℕ)
    (output : Fin ((2 * radius + 1) * cellWidth Symbol State)) : CellTemplateTag Symbol State := by
  classical
  exact ((decide ((finProdFinEquiv.symm output).1.val = 0),
    decide ((finProdFinEquiv.symm output).1.val = 2 * radius)), (finProdFinEquiv.symm output).2)

theorem cellTemplateAt_table (machine : TM0.Machine Symbol State) (radius : ℕ)
    (output : Fin ((2 * radius + 1) * cellWidth Symbol State)) :
    cellTables (2 * radius + 1) (windowUpdate machine radius) output =
      fixedCellTable machine (cellTemplateAt radius output) := by
  classical
  funext bits
  simp [cellTables, windowUpdate, fixedCellTable, cellTemplateAt]

/-- The existing local-expression compiler selects exactly this finite
template and renames its fixed input positions to neighboring cell bits. -/
theorem localCellExpression_eq (machine : TM0.Machine Symbol State) (radius : ℕ)
    (output : Fin ((2 * radius + 1) * cellWidth Symbol State)) :
    localExpressions ((2 * radius + 1) * cellWidth Symbol State) (3 * cellWidth Symbol State)
        (cellSources (2 * radius + 1) (windowNeighbors radius))
        (cellTables (2 * radius + 1) (windowUpdate machine radius)) output =
      (cellExpression machine (cellTemplateAt radius output)).rename
        (layerNames (fun argument => (cellSources (2 * radius + 1) (windowNeighbors radius) output argument).val)) := by
  simp only [localExpressions, cellTemplateAt_table, cellExpression]
  rfl

/-- Fixed gate data for all boundary/bit choices, using a common finite
reference type and a common number of gates. -/
noncomputable def cellTemplateProgram (machine : TM0.Machine Symbol State)
    (choice : Fin (Fintype.card (CellTemplateTag Symbol State)))
    (slot : Fin (cellBlockSize Symbol State)) :
    Bool ⊕ (Fin (3 * cellWidth Symbol State + cellBlockSize Symbol State) ×
      Fin (3 * cellWidth Symbol State + cellBlockSize Symbol State)) :=
  let tag := (Fintype.equivFin (CellTemplateTag Symbol State)).symm choice
  let equal := cellExpression_gateCount machine tag
  let gate := (cellExpression machine tag).gateTemplates (cellExpression_valid machine tag)
    (slot.cast equal.symm)
  gate.map id (fun pair =>
    (pair.1.cast (congrArg (fun count => 3 * cellWidth Symbol State + count) equal),
      pair.2.cast (congrArg (fun count => 3 * cellWidth Symbol State + count) equal)))

/-- The finite template table contains exactly the canonical compiler's gates;
the cardinality casts change no wire number. -/
theorem cellTemplateProgram_value (machine : TM0.Machine Symbol State)
    (choice : Fin (Fintype.card (CellTemplateTag Symbol State))) (slot : Fin (cellBlockSize Symbol State)) :
    gateValue (cellTemplateProgram machine choice slot) =
      ((cellExpression machine ((Fintype.equivFin (CellTemplateTag Symbol State)).symm choice)).compile
        (3 * cellWidth Symbol State)).1[slot.val]'(by
          rw [Expression.compile_length, cellExpression_gateCount]
          exact slot.isLt) := by
  simp only [cellTemplateProgram, gateValue_cast, Expression.gateTemplates, gateValue_boundGate]
  rfl

/-- Emit one local transition block chosen from the fixed machine table.
Runtime arguments supply ordinary bounded wire coordinates and a finite tag. -/
noncomputable def emitCellProgram {Parameter : Type} [Fintype Parameter]
    (machine : TM0.Machine Symbol State) (wires : MvPolynomial Parameter ℕ) :
    Computation Parameter (Fin (3 * cellWidth Symbol State + cellBlockSize Symbol State) ⊕ Unit) :=
  instantiateProgramChoice wires (cellTemplateProgram machine)

theorem emitCellProgram_realizable {Parameter : Type} [Fintype Parameter]
    (machine : TM0.Machine Symbol State) (wires : MvPolynomial Parameter ℕ) :
    (emitCellProgram machine wires).Realizable :=
  instantiateProgramChoice_realizable wires (cellTemplateProgram machine)

theorem emitCellProgram_value {Parameter : Type} [Fintype Parameter]
    (machine : TM0.Machine Symbol State) (wires : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (choice : Fin (Fintype.card (CellTemplateTag Symbol State)))
    (coordinates : Fin (3 * cellWidth Symbol State + cellBlockSize Symbol State) → Fin (MvPolynomial.eval sizes wires)) :
    List.ofFn (fun index => gateValue ((emitCellProgram machine wires).compute sizes
      ⟨(fun name => match name with | .inl port => coordinates port | .inr _ => choice), trivial⟩ index)) =
      ((cellExpression machine ((Fintype.equivFin (CellTemplateTag Symbol State)).symm choice)).compile
        (3 * cellWidth Symbol State)).1.map (Gate.rename (layerNames (fun index => (coordinates index).val))) := by
  change List.ofFn (fun index => gateValue ((instantiateProgram wires (cellTemplateProgram machine choice)).compute
    sizes ⟨coordinates, trivial⟩ index)) = _
  rw [instantiateProgram_value]
  apply congrArg (List.map (Gate.rename (layerNames (fun index => (coordinates index).val))))
  apply List.ext_getElem
  · simp [Expression.compile_length, cellExpression_gateCount]
  · intro index firstBound secondBound
    simp only [List.getElem_ofFn, cellTemplateProgram_value]

/-- Prepare the fresh offsets internally and emit the selected local block
at its runtime base. The first argument family contains base and input wires;
the final argument is the specialization-fixed boundary/bit tag. -/
noncomputable def emitCellProgramAt {Parameter : Type} [Fintype Parameter]
    (machine : TM0.Machine Symbol State) (wires : MvPolynomial Parameter ℕ) :
    Computation Parameter ((Unit ⊕ Fin (3 * cellWidth Symbol State)) ⊕ Unit) :=
  (emitCellProgram machine wires).onResults
    (Sum.elim (fun _ => arrayPosition wires)
      (fun _ => templateTagDomain (Fintype.card (CellTemplateTag Symbol State))))
    (fun sizes arguments => (arguments (.inl (.inl ()))).val + cellBlockSize Symbol State ≤
      MvPolynomial.eval sizes wires)
    (fun name _ arguments => match name with
      | .inl port => Expression.templateCoordinates (arguments.val (.inl (.inl ())))
          (fun index => arguments.val (.inl (.inr index))) arguments.property port
      | .inr _ => arguments.val (.inr ())) (by intros; trivial)

theorem emitCellProgramAt_realizable {Parameter : Type} [Fintype Parameter]
    (machine : TM0.Machine Symbol State) (wires : MvPolynomial Parameter ℕ) :
    (emitCellProgramAt machine wires).Realizable := by
  unfold emitCellProgramAt
  apply (emitCellProgram_realizable machine wires).onResults
  intro name
  dsimp only [emitCellProgram, instantiateProgramChoice]
  cases name with
  | inl port =>
    have prepared := (Expression.templateCoordinates_realizable (3 * cellWidth Symbol State)
      (cellBlockSize Symbol State) wires port).withArguments
      (Sum.elim (fun _ : Unit ⊕ Fin (3 * cellWidth Symbol State) => arrayPosition wires)
        (fun _ : Unit => templateTagDomain (Fintype.card (CellTemplateTag Symbol State))))
      ⟨Sum.inl, Sum.inl_injective⟩ (fun _ => rfl)
    exact prepared.withSpecification _ _ (by intros; assumption) (by intros; rfl)
  | inr singleton =>
    cases singleton
    exact Realizable.argument _ (Sum.inr () : (Unit ⊕ Fin (3 * cellWidth Symbol State)) ⊕ Unit) _

/-- The certified, tagged machine block has exactly the gate list of its
selected local expression at the supplied runtime base and neighbor wires. -/
theorem emitCellProgramAt_value {Parameter : Type} [Fintype Parameter]
    (machine : TM0.Machine Symbol State) (wires : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (choice : Fin (Fintype.card (CellTemplateTag Symbol State)))
    (base : Fin (MvPolynomial.eval sizes wires))
    (inputs : Fin (3 * cellWidth Symbol State) → Fin (MvPolynomial.eval sizes wires))
    (fits : base.val + cellBlockSize Symbol State ≤ MvPolynomial.eval sizes wires) :
    List.ofFn (fun index => gateValue ((emitCellProgramAt machine wires).compute sizes
      ⟨(fun name => match name with
        | .inl (.inl _) => base | .inl (.inr input) => inputs input | .inr _ => choice), fits⟩ index)) =
      (((cellExpression machine ((Fintype.equivFin (CellTemplateTag Symbol State)).symm choice)).rename
        (layerNames (fun index => (inputs index).val))).compile base.val).1 := by
  let coordinates := Expression.templateCoordinates base inputs fits
  change List.ofFn (fun index => gateValue ((emitCellProgram machine wires).compute sizes
    ⟨(fun name => match name with | .inl port => coordinates port | .inr _ => choice), trivial⟩ index)) = _
  rw [emitCellProgram_value]
  rw [Expression.templateCoordinates_rename base inputs fits _ (by
    intro gate member
    simpa only [Expression.compile_length, cellExpression_gateCount] using
      (Expression.compile_valid (cellExpression_valid machine _)).1.gates_valid gate member)]
  have relocated := congrArg Prod.fst
    (Expression.compile_relocate (cellExpression_valid machine
      ((Fintype.equivFin (CellTemplateTag Symbol State)).symm choice)) base.val 0
      (fun index => (inputs index).val))
  simpa only [Nat.add_zero] using relocated.symm

end Polytime2.Complexity.CookLevin
