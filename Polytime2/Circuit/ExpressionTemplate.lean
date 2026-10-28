import Polytime2.Circuit.Construction
import Polytime2.Circuit.TemplateRelocation
import Polytime2.Circuit.WireArithmetic

/-! # Certified emission of precompiled expression templates

Compile each fixed expression once into finite template data. The runtime
emitter substitutes supplied wire coordinates into that data, using the
existing record constructor. The value theorem identifies its complete gate
list with ordinary renaming of the original mathematical compiler's output.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Circuit.Expression

open EncodedDomain Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

/-- The finite gate data of a precompiled expression, with all references
bounded by the expression's input count plus its exact gate count. -/
def gateTemplates (expression : Expression) {source : ℕ} (valid : expression.Valid source) :
    Fin expression.gateCount → Bool ⊕ (Fin (source + expression.gateCount) × Fin (source + expression.gateCount)) :=
  fun index =>
    let program := (expression.compile source).1
    let slot : Fin program.length := ⟨index.val, by rw [compile_length]; exact index.isLt⟩
    boundGate (program.get slot) (by
      have bounded := (compile_valid valid).1.gates_valid (program.get slot) (List.get_mem _ slot)
      simpa only [compile_length] using bounded)

/-- Runtime emission of a fixed expression template. All input and fresh
wire coordinates are supplied as an ordinary fixed finite argument family. -/
noncomputable def emitTemplate (expression : Expression) {source : ℕ} (valid : expression.Valid source)
    (wires : MvPolynomial Parameter ℕ) : Computation Parameter (Fin (source + expression.gateCount)) :=
  instantiateProgram wires (expression.gateTemplates valid)

theorem emitTemplate_realizable (expression : Expression) {source : ℕ} (valid : expression.Valid source)
    (wires : MvPolynomial Parameter ℕ) : (expression.emitTemplate valid wires).Realizable :=
  instantiateProgram_realizable wires (expression.gateTemplates valid)

theorem emitTemplate_value (expression : Expression) {source : ℕ} (valid : expression.Valid source)
    (wires : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (coordinates : Fin (source + expression.gateCount) → Fin (MvPolynomial.eval sizes wires)) :
    List.ofFn (fun index => gateValue ((expression.emitTemplate valid wires).compute sizes
      ⟨coordinates, trivial⟩ index)) =
        (expression.compile source).1.map (Gate.rename (layerNames (fun index => (coordinates index).val))) := by
  change List.ofFn (fun index => gateValue ((instantiateProgram wires (expression.gateTemplates valid)).compute
    sizes ⟨coordinates, trivial⟩ index)) = _
  rw [instantiateProgram_value]
  apply congrArg (List.map (Gate.rename (layerNames (fun index => (coordinates index).val))))
  apply List.ext_getElem
  · simp [compile_length]
  · intro index firstBound secondBound
    simp only [List.getElem_ofFn, gateTemplates, gateValue_boundGate]
    rfl

/-- Original input wires followed by consecutive fresh template wires. -/
def templateCoordinates {source count wires : ℕ} (base : Fin wires) (inputs : Fin source → Fin wires)
    (fits : base.val + count ≤ wires) : Fin (source + count) → Fin wires :=
  fun port => if original : port.val < source then inputs ⟨port.val, original⟩
    else ⟨base.val + (port.val - source), by have bounded := port.isLt; omega⟩

/-- Emit a precompiled expression at a runtime base wire. The caller provides
the original input wires; fixed template offsets are prepared internally. -/
noncomputable def emitTemplateAt (expression : Expression) {source : ℕ} (valid : expression.Valid source)
    (wires : MvPolynomial Parameter ℕ) : Computation Parameter (Unit ⊕ Fin source) :=
  (expression.emitTemplate valid wires).onResults (fun _ => arrayPosition wires)
    (fun sizes arguments => (arguments (.inl ())).val + expression.gateCount ≤ MvPolynomial.eval sizes wires)
    (fun port _ arguments => templateCoordinates (arguments.val (.inl ()))
      (fun index => arguments.val (.inr index)) arguments.property port) (by intros; trivial)

/-- Prepare one coordinate of a fixed template from its runtime base and
original input wires. Shared by fixed and runtime-selected templates. -/
theorem templateCoordinates_realizable (source count : ℕ) (wires : MvPolynomial Parameter ℕ)
    (port : Fin (source + count)) :
    (Computation.mk (fun _ : Unit ⊕ Fin source => arrayPosition wires) (arrayPosition wires)
      (fun sizes arguments => (arguments (.inl ())).val + count ≤ MvPolynomial.eval sizes wires)
      (fun _ arguments => templateCoordinates (arguments.val (.inl ()))
        (fun index => arguments.val (.inr index)) arguments.property port)).Realizable := by
  by_cases original : port.val < source
  · simpa only [templateCoordinates, dite_eq_left original] using
      Realizable.argument (fun _ : Unit ⊕ Fin source => arrayPosition wires) (.inr ⟨port.val, original⟩)
        (fun sizes arguments => (arguments (.inl ())).val + count ≤ MvPolynomial.eval sizes wires)
  · have selected := (wireShift_realizable wires (port.val - source)).withArguments
      (fun _ : Unit ⊕ Fin source => arrayPosition wires)
      ⟨(fun _ => .inl ()), by intro a b equal; cases a; cases b; rfl⟩ (fun _ => rfl)
    have ready := selected.withPrecondition
      (fun sizes arguments => (arguments (.inl ())).val + count ≤ MvPolynomial.eval sizes wires)
      (by
        intro sizes arguments fits
        change (arguments (.inl ())).val + (port.val - source) < MvPolynomial.eval sizes wires
        have bounded := port.isLt
        omega)
    apply ready.withSpecification _ _ (by intros; assumption)
    intro sizes arguments fits
    simp only [templateCoordinates, dite_eq_right original]
    rfl

theorem emitTemplateAt_realizable (expression : Expression) {source : ℕ} (valid : expression.Valid source)
    (wires : MvPolynomial Parameter ℕ) : (expression.emitTemplateAt valid wires).Realizable := by
  unfold emitTemplateAt
  apply (expression.emitTemplate_realizable valid wires).onResults
  intro port
  exact templateCoordinates_realizable source expression.gateCount wires port

/-- Substitution of prepared coordinates is ordinary relocation on every
bounded template gate. The selected program need not be rebuilt. -/
theorem templateCoordinates_rename {source count wires : ℕ} (base : Fin wires)
    (inputs : Fin source → Fin wires) (fits : base.val + count ≤ wires) (program : List Gate)
    (bounded : ∀ gate ∈ program, gate.Valid (source + count)) :
    program.map (Gate.rename (layerNames (fun index => (templateCoordinates base inputs fits index).val))) =
      program.map (Gate.rename (spliceNames source base.val (fun index => (inputs index).val))) := by
  have agree : ∀ wire < source + count,
      layerNames (fun index => (templateCoordinates base inputs fits index).val) wire =
        spliceNames source base.val (fun index => (inputs index).val) wire := by
    intro wire within
    by_cases original : wire < source <;>
      simp [layerNames, templateCoordinates, spliceNames, within, original]
  apply List.map_congr_left
  intro gate member
  have within := bounded gate member
  cases gate with
  | inl value => rfl
  | inr pair => exact congrArg Sum.inr (Prod.ext (agree pair.1 within.1) (agree pair.2 within.2))

/-- Certified template emission produces exactly the original expression
compiler's gates at the requested base and input wires. -/
theorem emitTemplateAt_value (expression : Expression) {source : ℕ} (valid : expression.Valid source)
    (wires : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (base : Fin (MvPolynomial.eval sizes wires))
    (inputs : Fin source → Fin (MvPolynomial.eval sizes wires))
    (fits : base.val + expression.gateCount ≤ MvPolynomial.eval sizes wires) :
    List.ofFn (fun index => gateValue ((expression.emitTemplateAt valid wires).compute sizes
      ⟨Sum.elim (fun _ : Unit => base) inputs, fits⟩ index)) =
        ((expression.rename (layerNames (fun index => (inputs index).val))).compile base.val).1 := by
  let coordinates := templateCoordinates base inputs fits
  change List.ofFn (fun index => gateValue ((expression.emitTemplate valid wires).compute sizes
    ⟨coordinates, trivial⟩ index)) = _
  rw [emitTemplate_value]
  rw [templateCoordinates_rename base inputs fits (expression.compile source).1 (by
    intro gate member
    simpa only [compile_length] using (compile_valid valid).1.gates_valid gate member)]
  have relocated := congrArg Prod.fst (compile_relocate valid base.val 0 (fun index => (inputs index).val))
  simpa only [Nat.add_zero] using relocated.symm

end Polytime2.Circuit.Expression
