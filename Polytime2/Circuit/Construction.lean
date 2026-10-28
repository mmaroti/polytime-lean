import Polytime2.Circuit.Compose
import Polytime2.Arrays.Indices
import Polytime2.Computation.Sums
import Polytime2.Computation.RecordArguments
import Polytime2.Arithmetic.BitComparison

/-! # Certified substitution of fixed gate templates

A fixed NAND template reads a finite family of mathematical wire coordinates
and produces a gate on those coordinates. Constants read no coordinates.
The coordinate bound is a polynomial; all arithmetic constructing those
coordinates is supplied by the caller. The existing product and sum codecs
give the canonical gate encoding, without a new machine or tape convention.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Circuit

open EncodedDomain Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

/-- Boolean constants or NAND pairs, with ordinary bounded wire coordinates. -/
noncomputable def gateDomain (wires : MvPolynomial Parameter ℕ) : EncodedDomain Parameter :=
  booleans.sum ((arrayPosition wires).prod (arrayPosition wires))

/-- Canonical gate array paired with its actual selected output wire. -/
noncomputable def networkDomain (inputs count : MvPolynomial Parameter ℕ) : EncodedDomain Parameter :=
  ((gateDomain (inputs + count)).arrayOfLength count).prod (arrayPosition (inputs + count))

/-- Forget only the bounds on the mathematical wire coordinates. -/
def gateValue {wires : ℕ} (gate : Bool ⊕ (Fin wires × Fin wires)) : Gate :=
  gate.map id (fun pair => (pair.1.val, pair.2.val))

/-- Forgetting established finite bounds loses no gate information. -/
theorem gateValue_injective {wires : ℕ} : Function.Injective (gateValue (wires := wires)) := by
  apply Function.Injective.sumMap Function.injective_id
  intro first second equal
  exact Prod.ext (Fin.ext (congrArg Prod.fst equal)) (Fin.ext (congrArg Prod.snd equal))

/-- Observe a bounded gate array and output coordinate as an ordinary network. -/
def programValue {count wires : ℕ}
    (program : (Fin count → Bool ⊕ (Fin wires × Fin wires)) × Fin wires) : Network :=
  (List.ofFn (fun index => gateValue (program.1 index)), program.2.val)

theorem programValue_injective {count wires : ℕ} : Function.Injective (@programValue count wires) := by
  intro first second equal
  apply Prod.ext
  · funext index
    apply gateValue_injective
    exact congrFun (List.ofFn_injective (congrArg Prod.fst equal)) index
  · exact Fin.ext (congrArg Prod.snd equal)

/-- Changing only a proven wire-bound polynomial equality preserves the network. -/
theorem programValue_transport (sizes : Parameter → ℕ) (source target count : MvPolynomial Parameter ℕ) (equal : source = target)
    (program : (((gateDomain source).arrayOfLength count).prod (arrayPosition source)).Carrier sizes) :
    programValue ((congrArg (fun bound => ((gateDomain bound).arrayOfLength count).prod (arrayPosition bound)) equal) ▸ program) =
      programValue program := by
  cases equal
  rfl

/-- Attach an established mathematical wire bound to a gate. -/
def boundGate {wires : ℕ} (gate : Gate) (valid : gate.Valid wires) : Bool ⊕ (Fin wires × Fin wires) :=
  match gate with
  | .inl value => .inl value
  | .inr pair => .inr (⟨pair.1, valid.1⟩, ⟨pair.2, valid.2⟩)

theorem gateValue_boundGate {wires : ℕ} (gate : Gate) (valid : gate.Valid wires) :
    gateValue (boundGate gate valid) = gate := by
  cases gate <;> rfl

theorem gateValue_cast {source target : ℕ} (equal : source = target)
    (gate : Bool ⊕ (Fin source × Fin source)) :
    gateValue (gate.map id (fun pair => (pair.1.cast equal, pair.2.cast equal))) = gateValue gate := by
  cases gate <;> rfl

/-- Instantiate one specialization-fixed template. The actual input wire
coordinates vary with runtime sizes and with preceding constructor stages. -/
noncomputable def instantiateGate (wires : MvPolynomial Parameter ℕ) {arity : ℕ}
    (template : Bool ⊕ (Fin arity × Fin arity)) : Computation Parameter (Fin arity) where
  inputDomains _ := arrayPosition wires
  outputDomain := gateDomain wires
  precondition _ _ := True
  compute _ arguments := template.map id (fun pair => (arguments.val pair.1, arguments.val pair.2))

theorem instantiateGate_realizable (wires : MvPolynomial Parameter ℕ) {arity : ℕ}
    (template : Bool ⊕ (Fin arity × Fin arity)) : (instantiateGate wires template).Realizable := by
  let inputs : Fin arity → EncodedDomain Parameter := fun _ => arrayPosition wires
  cases template with
  | inl value =>
    have prepared := (booleanOperation_realizable (Parameter := Parameter) (Argument := Empty) (fun _ => value)).onResults
      inputs (fun _ _ => True) (fun empty => nomatch empty)
      (by intros; trivial) (fun empty => nomatch empty)
    have injected := prepared.followedBy
      (sumInl_realizable booleans ((arrayPosition wires).prod (arrayPosition wires))) rfl (by intros; trivial)
    exact injected.withSpecification (fun _ _ => True) (instantiateGate wires (.inl value)).compute
      (by intros; trivial) (by intros; rfl)
  | inr pair =>
    have first := Realizable.argument inputs pair.1 (fun _ _ => True)
    have second := Realizable.argument inputs pair.2 (fun _ _ => True)
    have collected := first.prodMk second
    have injected := collected.followedBy
      (sumInr_realizable booleans ((arrayPosition wires).prod (arrayPosition wires))) rfl (by intros; trivial)
    exact injected.withSpecification (fun _ _ => True) (instantiateGate wires (.inr pair)).compute
      (by intros; trivial) (by intros; rfl)

/-- Emit all gates of a fixed finite program using the same runtime wire
coordinates. The result is the ordinary finite family of instantiated gates. -/
noncomputable def instantiateProgram (wires : MvPolynomial Parameter ℕ) {arity count : ℕ}
    (templates : Fin count → Bool ⊕ (Fin arity × Fin arity)) : Computation Parameter (Fin arity) where
  inputDomains _ := arrayPosition wires
  outputDomain := EncodedDomain.record count (fun _ => gateDomain wires)
  precondition _ _ := True
  compute _ arguments := fun index =>
    (templates index).map id (fun pair => (arguments.val pair.1, arguments.val pair.2))

theorem instantiateProgram_realizable (wires : MvPolynomial Parameter ℕ) {arity count : ℕ}
    (templates : Fin count → Bool ⊕ (Fin arity × Fin arity)) :
    (instantiateProgram wires templates).Realizable :=
  Realizable.recordOutputs (fun _ : Fin arity => arrayPosition wires) count (fun _ => gateDomain wires)
    (fun _ _ => True) (fun index => (instantiateGate wires (templates index)).compute)
    (fun index => instantiateGate_realizable wires (templates index))

/-- Gate substitution agrees with ordinary renaming of natural wire numbers. -/
theorem instantiateGate_value (wires : MvPolynomial Parameter ℕ) {arity : ℕ}
    (template : Bool ⊕ (Fin arity × Fin arity)) (sizes : Parameter → ℕ)
    (arguments : Fin arity → Fin (MvPolynomial.eval sizes wires)) :
    gateValue ((instantiateGate wires template).compute sizes ⟨arguments, trivial⟩) =
      (gateValue template).rename
        (fun wire => if bounded : wire < arity then (arguments ⟨wire, bounded⟩).val else 0) := by
  cases template with
  | inl value => rfl
  | inr pair => simp [instantiateGate, gateValue, Gate.rename, pair.1.isLt, pair.2.isLt]

/-- The emitted finite program is exactly a renaming of its template gates. -/
theorem instantiateProgram_value (wires : MvPolynomial Parameter ℕ) {arity count : ℕ}
    (templates : Fin count → Bool ⊕ (Fin arity × Fin arity)) (sizes : Parameter → ℕ)
    (coordinates : Fin arity → Fin (MvPolynomial.eval sizes wires)) :
    List.ofFn (fun index => gateValue ((instantiateProgram wires templates).compute sizes
      ⟨coordinates, trivial⟩ index)) =
        (List.ofFn (fun index => gateValue (templates index))).map
          (Gate.rename (layerNames (fun index => (coordinates index).val))) := by
  apply List.ext_getElem
  · simp
  · intro index firstBound secondBound
    simp only [List.getElem_ofFn, List.getElem_map]
    exact instantiateGate_value wires (templates ⟨index, by simpa using firstBound⟩) sizes coordinates

end Polytime2.Circuit
