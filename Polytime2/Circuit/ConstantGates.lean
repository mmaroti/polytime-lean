import Polytime2.Circuit.Construction
import Polytime2.Arrays.FlattenRecords

/-! # The two constant gates used by input wiring -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Circuit

open EncodedDomain Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

/-- Emit false, then true, in exactly the order of `wiringLayer`. -/
noncomputable def twoConstantGates (wires : MvPolynomial Parameter ℕ) : Computation Parameter Empty :=
  ((instantiateProgram wires (![.inl false, .inl true] : Fin 2 → Bool ⊕ (Fin 0 × Fin 0))).onResults
    Empty.elim (fun _ _ => True) (fun port => Fin.elim0 port) (by intros; trivial)).followedBy
    (recordToArray (gateDomain wires) 2) rfl (by intros; trivial)

theorem twoConstantGates_realizable (wires : MvPolynomial Parameter ℕ) :
    (twoConstantGates wires).Realizable := by
  have fixed := (instantiateProgram_realizable wires
    (![.inl false, .inl true] : Fin 2 → Bool ⊕ (Fin 0 × Fin 0))).onResults
      Empty.elim (fun _ _ => True) (fun port => Fin.elim0 port) (by intros; trivial) (fun port => Fin.elim0 port)
  exact fixed.followedBy (recordToArray_realizable (gateDomain wires) 2) rfl (by intros; trivial)

theorem twoConstantGates_value (wires : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (twoConstantGates wires).Arguments sizes // True}) :
    List.ofFn (fun index => gateValue ((twoConstantGates wires).compute sizes arguments index)) =
      [.inl false, .inl true] := by
  simp only [twoConstantGates, followedBy]
  rw [List.ofFn_comp' _ gateValue, recordToArray_list]
  simp [onResults, instantiateProgram, gateValue, List.map_ofFn, List.ofFn_succ]

end Polytime2.Circuit
