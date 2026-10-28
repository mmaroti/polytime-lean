import Polytime2.Circuit.Compose

/-! # Input wiring with Boolean constants

A prepared circuit input can be a source bit or a constant. Two constant
gates suffice for any number of prepared inputs, with no duplication of input
bits. This is the initial-word wiring used before bounded TM0 simulation.
-/

namespace Polytime2.Circuit

def wiringLayer {width : ℕ} (inputs : ℕ) (choices : Fin width → Bool ⊕ Fin inputs) : Layer width :=
  ([.inl false, .inl true], fun index => match choices index with
    | .inl value => inputs + if value then 1 else 0
    | .inr source => source.val)

theorem wiringLayer_valid {width : ℕ} (inputs : ℕ) (choices : Fin width → Bool ⊕ Fin inputs) :
    WellFormed inputs (wiringLayer inputs choices).1 ∧
      ∀ index, (wiringLayer inputs choices).2 index < inputs + (wiringLayer inputs choices).1.length := by
  refine ⟨⟨trivial, ⟨trivial, trivial⟩⟩, ?_⟩
  intro index
  cases choice : choices index with
  | inl value => cases value <;> simp [wiringLayer, choice]
  | inr source => simpa [wiringLayer, choice] using Nat.lt_trans source.isLt (by omega)

theorem wiringLayer_correct {width : ℕ} (inputs : ℕ) (choices : Fin width → Bool ⊕ Fin inputs)
    (assignment : Fin inputs → Bool) (index : Fin width) :
    run inputs (wiringLayer inputs choices).1 (inputValues assignment)
      ((wiringLayer inputs choices).2 index) =
      match choices index with
      | .inl value => value
      | .inr source => assignment source := by
  cases choice : choices index with
  | inl value => cases value <;> simp [wiringLayer, choice, run, Gate.eval]
  | inr source => simp [wiringLayer, choice, run, Gate.eval, inputValues,
      Function.update_of_ne (Nat.ne_of_lt source.isLt),
      Function.update_of_ne (show source.val ≠ inputs + 1 by omega), source.isLt]

end Polytime2.Circuit
