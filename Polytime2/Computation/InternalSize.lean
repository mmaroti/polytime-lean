/-
Copyright (c) 2026 Miklos Maroti <mmaroti@math.u-szeged.hu>
SPDX-License-Identifier: Apache-2.0

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Polytime2.Computation.Realizable
import Polytime2.StandardUnarySum

/-! # Hiding a counter-capacity size behind two public dimensions

A certified call uses the internal assignment `[K + L + 1, K, L]`. The new
capacity header is constructed at runtime in private storage, and polynomial
bounds are substituted at the unchanged public assignment.
-/

namespace Polytime2

namespace Computation.Realizable.Internal

open MultiTape CallingConvention

/-- The first source size is private; the other two remain independent. -/
def internalSizes (sizes : Fin 2 → ℕ) : Fin 3 → ℕ :=
  ![sizes 0 + sizes 1 + 1, sizes 0, sizes 1]

noncomputable def internalPolynomials : Fin 3 → MvPolynomial (Fin 2) ℕ :=
  ![MvPolynomial.X 0 + MvPolynomial.X 1 + 1, MvPolynomial.X 0, MvPolynomial.X 1]

noncomputable def internalBound (bound : MvPolynomial (Fin 3) ℕ) :
    MvPolynomial (Fin 2) ℕ := MvPolynomial.eval₂Hom MvPolynomial.C internalPolynomials bound

theorem internalBound_eval (bound : MvPolynomial (Fin 3) ℕ) (sizes : Fin 2 → ℕ) :
    MvPolynomial.eval sizes (internalBound bound) = MvPolynomial.eval (internalSizes sizes) bound := by
  induction bound using MvPolynomial.induction_on with
  | C value => simp [internalBound]
  | add left right leftEqual rightEqual => simpa [internalBound] using congrArg₂ (· + ·) leftEqual rightEqual
  | mul_X value parameter equality =>
    have parameterEqual : MvPolynomial.eval sizes (internalPolynomials parameter) = internalSizes sizes parameter := by
      fin_cases parameter <;> simp [internalPolynomials, internalSizes]
    simpa [internalBound, parameterEqual] using congrArg (· * internalSizes sizes parameter) equality

end Computation.Realizable.Internal

namespace EncodedDomain

-- carrierLevel: mathematical values in the original and specialized domains.
universe carrierLevel

/-- Substitute the private capacity while retaining the original encoded bits. -/
noncomputable def withInternalSize (domain : EncodedDomain.{0, carrierLevel} (Fin 3)) :
    EncodedDomain (Fin 2) where
  Carrier sizes := domain.Carrier (Computation.Realizable.Internal.internalSizes sizes)
  width sizes := domain.width (Computation.Realizable.Internal.internalSizes sizes)
  encode sizes := domain.encode (Computation.Realizable.Internal.internalSizes sizes)
  decode sizes := domain.decode (Computation.Realizable.Internal.internalSizes sizes)
  decode_encode sizes := domain.decode_encode (Computation.Realizable.Internal.internalSizes sizes)
  encode_decode sizes := domain.encode_decode (Computation.Realizable.Internal.internalSizes sizes)
  polynomial_width := by
    obtain ⟨bound, bounded⟩ := domain.polynomial_width
    exact ⟨Computation.Realizable.Internal.internalBound bound, fun sizes => by
      rw [Computation.Realizable.Internal.internalBound_eval]; exact bounded _⟩

end EncodedDomain

namespace Computation

open MultiTape CallingConvention Realizable.Internal

universe carrierLevel
variable {InputName : Type} [Fintype InputName]

/-- Replace a caller-supplied counter capacity with a certified private size.
The two public sizes are the original row and column dimensions. -/
noncomputable def withInternalSize (computation : Computation.{carrierLevel} (Fin 3) InputName) :
    Computation (Fin 2) InputName where
  inputDomains name := (computation.inputDomains name).withInternalSize
  outputDomain := computation.outputDomain.withInternalSize
  precondition sizes := computation.precondition (internalSizes sizes)
  compute sizes := computation.compute (internalSizes sizes)

namespace Realizable

/-- The generated unary header, all private storage, and substituted runtime
witnesses stay inside the certificate. Its construction is charged. -/
theorem withInternalSize {computation : Computation.{carrierLevel} (Fin 3) InputName}
    (realizable : computation.Realizable) : computation.withInternalSize.Realizable := by
  classical
  obtain ⟨ScratchName, finiteScratch, scratchDomains, State, finiteStates,
    source, sourceEntry, sourceExit, certificate⟩ := realizable
  let scratchFiniteInstance : Fintype ScratchName := finiteScratch
  let stateFiniteInstance : Fintype State := finiteStates
  let target := computation.withInternalSize
  let scratch : Unit ⊕ ScratchName → EncodedDomain (Fin 2) :=
    Sum.elim (fun _ => (EncodedDomain.unary 0).withInternalSize)
      (fun name => (scratchDomains name).withInternalSize)
  let capacityTape : TapeName target (Unit ⊕ ScratchName) := scratchTape target (.inl ())
  let wiring : TapeName computation ScratchName ↪ TapeName target (Unit ⊕ ScratchName) :=
    ⟨(fun name => match name with
      | .inl 0 => capacityTape
      | .inl 1 => .inl 0
      | .inl 2 => .inl 1
      | .inr (.inl argument) => inputTape target argument
      | .inr (.inr (.inl result)) => outputTape target
      | .inr (.inr (.inr name)) => scratchTape target (.inr name)), by
      intro first second equal
      rcases first with parameter | argument | result | name <;>
        rcases second with parameter' | argument' | result' | name' <;>
        first | (fin_cases parameter <;> fin_cases parameter' <;> simp_all [capacityTape])
              | (fin_cases parameter <;> simp_all [capacityTape])
              | (fin_cases parameter' <;> simp_all [capacityTape])
              | simp_all⟩
  let prepare := StandardUnarySum.machine (.inl 0) (.inl 1) capacityTape (by simp [capacityTape]) (by simp [capacityTape])
  let algorithm := MultiTape.sequence prepare
    (MultiTape.wire (Alphabet := Alphabet (TapeName target (Unit ⊕ ScratchName))) wiring source) sourceEntry
  refine ⟨Unit ⊕ ScratchName, inferInstance, scratch, _, inferInstance,
    algorithm, .inl (.inl (.inl (.inl false))), .inr sourceExit, ?_⟩
  obtain ⟨bound, execute⟩ := Internal.wiredRuns scratchDomains source sourceEntry sourceExit certificate wiring
  refine ⟨(by intro parameter; rfl), (by intro name; rfl), ?_,
    internalBound bound + 3 * (MvPolynomial.X 0 + MvPolynomial.X 1) + 18, ?_⟩
  · intro symbols
    simp [algorithm, MultiTape.sequence, MultiTape.wire, certificate.2.2.1]
  · intro sizes input initial valid represented headers
    let arguments := Internal.arguments target scratch sizes input
    let width := fun name => (Internal.domains target scratch name).width sizes
    let readonly : TapeName target (Unit ⊕ ScratchName) → Bool := Internal.readOnly target
    have capacityWidth : width capacityTape = sizes 0 + sizes 1 + 1 := rfl
    obtain ⟨prepareTicks, prepareCost, prepared⟩ := StandardUnarySum.runs
      (.inl 0) (.inl 1) capacityTape (by simp [capacityTape]) (by simp [capacityTape]) width readonly rfl
      (sizes 0) (sizes 1) capacityWidth initial (headers 0) (headers 1)
      (represented.region capacityTape)
    let middle := Function.update initial capacityTape (unary (sizes 0 + sizes 1 + 1))
    have widths : ∀ name, width (wiring name) =
        (Internal.domains computation scratchDomains name).width (internalSizes sizes) := by
      intro name
      rcases name with parameter | argument | result | name
      · fin_cases parameter <;> rfl
      · rfl
      · rfl
      · rfl
    have immutable : ∀ name, readonly (wiring name) = true → Internal.readOnly computation name = true := by
      intro name premise
      rcases name with parameter | argument | result | name
      · rfl
      · rfl
      · contradiction
      · contradiction
    obtain ⟨sourceTicks, final, sourceCost, trace, correct, _, _⟩ := execute
      (internalSizes sizes) arguments valid width readonly middle widths immutable
      (by
        intro parameter
        fin_cases parameter
        · change middle capacityTape = unary (sizes 0 + sizes 1 + 1)
          exact Function.update_self _ _ _
        · change middle (.inl 0) = unary (sizes 0)
          exact (Function.update_of_ne (show (.inl 0 : TapeName target (Unit ⊕ ScratchName)) ≠ capacityTape by
            dsimp [capacityTape]; simp) _ _).trans (headers 0)
        · change middle (.inl 1) = unary (sizes 1)
          exact (Function.update_of_ne (show (.inl 1 : TapeName target (Unit ⊕ ScratchName)) ≠ capacityTape by
            dsimp [capacityTape]; simp) _ _).trans (headers 1))
      (by
        intro name
        change middle (inputTape target name) =
          encoded (target.inputDomains name) sizes (arguments name)
        exact (Function.update_of_ne (show inputTape target name ≠ capacityTape by
          dsimp [capacityTape]; simp) _ _).trans (represented.1 (inputTape target name) rfl))
      (by intro name; exact prepared.region (wiring name) (represented.region (wiring name)))
    have combined := prepared.sequence (MultiTape.wire wiring source) sourceEntry
      (StandardUnarySum.halt (.inl 0) (.inl 1) capacityTape (by simp [capacityTape]) (by simp [capacityTape])) trace
    refine ⟨prepareTicks + (sourceTicks + 1),
      (fun _ => target.compute sizes ⟨arguments, valid⟩), final, ?_, combined, ⟨valid, rfl⟩, ?_⟩
    · rw [← internalBound_eval bound sizes] at sourceCost
      simp only [map_add, map_mul, map_ofNat, MvPolynomial.eval_X]
      omega
    · intro name; cases name
      exact correct

end Realizable
end Computation
end Polytime2
