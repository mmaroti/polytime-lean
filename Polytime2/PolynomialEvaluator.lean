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

import Polytime2.UnaryPolynomial
import Polytime2.StandardTapeCommands
import Polytime2.Pipeline
import Polytime2.EncodedDomain

/-! # Polynomial-time evaluation of exact width polynomials

Runtime sizes are immutable unary words, one per parameter. Private tapes and
the result tape may initially contain arbitrary symbols in their regions. A
fixed finite machine prepares its own variable-occurrence copies, evaluates the specialized polynomial, and
returns its unary value with the result head restored. No encoded output
domain or separately supplied runtime capacity is needed.
-/

namespace Polytime2.PolynomialEvaluator

open MultiTape CallingConvention
open Binary (Symbol word)

noncomputable section Evaluation

variable {Parameter : Type}

/-- Public size tapes, private occurrence tapes, and the sole result tape. -/
abbrev TapeName (Parameter Scratch : Type) := Parameter ⊕ (Scratch ⊕ Unit)

/-- Canonical unary size inputs and arbitrary private buffer contents. -/
def initial {Scratch : Type} (sizes : Parameter → ℕ)
    (contents : Scratch ⊕ Unit → List Symbol := fun _ => []) : Tapes (CallingConvention.Alphabet (TapeName Parameter Scratch))
  | .inl parameter => unary (sizes parameter)
  | .inr name => buffer (contents name)

/-- Only the result is public; occurrence copies remain private. -/
def result {Scratch : Type} (role : Scratch → Parameter) (sizes : Parameter → ℕ)
    (value : ℕ) : Tapes (CallingConvention.Alphabet (TapeName Parameter Scratch))
  | .inl parameter => unary (sizes parameter)
  | .inr (.inl scratch) => unary (sizes (role scratch))
  | .inr (.inr _) => unary value

/-- Exact private occurrence capacities and the unary result capacity. -/
def widths {Scratch : Type} (role : Scratch → Parameter) (sizes : Parameter → ℕ)
    (value : ℕ) : TapeName Parameter Scratch → ℕ
  | .inl parameter => sizes parameter
  | .inr (.inl scratch) => sizes (role scratch)
  | .inr (.inr _) => value

/-- External size inputs are immutable; all private storage is writable. -/
def readOnly {Scratch : Type} : TapeName Parameter Scratch → Bool
  | .inl _ => true
  | .inr _ => false

/-- A finite unary evaluator with hidden private tapes and polynomial runtime. -/
def Computable [Fintype Parameter] (width : (Parameter → ℕ) → ℕ) : Prop :=
  ∃ (Scratch : Type) (_ : Fintype Scratch) (role : Scratch → Parameter)
    (State : Type) (_ : Fintype State)
    (machine : Machine (CallingConvention.Alphabet (TapeName Parameter Scratch)) State)
    (entry exit : State) (bound : MvPolynomial Parameter ℕ),
    (∀ symbols, machine exit symbols = none) ∧
    ∀ sizes tapes, (∀ parameter, tapes (.inl parameter) = unary (sizes parameter)) →
      (∀ name, Region (widths role sizes (width sizes) name) 0 (tapes name)) →
      ∃ ticks, ticks ≤ MvPolynomial.eval sizes bound ∧
      Runs (widths role sizes (width sizes)) readOnly machine ticks
        entry (fun _ => 0) tapes exit (fun _ => 0) (result role sizes (width sizes))

private def ready {Scratch : Type} (role : Scratch → Parameter) (sizes : Parameter → ℕ)
    (written : ℕ) (contents : List Symbol := []) : Tapes (CallingConvention.Alphabet (TapeName Parameter Scratch))
  | .inl parameter => unary (sizes parameter)
  | .inr (.inl scratch) => unary (sizes (role scratch))
  | .inr (.inr _) => UnaryPolynomial.tail written contents

private def preparing {Scratch : Type} {count : ℕ} (enumeration : Fin count ≃ Scratch)
    (role : Scratch → Parameter) (sizes : Parameter → ℕ) (stage : ℕ)
    (contents : Scratch ⊕ Unit → List Symbol) :
    Tapes (CallingConvention.Alphabet (TapeName Parameter Scratch))
  | .inl parameter => unary (sizes parameter)
  | .inr (.inl scratch) =>
    if (enumeration.symm scratch).val < stage then unary (sizes (role scratch)) else buffer (contents (.inl scratch))
  | .inr (.inr _) => buffer (contents (.inr ()))

private def copySize {Scratch : Type} (role : Scratch → Parameter) (scratch : Scratch) :
    Machine (CallingConvention.Alphabet (TapeName Parameter Scratch)) (Fin 3) :=
  StandardTapeCommands.copy (.inl (role scratch)) (.inr (.inl scratch)) (by simp)

private theorem prepare_runs [Fintype Parameter] {Scratch : Type} [Fintype Scratch]
    {count : ℕ} (enumeration : Fin count ≃ Scratch) (role : Scratch → Parameter)
    (sizes : Parameter → ℕ) (capacity : ℕ) (contents : Scratch ⊕ Unit → List Symbol)
    (lengths : ∀ scratch, (contents (.inl scratch)).length = sizes (role scratch)) :
    ∃ ticks, ticks ≤ count * (2 * (∑ parameter, sizes parameter) + 3) ∧
      Runs (widths role sizes capacity) readOnly
        (Pipeline.machine (fun index => copySize role (enumeration index)) (fun _ => 0)) ticks
        (Pipeline.position (fun _ : Fin count => (0 : Fin 3)) 0) (fun _ => 0) (initial sizes contents)
        none (fun _ => 0) (ready role sizes 0 (contents (.inr ()))) := by
  classical
  let width := widths role sizes capacity
  let immutable : TapeName Parameter Scratch → Bool := readOnly
  obtain ⟨ticks, final, cost, trace, finalEq⟩ := Pipeline.runs width immutable
    (fun index => copySize role (enumeration index)) (fun _ => 0) (fun _ => 2)
    (fun stage tapes => tapes = preparing enumeration role sizes stage.val contents)
    (2 * (∑ parameter, sizes parameter) + 2)
    (by intro index symbols; simp [copySize, StandardTapeCommands.copy, wire, StandardTerminatedCopy.machine])
    (by
      intro index tapes represented
      subst tapes
      have targetEq : preparing enumeration role sizes index.val contents (.inr (.inl (enumeration index))) =
          buffer (contents (.inl (enumeration index))) := by
        simp [preparing]
      have copied := StandardTapeCommands.copy_runs (.inl (role (enumeration index)))
        (.inr (.inl (enumeration index))) (by simp) width immutable rfl
        (List.replicate (sizes (role (enumeration index))) true)
        (contents (.inl (enumeration index)))
        (by simp [width, widths]) (by simp [width, widths]) (by simpa using lengths (enumeration index))
        (preparing enumeration role sizes index.val contents) rfl targetEq
      have next : Function.update (preparing enumeration role sizes index.val contents)
          (.inr (.inl (enumeration index))) (buffer (word (List.replicate (sizes (role (enumeration index))) true))) =
          preparing enumeration role sizes (index.val + 1) contents := by
        funext name
        cases name with
        | inl parameter => simp [preparing]
        | inr name => cases name with
          | inr output => simp [preparing]
          | inl scratch =>
            by_cases selected : scratch = enumeration index
            · subst scratch
              simp [preparing, unary, CallingConvention.tape, buffer]
            · have notIndex : (enumeration.symm scratch).val ≠ index.val := by
                intro equal
                apply selected
                exact (enumeration.apply_symm_apply scratch).symm.trans (congrArg enumeration (Fin.ext equal))
              have notTarget : (Sum.inr (Sum.inl scratch) : TapeName Parameter Scratch) ≠ .inr (.inl (enumeration index)) := by
                simpa using selected
              rw [Function.update_of_ne notTarget]
              have same : (enumeration.symm scratch).val < index.val + 1 ↔
                  (enumeration.symm scratch).val < index.val := by omega
              simp only [preparing, same]
      have sizeBound : sizes (role (enumeration index)) ≤ ∑ parameter, sizes parameter :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
      refine ⟨2 * sizes (role (enumeration index)) + 2, _, by omega, ?_, next⟩
      simpa only [copySize, List.length_replicate] using copied)
    (initial sizes contents)
    (by funext name; cases name with
        | inl parameter => rfl
        | inr name => cases name <;> simp [initial, preparing])
  have finished : final = ready role sizes 0 (contents (.inr ())) := by
    rw [finalEq]
    funext name
    cases name with
    | inl parameter => rfl
    | inr name => cases name with
      | inl scratch => simp [preparing, ready, (enumeration.symm scratch).isLt]
      | inr output => rfl
  exact ⟨ticks, by omega, by simpa only [finished] using trace⟩

private def appenderWiring (Parameter Scratch : Type) :
    (Scratch ⊕ Unit) ↪ TapeName Parameter Scratch := Function.Embedding.inr

private def outputWiring (Parameter Scratch : Type) : Unit ↪ TapeName Parameter Scratch :=
  oneTape (.inr (.inr ()))

/-- A fixed polynomial has a finite machine computing its exact unary value.
The size inputs are restored, preparation and output restoration are charged,
and private storage and the runtime polynomial are existential witnesses. -/
theorem computable [Fintype Parameter] (polynomial : MvPolynomial Parameter ℕ) :
    Computable (fun sizes => MvPolynomial.eval sizes polynomial) := by
  classical
  obtain ⟨Scratch, finiteScratch, role, State, finiteState, appender, entry, exit, bound, correct⟩ :=
    UnaryPolynomial.exists_appender polynomial
  let scratchFiniteInstance := finiteScratch
  let stateFiniteInstance := finiteState
  let count := Fintype.card Scratch
  let enumeration : Fin count ≃ Scratch := (Fintype.equivFin Scratch).symm
  let preparation := Pipeline.machine (fun index => copySize role (enumeration index)) (fun _ => 0)
  let prepareEntry := Pipeline.position (fun _ : Fin count => (0 : Fin 3)) 0
  let evaluate := wire (Alphabet := CallingConvention.Alphabet (TapeName Parameter Scratch)) (appenderWiring Parameter Scratch) appender
  let restore := wire (Alphabet := CallingConvention.Alphabet (TapeName Parameter Scratch)) (outputWiring Parameter Scratch) StandardHead.BlankReturn.fromEnd
  let algorithm := MultiTape.sequence preparation (MultiTape.sequence evaluate restore (.inl 1)) (.inl entry)
  refine ⟨Scratch, inferInstance, role,
    Pipeline.State (fun _ : Fin count => Fin 3) ⊕ (State ⊕ (Fin 2 ⊕ Fin 3)), inferInstance,
    algorithm, .inl prepareEntry, .inr (.inr (.inr 2)),
    MvPolynomial.C count * (2 * (∑ parameter, MvPolynomial.X parameter) + 3) + bound + polynomial + 5, ?_, ?_⟩
  · intro symbols
    simp [algorithm, MultiTape.sequence, restore, wire, StandardHead.BlankReturn.fromEnd,
      StandardHead.BlankReturn.machine]
  · intro sizes tapes headers regions
    choose contents lengths contentsEq using fun name : Scratch ⊕ Unit => (regions (.inr name)).exists_buffer
    have sourceLengths : ∀ scratch, (contents (.inl scratch)).length = sizes (role scratch) := by
      intro scratch; exact lengths (.inl scratch)
    have resultLength : (contents (.inr ())).length = MvPolynomial.eval sizes polynomial := lengths (.inr ())
    have canonical : tapes = initial sizes contents := by
      funext name
      cases name with
      | inl parameter => exact headers parameter
      | inr name => exact contentsEq name
    rw [canonical]
    obtain ⟨prepareTicks, prepareCost, prepared⟩ := prepare_runs enumeration role sizes (MvPolynomial.eval sizes polynomial) contents sourceLengths
    obtain ⟨evaluateTicks, evaluateCost, evaluated⟩ := correct.2 sizes 0 (MvPolynomial.eval sizes polynomial) (by simp) (contents (.inr ()))
    have exhausted : (contents (.inr ())).drop (MvPolynomial.eval sizes polynomial) = [] := by
      exact List.drop_eq_nil_of_le (Nat.le_of_eq resultLength)
    simp only [zero_add, exhausted] at evaluated
    let capacity := MvPolynomial.eval sizes polynomial
    let layoutWidth := widths role sizes capacity
    let cursorPosition : TapeName Parameter Scratch → ℤ
      | .inr (.inr _) => capacity
      | _ => 0
    have evaluated := evaluated.regions
      (fun name => layoutWidth (appenderWiring Parameter Scratch name)) (fun _ => 0)
      (by intro name writable; cases name with
          | inl source => simp [UnaryPolynomial.readOnly] at writable
          | inr output => simp [layoutWidth, widths, appenderWiring, capacity])
    have evaluation := evaluated.wire_at_of_eq (appenderWiring Parameter Scratch) layoutWidth readOnly
      (by intro name; rfl) (by intro name premise; cases name <;> simp [readOnly, appenderWiring] at premise)
      (fun _ => 0) cursorPosition
      (ready role sizes 0 (contents (.inr ()))) (ready role sizes (MvPolynomial.eval sizes polynomial))
      (by intro name; cases name <;> rfl)
      (by intro name; cases name <;> rfl)
      (by intro name outside; cases name with
          | inl parameter => rfl
          | inr name => exact False.elim (outside ⟨name, rfl⟩))
      (by intro name; cases name <;> rfl)
      (by intro name; cases name <;> rfl)
      (by intro name outside; cases name with
          | inl parameter => rfl
          | inr name => exact False.elim (outside ⟨name, rfl⟩))
    have returned := (StandardHead.BlankReturn.fromEnd_runs
      (List.replicate (MvPolynomial.eval sizes polynomial) true))
    simp only [List.length_replicate] at returned
    have blanks : (Turing.ListBlank.mk [0] : Turing.ListBlank Symbol) = Turing.ListBlank.mk [] :=
      Binary.mk_append_blank []
    have restoration := returned.wire_at_of_eq (outputWiring Parameter Scratch) layoutWidth readOnly
      (by intro name; rfl) (by intro name premise; rfl)
      cursorPosition (fun _ => 0)
      (ready role sizes (MvPolynomial.eval sizes polynomial))
      (result role sizes (MvPolynomial.eval sizes polynomial))
      (by intro name; cases name; rfl)
      (by intro name; rfl)
      (by intro name outside; cases name with
          | inl parameter => rfl
          | inr name => cases name with
            | inl scratch => rfl
            | inr output => exact False.elim (outside ⟨(), rfl⟩))
      (by intro name; cases name
          change UnaryPolynomial.tail (MvPolynomial.eval sizes polynomial) = _
          simp [UnaryPolynomial.tail, Binary.tape, word, Binary.mk_append_blank, blanks])
      (by intro name; cases name
          change unary (MvPolynomial.eval sizes polynomial) = _
          simp [unary, CallingConvention.tape, buffer, word])
      (by intro name outside; cases name with
          | inl parameter => rfl
          | inr name => cases name with
            | inl scratch => rfl
            | inr output => exact False.elim (outside ⟨(), rfl⟩))
    have tailTrace := evaluation.sequence restore (.inl 1)
      (by intro symbols; simp [wire, correct.1]) restoration
    have complete := prepared.sequence (MultiTape.sequence evaluate restore (.inl 1)) (.inl entry) (by intro symbols; rfl) tailTrace
    refine ⟨prepareTicks + (evaluateTicks + (MvPolynomial.eval sizes polynomial + 3) + 1) + 1, ?_, ?_⟩
    · simp only [map_add, map_mul, map_ofNat, MvPolynomial.eval_C, map_sum, MvPolynomial.eval_X]
      nlinarith
    · simpa only [algorithm, List.length_replicate] using complete

end Evaluation
end Polytime2.PolynomialEvaluator

namespace Polytime2.EncodedDomain

-- carrierLevel: values of the encoded domain; widths depend only on sizes.
universe carrierLevel
variable {Parameter : Type} [Fintype Parameter]

/-- The exact bit width of every encoded domain has a certified unary evaluator. -/
theorem width_computable (domain : EncodedDomain.{0, carrierLevel} Parameter) :
    PolynomialEvaluator.Computable domain.width :=
  PolynomialEvaluator.computable domain.widthPolynomial

end Polytime2.EncodedDomain
