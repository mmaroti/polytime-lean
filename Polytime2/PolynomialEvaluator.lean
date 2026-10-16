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
the result tape initially contain blanks. A fixed finite machine prepares its
own variable-occurrence copies, evaluates the specialized polynomial, and
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

/-- Canonical unary size inputs and otherwise blank storage. -/
def initial {Scratch : Type} (sizes : Parameter → ℕ) : Tapes (CallingConvention.Alphabet (TapeName Parameter Scratch))
  | .inl parameter => unary (sizes parameter)
  | .inr _ => buffer []

/-- Only the result is public; occurrence copies remain private. -/
def result {Scratch : Type} (role : Scratch → Parameter) (sizes : Parameter → ℕ)
    (value : ℕ) : Tapes (CallingConvention.Alphabet (TapeName Parameter Scratch))
  | .inl parameter => unary (sizes parameter)
  | .inr (.inl scratch) => unary (sizes (role scratch))
  | .inr (.inr _) => unary value

/-- Size input symbols are never rewritten by any controller transition. -/
def ImmutableInputs {Scratch State : Type}
    (machine : Machine (CallingConvention.Alphabet (TapeName Parameter Scratch)) State) : Prop :=
  ∀ state symbols next actions, machine state symbols = some (next, actions) →
    ∀ parameter, (actions (.inl parameter)).1 = symbols (.inl parameter)

/-- A finite unary evaluator with hidden private tapes and polynomial runtime. -/
def Computable [Fintype Parameter] (width : (Parameter → ℕ) → ℕ) : Prop :=
  ∃ (Scratch : Type) (_ : Fintype Scratch) (role : Scratch → Parameter)
    (State : Type) (_ : Fintype State)
    (machine : Machine (CallingConvention.Alphabet (TapeName Parameter Scratch)) State)
    (entry exit : State) (bound : MvPolynomial Parameter ℕ),
    (∀ symbols, machine exit symbols = none) ∧ ImmutableInputs machine ∧
    ∀ sizes, ∃ ticks, ticks ≤ MvPolynomial.eval sizes bound ∧
      Steps machine ticks (entry, initial sizes) (exit, result role sizes (width sizes))

private def ready {Scratch : Type} (role : Scratch → Parameter) (sizes : Parameter → ℕ)
    (written : ℕ) : Tapes (CallingConvention.Alphabet (TapeName Parameter Scratch))
  | .inl parameter => unary (sizes parameter)
  | .inr (.inl scratch) => unary (sizes (role scratch))
  | .inr (.inr _) => UnaryPolynomial.tail written

private def preparing {Scratch : Type} {count : ℕ} (enumeration : Fin count ≃ Scratch)
    (role : Scratch → Parameter) (sizes : Parameter → ℕ) (stage : ℕ) :
    Tapes (CallingConvention.Alphabet (TapeName Parameter Scratch))
  | .inl parameter => unary (sizes parameter)
  | .inr (.inl scratch) =>
    if (enumeration.symm scratch).val < stage then unary (sizes (role scratch)) else buffer []
  | .inr (.inr _) => buffer []

private def copySize {Scratch : Type} (role : Scratch → Parameter) (scratch : Scratch) :
    Machine (CallingConvention.Alphabet (TapeName Parameter Scratch)) (Fin 3) :=
  StandardTapeCommands.copy (.inl (role scratch)) (.inr (.inl scratch)) (by simp)

private theorem blank_buffer (count : ℕ) : buffer (List.replicate count (0 : Symbol)) = buffer [] := by
  have equal : Turing.ListBlank.mk (List.replicate count (0 : Symbol)) = Turing.ListBlank.mk [] :=
    Quotient.sound (Or.inr ⟨count, by simp⟩)
  exact congrArg (fun right => Turing.Tape.mk' (Turing.ListBlank.mk ([] : List Symbol)) right) equal

private theorem copy_source_immutable (state : Fin 3) (symbols : Bool → Symbol)
    (next : Fin 3) (actions : Bool → Symbol × Option Turing.Dir)
    (instruction : StandardTerminatedCopy.machine state symbols = some (next, actions)) :
    (actions false).1 = symbols false := by
  fin_cases state <;> simp only [StandardTerminatedCopy.machine] at instruction
  all_goals (try split at instruction) <;> simp_all
  all_goals (rw [← instruction.2]) <;> simp_all

private theorem copySize_immutable {Scratch : Type} (role : Scratch → Parameter) (scratch : Scratch) :
    ImmutableInputs (copySize role scratch) := by
  classical
  intro state symbols next actions instruction parameter
  unfold copySize StandardTapeCommands.copy wire at instruction
  cases command : StandardTerminatedCopy.machine state
      (fun name => symbols ((twoTapes (.inl (role scratch)) (.inr (.inl scratch)) (by simp)) name)) with
  | none => simp [command] at instruction
  | some commandValue =>
    simp only [command, Option.map_some, Option.some.injEq, Prod.mk.injEq] at instruction
    obtain ⟨rfl, rfl⟩ := instruction
    rw [install_two]
    simp only [Function.update_of_ne (Sum.inl_ne_inr)]
    by_cases selected : parameter = role scratch
    · subst parameter
      rw [Function.update_self]
      exact copy_source_immutable state _ _ _ command
    · rw [Function.update_of_ne (by simpa using selected)]
      rfl

private theorem wire_immutable {Scratch Source State : Type}
    (wiring : Source ↪ TapeName Parameter Scratch)
    (outside : ∀ parameter, Sum.inl parameter ∉ Set.range wiring)
    (machine : Machine (CallingConvention.Alphabet Source) State) :
    ImmutableInputs (wire wiring machine) := by
  classical
  intro state symbols next actions instruction parameter
  unfold wire at instruction
  cases command : machine state (fun name => symbols (wiring name)) with
  | none => simp [command] at instruction
  | some commandValue =>
    simp only [command, Option.map_some, Option.some.injEq, Prod.mk.injEq] at instruction
    obtain ⟨rfl, rfl⟩ := instruction
    rw [install_outside wiring _ _ _ (outside parameter)]
    rfl

private theorem sequence_immutable {Scratch First Second : Type}
    (first : Machine (CallingConvention.Alphabet (TapeName Parameter Scratch)) First)
    (second : Machine (CallingConvention.Alphabet (TapeName Parameter Scratch)) Second)
    (entry : Second) (firstImmutable : ImmutableInputs first) (secondImmutable : ImmutableInputs second) :
    ImmutableInputs (MultiTape.sequence first second entry) := by
  intro state symbols next actions instruction parameter
  cases state with
  | inl state =>
    cases command : first state symbols with
    | none =>
      simp only [MultiTape.sequence, command, Option.some.injEq, Prod.mk.injEq] at instruction
      obtain ⟨rfl, rfl⟩ := instruction
      rfl
    | some commandValue =>
      simp only [MultiTape.sequence, command, Option.some.injEq, Prod.mk.injEq] at instruction
      obtain ⟨rfl, rfl⟩ := instruction
      exact firstImmutable state symbols _ _ command parameter
  | inr state =>
    cases command : second state symbols with
    | none => simp [MultiTape.sequence, command] at instruction
    | some commandValue =>
      simp only [MultiTape.sequence, command, Option.map_some, Option.some.injEq, Prod.mk.injEq] at instruction
      obtain ⟨rfl, rfl⟩ := instruction
      exact secondImmutable state symbols _ _ command parameter

private theorem preparation_immutable {Scratch : Type} {count : ℕ}
    (enumeration : Fin count ≃ Scratch) (role : Scratch → Parameter) :
    ImmutableInputs (Pipeline.machine (fun index => copySize role (enumeration index)) (fun _ => 0)) := by
  intro state symbols next actions instruction parameter
  cases state with
  | none => simp [Pipeline.machine] at instruction
  | some state =>
    obtain ⟨index, state⟩ := state
    cases command : copySize role (enumeration index) state symbols with
    | none =>
      simp only [Pipeline.machine, command, Option.some.injEq, Prod.mk.injEq] at instruction
      obtain ⟨rfl, rfl⟩ := instruction
      rfl
    | some commandValue =>
      simp only [Pipeline.machine, command, Option.some.injEq, Prod.mk.injEq] at instruction
      obtain ⟨rfl, rfl⟩ := instruction
      exact copySize_immutable role (enumeration index) state symbols _ _ command parameter

private theorem prepare_steps [Fintype Parameter] {Scratch : Type} [Fintype Scratch]
    {count : ℕ} (enumeration : Fin count ≃ Scratch) (role : Scratch → Parameter)
    (sizes : Parameter → ℕ) :
    ∃ ticks, ticks ≤ count * (2 * (∑ parameter, sizes parameter) + 3) ∧
      Steps (Pipeline.machine (fun index => copySize role (enumeration index)) (fun _ => 0)) ticks
        (Pipeline.position (fun _ : Fin count => (0 : Fin 3)) 0, initial sizes)
        (none, ready role sizes 0) := by
  classical
  let width : TapeName Parameter Scratch → ℕ
    | .inl parameter => sizes parameter
    | .inr (.inl scratch) => sizes (role scratch)
    | .inr (.inr _) => 0
  let immutable : TapeName Parameter Scratch → Bool
    | .inl _ => true
    | .inr _ => false
  obtain ⟨ticks, final, cost, trace, finalEq⟩ := Pipeline.steps
    (fun index => copySize role (enumeration index)) (fun _ => 0) (fun _ => 2)
    (fun stage tapes => tapes = preparing enumeration role sizes stage.val)
    (2 * (∑ parameter, sizes parameter) + 2)
    (by intro index symbols; simp [copySize, StandardTapeCommands.copy, wire, StandardTerminatedCopy.machine])
    (by
      intro index tapes represented
      subst tapes
      have targetEq : preparing enumeration role sizes index.val (.inr (.inl (enumeration index))) =
          buffer (List.replicate (sizes (role (enumeration index))) 0) := by
        simp [preparing, blank_buffer]
      have copied := StandardTapeCommands.copy_runs (.inl (role (enumeration index)))
        (.inr (.inl (enumeration index))) (by simp) width immutable rfl
        (List.replicate (sizes (role (enumeration index))) true)
        (List.replicate (sizes (role (enumeration index))) 0)
        (by simp [width]) (by simp [width]) (by simp)
        (preparing enumeration role sizes index.val) rfl targetEq
      have next : Function.update (preparing enumeration role sizes index.val)
          (.inr (.inl (enumeration index))) (buffer (word (List.replicate (sizes (role (enumeration index))) true))) =
          preparing enumeration role sizes (index.val + 1) := by
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
      simpa only [copySize, List.length_replicate] using copied.steps)
    (initial sizes)
    (by funext name; cases name with
        | inl parameter => rfl
        | inr name => cases name <;> simp [initial, preparing])
  have finished : final = ready role sizes 0 := by
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
    MvPolynomial.C count * (2 * (∑ parameter, MvPolynomial.X parameter) + 3) + bound + polynomial + 5, ?_, ?_, ?_⟩
  · intro symbols
    simp [algorithm, MultiTape.sequence, restore, wire, StandardHead.BlankReturn.fromEnd,
      StandardHead.BlankReturn.machine]
  · change ImmutableInputs (MultiTape.sequence preparation (MultiTape.sequence evaluate restore (.inl 1)) (.inl entry))
    apply sequence_immutable preparation (MultiTape.sequence evaluate restore (.inl 1)) (.inl entry)
      (preparation_immutable enumeration role)
    apply sequence_immutable evaluate restore (.inl 1)
    · exact wire_immutable (appenderWiring Parameter Scratch)
        (by intro parameter; rintro ⟨name, equal⟩; cases equal) appender
    · exact wire_immutable (outputWiring Parameter Scratch)
        (by intro parameter; rintro ⟨name, equal⟩; cases equal) StandardHead.BlankReturn.fromEnd
  · intro sizes
    obtain ⟨prepareTicks, prepareCost, prepared⟩ := prepare_steps enumeration role sizes
    obtain ⟨evaluateTicks, evaluateCost, evaluated⟩ := correct.2 sizes 0
    simp only [zero_add] at evaluated
    have evaluation := wire_steps_of_eq (appenderWiring Parameter Scratch) appender evaluated
      (ready role sizes 0) (ready role sizes (MvPolynomial.eval sizes polynomial))
      (by intro name; cases name <;> rfl)
      (by intro name; cases name <;> rfl)
      (by intro name outside; cases name with
          | inl parameter => rfl
          | inr name => exact False.elim (outside ⟨name, rfl⟩))
    have returned := (StandardHead.BlankReturn.fromEnd_runs
      (List.replicate (MvPolynomial.eval sizes polynomial) true)).steps
    have blanks : (Turing.ListBlank.mk [0] : Turing.ListBlank Symbol) = Turing.ListBlank.mk [] :=
      Binary.mk_append_blank []
    have restoration := wire_steps_of_eq (outputWiring Parameter Scratch)
      StandardHead.BlankReturn.fromEnd returned
      (ready role sizes (MvPolynomial.eval sizes polynomial))
      (result role sizes (MvPolynomial.eval sizes polynomial))
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
    have tailTrace := sequence_steps evaluate restore (.inl 1) evaluation
      (by intro symbols; simp [evaluate, wire, correct.1]) restoration
    have complete := sequence_steps preparation (MultiTape.sequence evaluate restore (.inl 1)) (.inl entry)
      prepared (by intro symbols; rfl) tailTrace
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
