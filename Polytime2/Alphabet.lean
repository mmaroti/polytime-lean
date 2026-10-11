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

import Polytime2.Machine

/-! # Alphabet equivalences for heterogeneous tape wiring

Dependent alphabets that agree at each named tape need not be definitionally
equal in Lean. A blank-preserving equivalence adapts a routine to its caller
without adding transitions. Matrix address and scalar-access composition needs
this adapter even though the corresponding symbols are identical.
-/

namespace Polytime2.MultiTape

-- tapeLevel: common tape names; sourceLevel, targetLevel: the two alphabets.
-- stateLevel: the unchanged controller.
universe tapeLevel sourceLevel targetLevel stateLevel
variable {TapeName : Type tapeLevel}
variable {Source : TapeName → Type sourceLevel} {Target : TapeName → Type targetLevel}
variable [∀ name, Inhabited (Source name)] [∀ name, Inhabited (Target name)]
variable {State : Type stateLevel}

@[simp] theorem mapTape_identity {Symbol : Type sourceLevel} [Inhabited Symbol] (tape : Turing.Tape Symbol) :
    tape.map (⟨id, rfl⟩ : Turing.PointedMap Symbol Symbol) = tape := by
  have mapHalf : ∀ half : Turing.ListBlank Symbol,
      half.map (⟨id, rfl⟩ : Turing.PointedMap Symbol Symbol) = half := by
    intro half
    induction half using Turing.ListBlank.induction_on with
    | h values => simp [Turing.ListBlank.map_mk]
  cases tape
  simp [Turing.Tape.map, mapHalf]

def pointedAlphabet (equivalences : ∀ name, Source name ≃ Target name)
    (blanks : ∀ name, equivalences name default = default) (name : TapeName) :
    Turing.PointedMap (Source name) (Target name) :=
  ⟨equivalences name, blanks name⟩

def mapTapes (equivalences : ∀ name, Source name ≃ Target name)
    (blanks : ∀ name, equivalences name default = default) (tapes : Tapes Source) : Tapes Target :=
  fun name => (tapes name).map (pointedAlphabet equivalences blanks name)

def relabel (equivalences : ∀ name, Source name ≃ Target name) (machine : Machine Source State) :
    Machine Target State := fun state symbols =>
  (machine state (fun name => (equivalences name).symm (symbols name))).map fun command =>
    (command.1, fun name => (equivalences name (command.2 name).1, (command.2 name).2))

private theorem mapped_action (equivalences : ∀ name, Source name ≃ Target name)
    (blanks : ∀ name, equivalences name default = default)
    (actions : Actions Source) (tapes : Tapes Source) :
    mapTapes equivalences blanks (act actions tapes) =
      act (fun name => (equivalences name (actions name).1, (actions name).2)) (mapTapes equivalences blanks tapes) := by
  funext name
  cases direction : (actions name).2 <;>
    simp [mapTapes, act, direction, Turing.Tape.map_write, Turing.Tape.map_move, pointedAlphabet]

theorem relabel_step (equivalences : ∀ name, Source name ≃ Target name)
    (blanks : ∀ name, equivalences name default = default)
    (machine : Machine Source State) (configuration : Configuration Source State) :
    step (relabel equivalences machine) (configuration.1, mapTapes equivalences blanks configuration.2) =
      (step machine configuration).map (fun final => (final.1, mapTapes equivalences blanks final.2)) := by
  have symbols : (fun name => (equivalences name).symm
      (read (mapTapes equivalences blanks configuration.2) name)) = read configuration.2 := by
    funext name
    simp [read, mapTapes, pointedAlphabet]
  simp only [step, relabel, symbols]
  cases transition : machine configuration.1 (read configuration.2) with
  | none => rfl
  | some command => simp [mapped_action]

/-- Relabeling symbols preserves the exact transition count and head positions. -/
theorem Steps.relabel (equivalences : ∀ name, Source name ≃ Target name)
    (blanks : ∀ name, equivalences name default = default)
    {machine : Machine Source State} {ticks : ℕ} {initial final : Configuration Source State}
    (trace : Steps machine ticks initial final) :
    Steps (MultiTape.relabel equivalences machine) ticks
      (initial.1, mapTapes equivalences blanks initial.2)
      (final.1, mapTapes equivalences blanks final.2) := by
  induction trace with
  | zero configuration => exact .zero _
  | @next count initial middle final transition rest hypothesis =>
    refine .next ?_ hypothesis
    rw [relabel_step, transition]
    rfl

end Polytime2.MultiTape
