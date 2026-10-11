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

import Polytime2.Wiring

/-! # Synchronous finite-table traversal

One stationary tape holds a runtime scalar. The remaining tapes hold equally
long vectors over a fixed finite carrier. A fixed table transforms each column
of these vectors. All heads are restored, and surrounding cells are preserved.
Row scaling and row addition are instances of this operation.
-/

namespace Polytime2.TableTraversal

open MultiTape

-- scalarLevel: the fixed scalar carrier; dataLevel: the names of synchronized vectors.
-- parameterLevel: the runtime size names used in polynomial certificates.
universe scalarLevel dataLevel parameterLevel

variable {Scalar : Type scalarLevel} [Inhabited Scalar] [DecidableEq Scalar]
variable {Data : Type dataLevel}

abbrev Symbol (Scalar : Type scalarLevel) := Option (Option Scalar)
abbrev TapeName (Data : Type dataLevel) := Sum Unit Data

def word (values : List Scalar) : List (Symbol Scalar) := values.map (some ∘ some)

def frame (parameter : Turing.Tape (Symbol Scalar))
    (left right : Data → List (Symbol Scalar)) : Tapes (fun _ : TapeName Data => Symbol Scalar)
  | .inl _ => parameter
  | .inr name => Turing.Tape.mk' (Turing.ListBlank.mk (left name)) (Turing.ListBlank.mk (right name))

/-- The table is specialization data; its first argument is a runtime scalar. -/
def machine (focus : Data) (table : Scalar → (Data → Scalar) → (Data → Scalar)) :
    Machine (fun _ : TapeName Data => Symbol Scalar) (Fin 3) := fun phase symbols =>
  match phase.val with
  | 0 => match symbols (.inr focus) with
    | some (some _) => some (0, fun name => match name with
      | .inl _ => (symbols name, none)
      | .inr index =>
        (some (some (table ((symbols (.inl ())).join.getD default)
          (fun index => (symbols (.inr index)).join.getD default) index)), some .right))
    | _ => some (1, stationary symbols)
  | 1 => if symbols (.inr focus) = some none then
      some (2, fun name => (symbols name, match name with | .inl _ => none | .inr _ => some .right))
    else some (1, fun name => (symbols name, match name with | .inl _ => none | .inr _ => some .left))
  | _ => none

private theorem forward (focus : Data) (table : Scalar → (Data → Scalar) → (Data → Scalar))
    (parameter : Turing.Tape (Symbol Scalar)) (coefficient : Scalar)
    (parameterHead : parameter.head = some (some coefficient))
    (values : List (Data → Scalar)) (left right : Data → List (Symbol Scalar)) :
    Steps (machine focus table) values.length
      (0, frame parameter left (fun name => word (values.map (fun row => row name)) ++ right name))
      (0, frame parameter
        (fun name => (word (values.map (fun row => table coefficient row name))).reverse ++ left name) right) := by
  induction values generalizing left with
  | nil => simpa [word] using Steps.zero (machine := machine focus table) (0, frame parameter left right)
  | cons value values hypothesis =>
    have first : step (machine focus table)
        (0, frame parameter left (fun name => word ((value :: values).map (fun row => row name)) ++ right name)) =
        some (0, frame parameter (fun name => some (some (table coefficient value name)) :: left name)
          (fun name => word (values.map (fun row => row name)) ++ right name)) := by
      simp only [step, machine, Fin.val_zero, MultiTape.read, frame, word, List.map_cons,
        List.cons_append, Turing.Tape.mk'_head, Turing.ListBlank.head_mk, List.headI_cons,
        parameterHead, Function.comp_def, Option.join_some, Option.getD_some, Option.map_some]
      congr 2
      funext name
      cases name with
      | inl name => simp [act, frame]
      | inr name =>
        simp [act, frame, Turing.Tape.write_mk', Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
    have rest := hypothesis (fun name => some (some (table coefficient value name)) :: left name)
    simpa [word, List.reverse_cons, List.append_assoc] using Steps.next first rest

private theorem rewind (focus : Data) (table : Scalar → (Data → Scalar) → (Data → Scalar))
    (parameter : Turing.Tape (Symbol Scalar)) (values : List (Data → Scalar))
    (left right : Data → List (Symbol Scalar)) (marker current : Data → Symbol Scalar)
    (boundary : marker focus = some none)
    (notBoundary : current focus ≠ some none) :
    Steps (machine focus table) (values.length + 2)
      (1, frame parameter (fun name => word (values.map (fun row => row name)) ++ marker name :: left name)
        (fun name => current name :: right name))
      (2, frame parameter (fun name => marker name :: left name)
        (fun name => (word (values.map (fun row => row name))).reverse ++ current name :: right name)) := by
  induction values generalizing current right with
  | nil =>
    have first : step (machine focus table)
        (1, frame parameter (fun name => marker name :: left name) (fun name => current name :: right name)) =
        some (1, frame parameter left (fun name => marker name :: current name :: right name)) := by
      simp only [step, machine, Fin.val_one, MultiTape.read, frame, Turing.Tape.mk'_head,
        Turing.ListBlank.head_mk, List.headI_cons, notBoundary, ↓reduceIte, Option.map_some]
      congr 2
      funext name
      cases name <;> simp [act, frame, Turing.Tape.write_mk', Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk]
    have second : step (machine focus table)
        (1, frame parameter left (fun name => marker name :: current name :: right name)) =
        some (2, frame parameter (fun name => marker name :: left name) (fun name => current name :: right name)) := by
      simp only [step, machine, Fin.val_one, MultiTape.read, frame, Turing.Tape.mk'_head,
        Turing.ListBlank.head_mk, List.headI_cons, boundary, ↓reduceIte, Option.map_some]
      congr 2
      funext name
      cases name <;> simp [act, frame, Turing.Tape.write_mk', Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
    simpa [word] using Steps.next first (Steps.next second (.zero _))
  | cons value values hypothesis =>
    have first : step (machine focus table)
        (1, frame parameter
          (fun name => word ((value :: values).map (fun row => row name)) ++ marker name :: left name)
          (fun name => current name :: right name)) =
        some (1, frame parameter
          (fun name => word (values.map (fun row => row name)) ++ marker name :: left name)
          (fun name => some (some (value name)) :: current name :: right name)) := by
      simp only [step, machine, Fin.val_one, MultiTape.read, frame, Turing.Tape.mk'_head,
        Turing.ListBlank.head_mk, List.headI_cons, notBoundary, ↓reduceIte, Option.map_some]
      congr 2
      funext name
      cases name <;> simp [act, frame, word, Turing.Tape.write_mk', Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk]
    have rest := hypothesis (fun name => current name :: right name) (fun name => some (some (value name))) (by simp)
    simpa [word, List.reverse_cons, List.append_assoc, Nat.add_assoc] using Steps.next first rest

/-- A delimited focus vector controls traversal of equal-length regions on all
data tapes. Other regions need no boundary symbols of their own, so they can
be rows inside a dense matrix. Arbitrary neighboring cells are preserved. -/
theorem controlled_steps (focus : Data) (table : Scalar → (Data → Scalar) → (Data → Scalar))
    (parameter : Turing.Tape (Symbol Scalar)) (coefficient : Scalar)
    (parameterHead : parameter.head = some (some coefficient))
    (values : List (Data → Scalar)) (left right : Data → List (Symbol Scalar))
    (marker current : Data → Symbol Scalar)
    (boundary : marker focus = some none) (finished : current focus = none) :
    Steps (machine focus table) (2 * values.length + 3)
      (0, frame parameter (fun name => marker name :: left name)
        (fun name => word (values.map (fun row => row name)) ++ current name :: right name))
      (2, frame parameter (fun name => marker name :: left name)
        (fun name => word (values.map (fun row => table coefficient row name)) ++ current name :: right name)) := by
  have scanned := forward focus table parameter coefficient parameterHead values
    (fun name => marker name :: left name) (fun name => current name :: right name)
  have handover : step (machine focus table)
      (0, frame parameter
        (fun name => (word (values.map (fun row => table coefficient row name))).reverse ++ marker name :: left name)
        (fun name => current name :: right name)) =
      some (1, frame parameter
        (fun name => (word (values.map (fun row => table coefficient row name))).reverse ++ marker name :: left name)
        (fun name => current name :: right name)) := by
    simp [step, machine, MultiTape.read, frame, finished]
  have restored := rewind focus table parameter (values.map (table coefficient)).reverse left right
    marker current boundary (by simp [finished])
  simp only [List.map_reverse, List.map_map, Function.comp_def, word, List.reverse_reverse,
    List.length_reverse, List.length_map] at scanned handover restored ⊢
  convert scanned.trans (Steps.next handover restored) using 1
  omega

/-- A runtime-length traversal has a fixed three-state controller. Its scalar
parameter, boundaries, surrounding storage, and all head positions are preserved. -/
theorem steps (focus : Data) (table : Scalar → (Data → Scalar) → (Data → Scalar))
    (parameter : Turing.Tape (Symbol Scalar)) (coefficient : Scalar)
    (parameterHead : parameter.head = some (some coefficient))
    (values : List (Data → Scalar)) (left right : Data → List (Symbol Scalar)) :
    Steps (machine focus table) (2 * values.length + 3)
      (0, frame parameter (fun name => some none :: left name)
        (fun name => word (values.map (fun row => row name)) ++ none :: right name))
      (2, frame parameter (fun name => some none :: left name)
        (fun name => word (values.map (fun row => table coefficient row name)) ++ none :: right name)) := by
  exact controlled_steps focus table parameter coefficient parameterHead values left right
    (fun _ => some none) (fun _ => none) rfl rfl

/-- Polynomial traversal cost; callers use a mathematical table on a fixed finite carrier. -/
theorem realizes {Parameter : Type parameterLevel} [Fintype Parameter] [Fintype Scalar] [Fintype Data]
    (focus : Data) (table : Scalar → (Data → Scalar) → (Data → Scalar))
    (capacity : MvPolynomial Parameter ℕ) :
    Realizes (machine focus table) 0 2
      (fun assignment initial => ∃ (parameter : Turing.Tape (Symbol Scalar)) (coefficient : Scalar)
        (values : List (Data → Scalar)) (left right : Data → List (Symbol Scalar)),
        parameter.head = some (some coefficient) ∧ values.length ≤ MvPolynomial.eval assignment capacity ∧
        initial = frame parameter (fun name => some none :: left name)
          (fun name => word (values.map (fun row => row name)) ++ none :: right name))
      (fun _ initial final => ∃ (parameter : Turing.Tape (Symbol Scalar)) (coefficient : Scalar)
        (values : List (Data → Scalar)) (left right : Data → List (Symbol Scalar)),
        parameter.head = some (some coefficient) ∧
        initial = frame parameter (fun name => some none :: left name)
          (fun name => word (values.map (fun row => row name)) ++ none :: right name) ∧
        final = frame parameter (fun name => some none :: left name)
          (fun name => word (values.map (fun row => table coefficient row name)) ++ none :: right name)) := by
  refine ⟨by intro symbols; rfl, 2 * capacity + 3, ?_⟩
  intro assignment initial valid
  obtain ⟨parameter, coefficient, values, left, right, head, bounded, rfl⟩ := valid
  refine ⟨2 * values.length + 3, _, ?_, steps focus table parameter coefficient head values left right,
    parameter, coefficient, values, left, right, head, rfl, rfl⟩
  simp only [map_add, map_mul, map_ofNat]
  omega

end Polytime2.TableTraversal
