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

import Polytime2.Primitives.Append
import Polytime2.Machine.Pipeline

/-! # Joining a finite family of immutable binary words

There is one input tape per field and one output tape. Field widths are runtime
values; source blanks are used only outside their canonical data regions.
-/

namespace Polytime2.Join

open MultiTape CallingConvention
open Binary (Symbol word)

variable {count : ℕ}

abbrev TapeName (count : ℕ) := Fin count ⊕ Unit

def dataWiring (index : Fin count) : Bool ↪ TapeName count :=
  ⟨(fun name => if name then .inr () else .inl index), by
    intro a b equal; cases a <;> cases b <;> simp_all⟩

@[simp] theorem dataWiring_apply (index : Fin count) (name : Bool) :
    dataWiring index name = if name then .inr () else .inl index := rfl

noncomputable def stage (index : Fin count) :=
  wire (Alphabet := Alphabet (TapeName count)) (dataWiring index) Append.machine

noncomputable def stages : Machine (Alphabet (TapeName count))
    (Pipeline.State (fun _ : Fin count => Bool ⊕ (Fin 2 ⊕ Fin 3))) :=
  Pipeline.machine stage (fun _ => .inl false)

noncomputable def restore : Machine (Alphabet (TapeName count)) (Fin 2 ⊕ Fin 3) :=
  wire (oneTape (.inr ())) StandardHead.BlankReturn.fromEnd

noncomputable def machine : Machine (Alphabet (TapeName count))
    (Pipeline.State (fun _ : Fin count => Bool ⊕ (Fin 2 ⊕ Fin 3)) ⊕ (Fin 2 ⊕ Fin 3)) :=
  MultiTape.sequence stages restore (.inl 1)

def entry : Pipeline.State (fun _ : Fin count => Bool ⊕ (Fin 2 ⊕ Fin 3)) ⊕ (Fin 2 ⊕ Fin 3) := Sum.inl (Pipeline.position (fun _ : Fin count => .inl false) 0)
def exit : Pipeline.State (fun _ : Fin count => Bool ⊕ (Fin 2 ⊕ Fin 3)) ⊕ (Fin 2 ⊕ Fin 3) :=
  .inr (.inr 2)

def readOnly : TapeName count → Bool := Sum.elim (fun _ => true) (fun _ => false)

def prefixBits (words : Fin count → List Bool) (index : ℕ) : List Bool :=
  ((List.ofFn words).take index).flatten

@[simp] theorem prefixBits_zero (words : Fin count → List Bool) : prefixBits words 0 = [] := by
  simp [prefixBits]

@[simp] theorem prefixBits_last (words : Fin count → List Bool) :
    prefixBits words count = (List.ofFn words).flatten := by
  simpa only [prefixBits, List.length_ofFn] using congrArg List.flatten (List.take_length (l := List.ofFn words))

theorem prefixBits_succ (words : Fin count → List Bool) (index : Fin count) :
    prefixBits words (index.val + 1) = prefixBits words index.val ++ words index := by
  unfold prefixBits
  rw [List.take_succ_eq_append_getElem (l := List.ofFn words) (i := index.val) (by simp)]
  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil, List.getElem_ofFn]

def widths (words : Fin count → List Bool) : TapeName count → ℕ :=
  Sum.elim (fun index => (words index).length) (fun _ => (List.ofFn words).flatten.length)

def position (words : Fin count → List Bool) (index : ℕ) : TapeName count → ℤ :=
  Sum.elim (fun _ => 0) (fun _ => (prefixBits words index).length)

def frame (words : Fin count → List Bool) (old : List Symbol) (index : ℕ) : Tapes (Alphabet (TapeName count)) :=
  Sum.elim (fun name => buffer (word (words name))) (fun _ =>
    Turing.Tape.mk' (Turing.ListBlank.mk (word (prefixBits words index).reverse))
      (Turing.ListBlank.mk (old.drop (prefixBits words index).length)))

@[simp] theorem halt (symbols : Symbols (Alphabet (TapeName count))) : machine exit symbols = none := by
  simp [machine, exit, MultiTape.sequence, restore, wire, StandardHead.BlankReturn.fromEnd,
    StandardHead.BlankReturn.machine]

/-- A fixed finite machine concatenates all runtime fields, restores every head,
and accepts arbitrary old output contents. -/
theorem runs (words : Fin count → List Bool) (old : List Symbol)
    (oldLength : old.length = (List.ofFn words).flatten.length) :
    ∃ ticks, ticks ≤ count * (2 * (List.ofFn words).flatten.length + 6) +
        (List.ofFn words).flatten.length + 4 ∧
      Runs (widths words) readOnly machine ticks entry (fun _ => 0) (frame words old 0)
        exit (fun _ => 0)
        (Sum.elim (fun name => buffer (word (words name)))
          (fun _ => buffer (word (List.ofFn words).flatten))) := by
  have blank : Turing.ListBlank.mk ([0] : List Symbol) = Turing.ListBlank.mk [] := by
    simpa using Binary.mk_append_blank ([] : List Symbol)
  have prefixBound (index : ℕ) : (prefixBits words index).length ≤ (List.ofFn words).flatten.length := by
    exact List.Sublist.length_le (List.Sublist.flatten (List.take_sublist index (List.ofFn words)))
  obtain ⟨ticks, middle, cost, trace, finalEq⟩ := Pipeline.runs_at (widths words) readOnly stage
    (fun _ => .inl false) (fun _ => .inr (.inr 2))
    (fun index tapes => tapes = frame words old index.val)
    (fun index => position words index.val) (2 * (List.ofFn words).flatten.length + 5)
    (by intro index symbols; simp [stage, wire, Append.halt])
    (by
      intro index tapes represented
      subst tapes
      let before := prefixBits words index.val
      let field := words index
      let previous := (old.drop before.length).take field.length
      have next := prefixBits_succ words index
      have fits : before.length + field.length ≤ (List.ofFn words).flatten.length := by
        have bound := prefixBound (index.val + 1)
        rw [next, List.length_append] at bound
        exact bound
      have previousLength : previous.length = field.length := by
        simp only [previous, List.length_take, List.length_drop, oldLength]
        omega
      have oldSplit : previous ++ (old.drop before.length).drop field.length = old.drop before.length :=
        List.take_append_drop field.length (old.drop before.length)
      simp only [before, List.drop_drop] at oldSplit
      have localTrace := Append.runs field previous previousLength before
        ((old.drop before.length).drop field.length)
        (fun name => widths words (dataWiring index name)) (by exact fits)
      have combined := localTrace.wire_at_of_eq (dataWiring index) (widths words) readOnly
        (by intro name; rfl) (by intro name premise; cases name <;> exact premise)
        (position words index.val) (position words (index.val + 1))
        (frame words old index.val) (frame words old (index.val + 1))
        (by intro name; cases name <;> rfl)
        (by intro name; cases name <;> simp [position, next, before, field])
        (by intro name outside; cases name with
          | inl name => rfl
          | inr name => exact False.elim (outside ⟨true, by cases name; rfl⟩))
        (by intro name; cases name <;>
          simp [frame, before, field, Copy.frame, buffer, Turing.Tape.mk₁,
            Turing.Tape.mk₂, word, blank, Binary.mk_append_blank, oldSplit])
        (by intro name; cases name <;>
          simp only [frame, dataWiring_apply, Bool.false_eq_true, ite_false, ite_true,
            Sum.elim_inl, Sum.elim_inr, Copy.frame, buffer, Turing.Tape.mk₁, Turing.Tape.mk₂,
            next, before, field, word, List.map_append, List.map_reverse, List.reverse_append,
            List.length_append, List.drop_drop, Binary.mk_append_blank, blank])
        (by intro name outside; cases name with
          | inl name => rfl
          | inr name => exact False.elim (outside ⟨true, by cases name; rfl⟩))
      refine ⟨2 * field.length + 5, _, ?_, combined, rfl⟩
      have fieldBound : field.length ≤ (List.ofFn words).flatten.length := by omega
      omega)
    (frame words old 0) rfl
  subst middle
  simp only [Fin.val_zero, Fin.val_last] at trace
  let result : Tapes (Alphabet (TapeName count)) :=
    Sum.elim (fun name => buffer (word (words name))) (fun _ => buffer (word (List.ofFn words).flatten))
  have returned := (StandardHead.BlankReturn.fromEnd_runs (List.ofFn words).flatten).wire_at_of_eq
    (oneTape (.inr () : TapeName count)) (widths words) readOnly
    (by intro name; rfl) (by intro name premise; rfl)
    (position words count) (fun _ => 0) (frame words old count) result
    (by intro name; cases name; simp [position]) (by intro name; rfl)
    (by intro name outside; cases name with
      | inl name => rfl
      | inr name => exact False.elim (outside ⟨(), by cases name; rfl⟩))
    (by
      intro name; cases name
      change Turing.Tape.mk' _ (Turing.ListBlank.mk (old.drop (prefixBits words count).length)) = _
      rw [prefixBits_last, List.drop_eq_nil_of_le (by omega)]
      simp [Binary.tape, word, blank, Binary.mk_append_blank])
    (by intro name; cases name; rfl)
    (by intro name outside; cases name with
      | inl name => rfl
      | inr name => exact False.elim (outside ⟨(), by cases name; rfl⟩))
  have complete := trace.sequence restore (.inl 1) (by intro symbols; rfl) returned
  have zero : position words 0 = fun _ => (0 : ℤ) := by funext name; cases name <;> simp [position]
  rw [zero] at complete
  refine ⟨ticks + ((List.ofFn words).flatten.length + 3) + 1, ?_, complete⟩
  simpa only [Nat.add_assoc, show 5 + 1 = 6 from rfl] using
    Nat.add_le_add_right cost ((List.ofFn words).flatten.length + 4)

end Polytime2.Join
