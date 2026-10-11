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

import Polytime2.Binary
import Polytime2.TableTraversal

/-! # Indexed access to a fixed finite scalar array

The index is a polynomially bounded unary counter. Only the index and array
heads travel; the scalar argument stays under its head. Both modes preserve
the index and restore all heads, with no scratch tapes. The unary convention
is suitable for bounded matrix coordinates, not general binary integers.
-/

namespace Polytime2.ScalarAccess

open MultiTape

-- parameterLevel: runtime size names; scalar symbols use a small fixed carrier.
universe parameterLevel
variable {Scalar : Type}

inductive TapeName | index | array | element
  deriving DecidableEq

instance : Fintype TapeName :=
  ⟨{.index, .array, .element}, by intro name; cases name <;> simp⟩

abbrev Alphabet (Scalar : Type) : TapeName → Type
  | .index => Binary.Symbol
  | .array | .element => TableTraversal.Symbol Scalar

instance (name : TapeName) : Inhabited (Alphabet Scalar name) := by
  cases name <;> exact inferInstance

instance [Fintype Scalar] (name : TapeName) : Fintype (Alphabet Scalar name) := by
  cases name <;> exact inferInstance

private theorem replicate_cons (count : ℕ) (tail : List Binary.Symbol) :
    List.replicate count 2 ++ 2 :: tail = 2 :: (List.replicate count 2 ++ tail) := by
  induction count <;> simp_all [List.replicate_succ]

private theorem mk_head_tail (values : List (TableTraversal.Symbol Scalar)) :
    Turing.ListBlank.mk (values.headI :: values.tail) = Turing.ListBlank.mk values := by
  exact Turing.ListBlank.cons_head_tail (Turing.ListBlank.mk values)

@[simp] private theorem mk_cons_head_tail (head : TableTraversal.Symbol Scalar)
    (values : List (TableTraversal.Symbol Scalar)) :
    Turing.ListBlank.mk (head :: values.headI :: values.tail) = Turing.ListBlank.mk (head :: values) := by
  exact congrArg (Turing.ListBlank.cons head) (mk_head_tail values)

def frame (indexLeft indexRight : List Binary.Symbol)
    (arrayLeft arrayRight : List (TableTraversal.Symbol Scalar))
    (element : Turing.Tape (TableTraversal.Symbol Scalar)) : Tapes (Alphabet Scalar)
  | .index => Turing.Tape.mk' (Turing.ListBlank.mk indexLeft) (Turing.ListBlank.mk indexRight)
  | .array => Turing.Tape.mk' (Turing.ListBlank.mk arrayLeft) (Turing.ListBlank.mk arrayRight)
  | .element => element

def machine (write : Bool) : Machine (Alphabet Scalar) (Fin 3) := fun phase symbols =>
  match phase.val with
  | 0 => if symbols .index = 0 then some (1, fun name => match name with
      | .index => (symbols .index, none)
      | .array => (if write then symbols .element else symbols .array, none)
      | .element => (if write then symbols .element else symbols .array, none))
    else some (0, fun name => (symbols name, match name with | .element => none | _ => some .right))
  | 1 => if symbols .index = 3 then
      some (2, fun name => (symbols name, match name with | .element => none | _ => some .right))
    else some (1, fun name => (symbols name, match name with | .element => none | _ => some .left))
  | _ => none

private theorem forward (write : Bool) (before : List Scalar)
    (indexLeft indexRight : List Binary.Symbol)
    (arrayLeft arrayRight : List (TableTraversal.Symbol Scalar))
    (element : Turing.Tape (TableTraversal.Symbol Scalar)) :
    Steps (machine write) before.length
      (0, frame indexLeft (List.replicate before.length 2 ++ indexRight)
        arrayLeft (TableTraversal.word before ++ arrayRight) element)
      (0, frame (List.replicate before.length 2 ++ indexLeft) indexRight
        ((TableTraversal.word before).reverse ++ arrayLeft) arrayRight element) := by
  induction before generalizing indexLeft arrayLeft with
  | nil =>
    simpa [TableTraversal.word] using Steps.zero (machine := machine write)
      (0, frame indexLeft indexRight arrayLeft arrayRight element)
  | cons value before hypothesis =>
    have first : step (machine write)
        (0, frame indexLeft (List.replicate (value :: before).length 2 ++ indexRight)
          arrayLeft (TableTraversal.word (value :: before) ++ arrayRight) element) =
        some (0, frame (2 :: indexLeft) (List.replicate before.length 2 ++ indexRight)
          (some (some value) :: arrayLeft) (TableTraversal.word before ++ arrayRight) element) := by
      simp only [step, machine, Fin.val_zero, MultiTape.read, frame, List.length_cons,
        List.replicate_succ, List.cons_append, Turing.Tape.mk'_head, Turing.ListBlank.head_mk,
        List.headI_cons, show (2 : Binary.Symbol) ≠ 0 by decide, ↓reduceIte, Option.map_some]
      congr 2
      funext name
      cases name <;> simp [act, frame, TableTraversal.word, Turing.Tape.write_mk',
        Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
    have rest := hypothesis (2 :: indexLeft) (some (some value) :: arrayLeft)
    simpa [TableTraversal.word, List.reverse_cons, List.append_assoc, List.replicate_succ,
      replicate_cons] using Steps.next first rest

private theorem rewind (write : Bool) (before : List Scalar)
    (indexLeft indexRight : List Binary.Symbol)
    (arrayLeft arrayRight : List (TableTraversal.Symbol Scalar))
    (current : TableTraversal.Symbol Scalar) (element : Turing.Tape (TableTraversal.Symbol Scalar)) :
    Steps (machine write) (before.length + 2)
      (1, frame (List.replicate before.length 2 ++ 3 :: indexLeft) (0 :: indexRight)
        (TableTraversal.word before ++ arrayLeft) (current :: arrayRight) element)
      (2, frame (3 :: indexLeft) (List.replicate before.length 2 ++ 0 :: indexRight)
        arrayLeft ((TableTraversal.word before).reverse ++ current :: arrayRight) element) := by
  -- Start one cell to the left; the index marker determines the common return point.
  have returnFrom : ∀ (preceding : List Scalar) (symbol : Binary.Symbol) (notMarker : symbol ≠ 3)
      (indexSuffix : List Binary.Symbol) (arraySuffix : List (TableTraversal.Symbol Scalar)),
      Steps (machine write) (preceding.length + 2)
        (1, frame (List.replicate preceding.length 2 ++ 3 :: indexLeft) (symbol :: indexSuffix)
          (TableTraversal.word preceding ++ arrayLeft) arraySuffix element)
        (2, frame (3 :: indexLeft) (List.replicate preceding.length 2 ++ symbol :: indexSuffix)
          arrayLeft ((TableTraversal.word preceding).reverse ++ arraySuffix) element) := by
    intro preceding
    induction preceding with
    | nil =>
      intro symbol notMarker indexSuffix arraySuffix
      have first : step (machine write)
          (1, frame (3 :: indexLeft) (symbol :: indexSuffix) arrayLeft arraySuffix element) =
          some (1, frame indexLeft (3 :: symbol :: indexSuffix) arrayLeft.tail
            (arrayLeft.headI :: arraySuffix) element) := by
        simp only [step, machine, Fin.val_one, MultiTape.read, frame, Turing.Tape.mk'_head,
          Turing.ListBlank.head_mk, List.headI_cons, notMarker, ↓reduceIte, Option.map_some]
        congr 2
        funext name
        cases name <;> simp [act, frame, Turing.Tape.write_mk', Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk]
      have second : step (machine write)
          (1, frame indexLeft (3 :: symbol :: indexSuffix) arrayLeft.tail
            (arrayLeft.headI :: arraySuffix) element) =
          some (2, frame (3 :: indexLeft) (symbol :: indexSuffix) arrayLeft arraySuffix element) := by
        simp only [step, machine, Fin.val_one, MultiTape.read, frame, Turing.Tape.mk'_head,
          Turing.ListBlank.head_mk, List.headI_cons, ↓reduceIte, Option.map_some]
        congr 2
        funext name
        cases name with
        | index => simp [act, frame, Turing.Tape.write_mk', Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
        | element => simp [act, frame]
        | array =>
          simp only [act, frame, Turing.Tape.mk'_head, Turing.ListBlank.head_mk, List.headI_cons,
            Turing.Tape.write_mk', Turing.ListBlank.tail_mk, List.tail_cons, Turing.ListBlank.cons_mk,
            Turing.Tape.move_right_mk']
          cases arrayLeft with
          | nil => exact congrArg (fun left => Turing.Tape.mk' left (Turing.ListBlank.mk arraySuffix)) (mk_head_tail [])
          | cons value values => rfl
      simpa [TableTraversal.word] using Steps.next first (Steps.next second (.zero _))
    | cons value preceding hypothesis =>
      intro symbol notMarker indexSuffix arraySuffix
      have first : step (machine write)
          (1, frame (List.replicate (value :: preceding).length 2 ++ 3 :: indexLeft) (symbol :: indexSuffix)
            (TableTraversal.word (value :: preceding) ++ arrayLeft) arraySuffix element) =
          some (1, frame (List.replicate preceding.length 2 ++ 3 :: indexLeft) (2 :: symbol :: indexSuffix)
            (TableTraversal.word preceding ++ arrayLeft) (some (some value) :: arraySuffix) element) := by
        simp only [step, machine, Fin.val_one, MultiTape.read, frame, Turing.Tape.mk'_head,
          Turing.ListBlank.head_mk, List.headI_cons, notMarker, ↓reduceIte, Option.map_some]
        congr 2
        funext name
        cases name <;> simp [act, frame, TableTraversal.word, Turing.Tape.write_mk',
          Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk, List.replicate_succ]
      have rest := hypothesis 2 (by decide) (symbol :: indexSuffix) (some (some value) :: arraySuffix)
      simpa [TableTraversal.word, List.reverse_cons, List.append_assoc, List.replicate_succ,
        replicate_cons, Nat.add_assoc] using Steps.next first rest
  exact returnFrom before 0 (by decide) indexRight (current :: arrayRight)

/-- Indexed scalar transfer preserves neighboring data and restores all heads. -/
theorem steps (write : Bool) (before after : List Scalar) (value replacement : Scalar)
    (indexLeft indexRight : List Binary.Symbol)
    (arrayLeft arrayRight elementLeft elementRight : List (TableTraversal.Symbol Scalar)) :
    let chosen := if write then replacement else value
    Steps (machine write) (2 * before.length + 3)
      (0, frame (3 :: indexLeft) (List.replicate before.length 2 ++ 0 :: indexRight)
        arrayLeft (TableTraversal.word (before ++ value :: after) ++ arrayRight)
        (Turing.Tape.mk' (Turing.ListBlank.mk elementLeft)
          (Turing.ListBlank.mk (some (some replacement) :: elementRight))))
      (2, frame (3 :: indexLeft) (List.replicate before.length 2 ++ 0 :: indexRight)
        arrayLeft (TableTraversal.word (before ++ chosen :: after) ++ arrayRight)
        (Turing.Tape.mk' (Turing.ListBlank.mk elementLeft)
          (Turing.ListBlank.mk (some (some chosen) :: elementRight)))) := by
  dsimp only
  let chosen := if write then replacement else value
  let element := Turing.Tape.mk' (Turing.ListBlank.mk elementLeft)
    (Turing.ListBlank.mk (some (some replacement) :: elementRight))
  let output := Turing.Tape.mk' (Turing.ListBlank.mk elementLeft)
    (Turing.ListBlank.mk (some (some chosen) :: elementRight))
  have scanned := forward write before (3 :: indexLeft) (0 :: indexRight) arrayLeft
    (some (some value) :: (TableTraversal.word after ++ arrayRight)) element
  have transfer : step (machine write)
      (0, frame (List.replicate before.length 2 ++ 3 :: indexLeft) (0 :: indexRight)
        ((TableTraversal.word before).reverse ++ arrayLeft)
        (some (some value) :: (TableTraversal.word after ++ arrayRight)) element) =
      some (1, frame (List.replicate before.length 2 ++ 3 :: indexLeft) (0 :: indexRight)
        ((TableTraversal.word before).reverse ++ arrayLeft)
        (some (some chosen) :: (TableTraversal.word after ++ arrayRight)) output) := by
    simp only [step, machine, Fin.val_zero, MultiTape.read, frame, Turing.Tape.mk'_head,
      Turing.ListBlank.head_mk, List.headI_cons, ↓reduceIte, Option.map_some]
    congr 2
    funext name
    cases name <;> cases write <;> simp [act, frame, element, output, chosen, Turing.Tape.write_mk', Turing.ListBlank.cons_mk]
  have restored := rewind write before.reverse indexLeft indexRight arrayLeft
    (TableTraversal.word after ++ arrayRight) (some (some chosen)) output
  simp only [List.length_reverse, TableTraversal.word, List.map_reverse, List.reverse_reverse] at restored
  convert scanned.trans (Steps.next transfer restored) using 1 <;>
    first | rfl | omega | simp [TableTraversal.word, List.map_append, List.append_assoc, element, output, chosen]

theorem lookup_steps (values : List Scalar) (index : Fin values.length) (replacement : Scalar)
    (indexLeft indexRight : List Binary.Symbol)
    (arrayLeft arrayRight elementLeft elementRight : List (TableTraversal.Symbol Scalar)) :
    Steps (machine false) (2 * index.val + 3)
      (0, frame (3 :: indexLeft) (List.replicate index.val 2 ++ 0 :: indexRight)
        arrayLeft (TableTraversal.word values ++ arrayRight)
        (Turing.Tape.mk' (Turing.ListBlank.mk elementLeft)
          (Turing.ListBlank.mk (some (some replacement) :: elementRight))))
      (2, frame (3 :: indexLeft) (List.replicate index.val 2 ++ 0 :: indexRight)
        arrayLeft (TableTraversal.word values ++ arrayRight)
        (Turing.Tape.mk' (Turing.ListBlank.mk elementLeft)
          (Turing.ListBlank.mk (some (some values[index.val]) :: elementRight)))) := by
  have split : values.take index.val ++ values[index.val] :: values.drop (index.val + 1) = values := by
    rw [← List.drop_eq_getElem_cons index.isLt, List.take_append_drop]
  have trace := steps false (values.take index.val) (values.drop (index.val + 1)) values[index.val]
    replacement indexLeft indexRight arrayLeft arrayRight elementLeft elementRight
  simpa only [Bool.false_eq_true, ite_false, split, List.length_take, Nat.min_eq_left index.isLt.le] using trace

theorem update_steps (values : List Scalar) (index : Fin values.length) (replacement : Scalar)
    (indexLeft indexRight : List Binary.Symbol)
    (arrayLeft arrayRight elementLeft elementRight : List (TableTraversal.Symbol Scalar)) :
    Steps (machine true) (2 * index.val + 3)
      (0, frame (3 :: indexLeft) (List.replicate index.val 2 ++ 0 :: indexRight)
        arrayLeft (TableTraversal.word values ++ arrayRight)
        (Turing.Tape.mk' (Turing.ListBlank.mk elementLeft)
          (Turing.ListBlank.mk (some (some replacement) :: elementRight))))
      (2, frame (3 :: indexLeft) (List.replicate index.val 2 ++ 0 :: indexRight)
        arrayLeft (TableTraversal.word (values.set index.val replacement) ++ arrayRight)
        (Turing.Tape.mk' (Turing.ListBlank.mk elementLeft)
          (Turing.ListBlank.mk (some (some replacement) :: elementRight)))) := by
  have split : values.take index.val ++ values[index.val] :: values.drop (index.val + 1) = values := by
    rw [← List.drop_eq_getElem_cons index.isLt, List.take_append_drop]
  have replaced : values.take index.val ++ replacement :: values.drop (index.val + 1) = values.set index.val replacement := by
    simpa only [index.isLt, ite_true] using
      (List.set_eq_take_append_cons_drop (l := values) (i := index.val) (a := replacement)).symm
  have trace := steps true (values.take index.val) (values.drop (index.val + 1)) values[index.val]
    replacement indexLeft indexRight arrayLeft arrayRight elementLeft elementRight
  simpa only [Bool.true_eq, ite_true, split, replaced, List.length_take, Nat.min_eq_left index.isLt.le] using trace

/-- A linear transition bound for a polynomially bounded matrix index.
No behavior is specified for malformed index or scalar encodings. -/
theorem realizes [Fintype Scalar] {Parameter : Type parameterLevel} [Fintype Parameter]
    (write : Bool) (capacity : MvPolynomial Parameter ℕ) :
    Realizes (machine (Scalar := Scalar) write) 0 2
      (fun assignment initial => ∃ (before after : List Scalar) (value replacement : Scalar)
        (indexLeft indexRight : List Binary.Symbol)
        (arrayLeft arrayRight elementLeft elementRight : List (TableTraversal.Symbol Scalar)),
        before.length ≤ MvPolynomial.eval assignment capacity ∧
        initial = frame (3 :: indexLeft) (List.replicate before.length 2 ++ 0 :: indexRight)
          arrayLeft (TableTraversal.word (before ++ value :: after) ++ arrayRight)
          (Turing.Tape.mk' (Turing.ListBlank.mk elementLeft)
            (Turing.ListBlank.mk (some (some replacement) :: elementRight))))
      (fun _ initial final => ∃ (before after : List Scalar) (value replacement : Scalar)
        (indexLeft indexRight : List Binary.Symbol)
        (arrayLeft arrayRight elementLeft elementRight : List (TableTraversal.Symbol Scalar)),
        initial = frame (3 :: indexLeft) (List.replicate before.length 2 ++ 0 :: indexRight)
          arrayLeft (TableTraversal.word (before ++ value :: after) ++ arrayRight)
          (Turing.Tape.mk' (Turing.ListBlank.mk elementLeft)
            (Turing.ListBlank.mk (some (some replacement) :: elementRight))) ∧
        final = frame (3 :: indexLeft) (List.replicate before.length 2 ++ 0 :: indexRight)
          arrayLeft (TableTraversal.word (before ++ (if write then replacement else value) :: after) ++ arrayRight)
          (Turing.Tape.mk' (Turing.ListBlank.mk elementLeft)
            (Turing.ListBlank.mk (some (some (if write then replacement else value)) :: elementRight)))) := by
  refine ⟨by intro symbols; rfl, 2 * capacity + 3, ?_⟩
  intro assignment initial valid
  obtain ⟨before, after, value, replacement, indexLeft, indexRight,
    arrayLeft, arrayRight, elementLeft, elementRight, bounded, rfl⟩ := valid
  refine ⟨2 * before.length + 3, _, ?_,
    steps write before after value replacement indexLeft indexRight arrayLeft arrayRight elementLeft elementRight,
    before, after, value, replacement, indexLeft, indexRight, arrayLeft, arrayRight, elementLeft, elementRight, rfl, rfl⟩
  simp only [map_add, map_mul, map_ofNat]
  omega

end Polytime2.ScalarAccess
