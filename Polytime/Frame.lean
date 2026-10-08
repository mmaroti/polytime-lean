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

import Polytime.TupleMachine

/-! # Executable preparation from a size header and canonical input bits

The header contains one unary natural per parameter in the supplied fixed
ordering. Scratch slots contain blank cells, not assumed default domain values.
Preparation here is an executable layout algorithm; its general tape compilation
is separate from the concrete tape routines.
-/

namespace Polytime.Frame

-- u: carriers of the input and scratch domain expressions.
universe u

open TupleMachine (Symbol data word)

variable {ctx : SizeContext}

/-- Unary fields are self-delimiting, including zero. -/
def header (values : List ℕ) : List Bool :=
  values.flatMap fun value => List.replicate value true ++ [false]

@[simp] theorem header_length (values : List ℕ) :
    (header values).length = values.sum + values.length := by
  induction values with
  | nil => rfl
  | cons value values hypothesis => simp [header] at *; omega

/-- Parse one unary natural, leaving the rest of the bit stream untouched. -/
def parseNatural : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest => (parseNatural rest).map fun (value, remaining) => (value + 1, remaining)

/-- The number of fields is fixed by specialization, not read from the input. -/
def parseHeader : ℕ → List Bool → Option (List ℕ × List Bool)
  | 0, bits => some ([], bits)
  | count + 1, bits => do
    let (value, rest) ← parseNatural bits
    let (values, remaining) ← parseHeader count rest
    pure (value :: values, remaining)

@[simp] theorem parseNatural_encoded (value : ℕ) (rest : List Bool) :
    parseNatural (List.replicate value true ++ false :: rest) = some (value, rest) := by
  induction value with
  | zero => rfl
  | succ value hypothesis => simp [List.replicate_succ, parseNatural, hypothesis]

@[simp] theorem parseHeader_encoded (values : List ℕ) (rest : List Bool) :
    parseHeader values.length (header values ++ rest) = some (values, rest) := by
  induction values with
  | nil => rfl
  | cons value values hypothesis =>
    simp only [header] at hypothesis
    simp [header, List.append_assoc, parseHeader, hypothesis]

/-- Fixed parameter enumeration is compile-time data. -/
def values {count : ℕ} (ordering : ctx.Parameter ≃ Fin count) (assignment : SizeAssignment ctx) :
    List ℕ := List.ofFn fun index => assignment (ordering.symm index)

def assignment {count : ℕ} (ordering : ctx.Parameter ≃ Fin count) (values : List ℕ) :
    SizeAssignment ctx := fun name => values.getD (ordering name).val 0

@[simp] theorem assignment_values {count : ℕ} (ordering : ctx.Parameter ≃ Fin count)
    (sizes : SizeAssignment ctx) : assignment ordering (values ordering sizes) = sizes := by
  funext name
  simp [assignment, values, List.getD_eq_getElem?_getD, (ordering name).isLt]

/-- Delimit each reserved scratch slot; no logical value is assigned to it. -/
def scratchCells (domains : List (DomainExpression.{u} ctx)) (sizes : SizeAssignment ctx) : List Symbol :=
  domains.flatMap fun domain => List.replicate (domain.bitWidth sizes) 0 ++ [4]

/-- Input and scratch are distinct regions, surrounded by fixed boundary symbols. -/
def cells (scratch : List (DomainExpression.{u} ctx)) (sizes : SizeAssignment ctx)
    (payload : List Bool) : List Symbol :=
  3 :: (word payload ++ 4 :: (scratchCells scratch sizes ++ [7]))

/-- Retain the size header as metadata available to the bare program. -/
def preparedCells {count : ℕ} (ordering : ctx.Parameter ≃ Fin count)
    (scratch : List (DomainExpression.{u} ctx)) (sizes : SizeAssignment ctx)
    (payload : List Bool) : List Symbol :=
  word (header (values ordering sizes)) ++ 7 :: cells scratch sizes payload

/-- Compute sizes from the header, then reserve exactly the declared capacities.
Mathematical input hypotheses and codec validity are not checked at runtime. -/
def prepare {count : ℕ} (ordering : ctx.Parameter ≃ Fin count)
    (input : DomainExpression.{u} ctx) (scratch : List (DomainExpression.{u} ctx))
    (source : List Bool) : Option (SizeAssignment ctx × List Symbol) := do
  let (parameters, payload) ← parseHeader count source
  let sizes := assignment ordering parameters
  if payload.length = input.bitWidth sizes then
    pure (sizes, word (header parameters) ++ 7 :: cells scratch sizes payload)
  else none

/-- Serialize the assignment separately from the canonical input encoding. -/
def serialize {count : ℕ} (ordering : ctx.Parameter ≃ Fin count)
    (input : DomainExpression.{u} ctx) (sizes : SizeAssignment ctx)
    (bits : BitVec (input.bitWidth sizes)) : List Bool :=
  header (values ordering sizes) ++ List.ofFn (BoolTuple.fromBits bits)

/-- Every exact-width payload produces precisely the specified prepared frame. -/
theorem prepare_serialized {count : ℕ} (ordering : ctx.Parameter ≃ Fin count)
    (input : DomainExpression.{u} ctx) (scratch : List (DomainExpression.{u} ctx))
    (sizes : SizeAssignment ctx) (bits : BitVec (input.bitWidth sizes)) :
    prepare ordering input scratch (serialize ordering input sizes bits) =
      some (sizes, preparedCells ordering scratch sizes (List.ofFn (BoolTuple.fromBits bits))) := by
  have headerLength : (values ordering sizes).length = count := by simp [values]
  have parsed := parseHeader_encoded (values ordering sizes) (List.ofFn (BoolTuple.fromBits bits))
  rw [headerLength] at parsed
  simp [prepare, serialize, preparedCells, parsed]

/-- Canonical mathematical inputs are installed without changing their bits. -/
theorem prepare_encoded {count : ℕ} (ordering : ctx.Parameter ≃ Fin count)
    (input : DomainExpression.{u} ctx) (scratch : List (DomainExpression.{u} ctx))
    (sizes : SizeAssignment ctx) (value : input.Value sizes) :
    prepare ordering input scratch (serialize ordering input sizes (input.encode sizes value)) =
      some (sizes, preparedCells ordering scratch sizes (List.ofFn (BoolTuple.fromBits (input.encode sizes value)))) :=
  prepare_serialized ordering input scratch sizes _

@[simp] theorem scratchCells_length (domains : List (DomainExpression.{u} ctx)) (sizes : SizeAssignment ctx) :
    (scratchCells domains sizes).length = (domains.map fun domain => domain.bitWidth sizes).sum + domains.length := by
  induction domains with
  | nil => rfl
  | cons domain domains hypothesis => simp [scratchCells]; omega

@[simp] theorem cells_length (scratch : List (DomainExpression.{u} ctx)) (sizes : SizeAssignment ctx)
    (payload : List Bool) :
    (cells scratch sizes payload).length =
      payload.length + (scratch.map fun domain => domain.bitWidth sizes).sum + scratch.length + 3 := by
  simp [cells]; omega

/-- Read the installed input region; marker and scratch cells are excluded. -/
theorem input_preserved (scratch : List (DomainExpression.{u} ctx)) (sizes : SizeAssignment ctx)
    (payload : List Bool) :
    ((cells scratch sizes payload).drop 1).take payload.length = word payload := by
  simp [cells]

/-- Prepared metadata and delimiters do not alter the canonical input region. -/
theorem prepared_input_preserved {count : ℕ} (ordering : ctx.Parameter ≃ Fin count)
    (scratch : List (DomainExpression.{u} ctx)) (sizes : SizeAssignment ctx) (payload : List Bool) :
    ((preparedCells ordering scratch sizes payload).drop
      ((header (values ordering sizes)).length + 2)).take payload.length = word payload := by
  have empty : (word (header (values ordering sizes))).drop
      ((header (values ordering sizes)).length + 2) = [] :=
    List.drop_eq_nil_of_le (by simp)
  simp only [preparedCells, List.drop_append, empty, TupleMachine.word_length,
    Nat.add_sub_cancel_left, List.nil_append]
  simp [cells]

noncomputable section StorageBound

/-- Frame storage has an automatically composed polynomial bound. -/
def sizeBound (input : DomainExpression.{u} ctx) (scratch : List (DomainExpression.{u} ctx)) : SizePolynomial ctx :=
  input.sizeBound + (scratch.map DomainExpression.sizeBound).sum + SizePolynomial.constant (scratch.length + 3)

theorem cells_bounded (input : DomainExpression.{u} ctx) (scratch : List (DomainExpression.{u} ctx))
    (sizes : SizeAssignment ctx) (bits : BitVec (input.bitWidth sizes)) :
    (cells scratch sizes (List.ofFn (BoolTuple.fromBits bits))).length ≤ (sizeBound input scratch).eval sizes := by
  have widths : (scratch.map fun domain => domain.bitWidth sizes).sum ≤
      ((scratch.map DomainExpression.sizeBound).sum).eval sizes := by
    induction scratch with
    | nil => simp
    | cons domain domains hypothesis =>
      simpa using Nat.add_le_add (domain.bitWidth_le sizes) hypothesis
  simp only [cells_length, List.length_ofFn, sizeBound, SizePolynomial.eval_add, SizePolynomial.eval_constant]
  have inputWidth := input.bitWidth_le sizes
  omega

/-- The retained header also has polynomial length in the size parameters. -/
def headerBound {count : ℕ} (ordering : ctx.Parameter ≃ Fin count) : SizePolynomial ctx :=
  (List.ofFn fun index => SizePolynomial.parameter (ordering.symm index)).sum +
    SizePolynomial.constant (count + 1)

@[simp] theorem headerBound_eval {count : ℕ} (ordering : ctx.Parameter ≃ Fin count)
    (sizes : SizeAssignment ctx) :
    (headerBound ordering).eval sizes = (header (values ordering sizes)).length + 1 := by
  simp [headerBound, values, List.map_ofFn, Function.comp_def, Nat.add_assoc]

/-- The complete frame, including size metadata, has a composed storage bound. -/
theorem preparedCells_bounded {count : ℕ} (ordering : ctx.Parameter ≃ Fin count)
    (input : DomainExpression.{u} ctx) (scratch : List (DomainExpression.{u} ctx))
    (sizes : SizeAssignment ctx) (bits : BitVec (input.bitWidth sizes)) :
    (preparedCells ordering scratch sizes (List.ofFn (BoolTuple.fromBits bits))).length ≤
      (headerBound ordering + sizeBound input scratch).eval sizes := by
  have capacity := cells_bounded input scratch sizes bits
  simp only [preparedCells, List.length_append, List.length_cons, TupleMachine.word_length,
    SizePolynomial.eval_add, headerBound_eval]
  omega

end StorageBound
end Polytime.Frame
