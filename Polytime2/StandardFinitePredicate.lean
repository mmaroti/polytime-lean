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

import Polytime2.StandardFiniteTable
import Polytime2.CallingConventionRegions

/-! # A fixed finite predicate on one immutable encoded argument

The binary-table primitive's second argument is a private zero-bit singleton.
Its whole tape is blank by its region contract, so no initialization is needed.
-/

namespace Polytime2.StandardFinitePredicate

open MultiTape CallingConvention

def unitDomain : EncodedDomain Empty := EncodedDomain.fixed (Equiv.refl (Fin 1))
abbrev State (width : ℕ) := StandardFiniteTable.State width 0 1
abbrev Alphabet := CallingConvention.Alphabet (Fin 3)

def domains (domain : EncodedDomain.{0, 0} Empty) : Fin 3 → EncodedDomain Empty :=
  StandardFiniteTable.domains domain unitDomain EncodedDomain.booleans

def readOnly (name : Fin 3) : Bool := decide (name = 0)

noncomputable def machine (domain : EncodedDomain.{0, 0} Empty)
    (predicate : ∀ assignment, domain.Carrier assignment → Bool) : Machine Alphabet (State (domain.width Empty.elim)) :=
  StandardFiniteTable.algorithm domain unitDomain EncodedDomain.booleans (fun assignment value _ => predicate assignment value)

/-- Only the scalar is a public input and only the Boolean is a public output.
The private singleton needs no validity guarantee on return. -/
theorem contract (domain : EncodedDomain.{0, 0} Empty)
    (predicate : ∀ assignment, domain.Carrier assignment → Bool) :
    CallingConvention.Realizes (domains domain) readOnly StandardFiniteTable.sizeTapes StandardFiniteTable.outputTapes (machine domain predicate)
      StandardFiniteTable.entry StandardFiniteTable.exit (fun _ _ => True)
      (fun assignment input output => output () = predicate assignment (input ⟨0, rfl⟩)) := by
  obtain ⟨bound, execute⟩ := (StandardFiniteTable.contract domain unitDomain EncodedDomain.booleans
    (fun assignment value _ => predicate assignment value)).wired_runs (Function.Embedding.refl (Fin 3))
  refine ⟨(by intro parameter; cases parameter), (by intro name; rfl), (by intro symbols; rfl), bound, ?_⟩
  intro assignment input initial valid represented headers
  have sameAssignment : assignment = (Empty.elim : Empty → ℕ) := Subsingleton.elim _ _
  subst assignment
  obtain ⟨oldUnit, length, unitEq⟩ := represented.2 1 rfl
  change oldUnit.length = 0 at length
  have empty : oldUnit = [] := List.eq_nil_of_length_eq_zero length
  subst oldUnit
  have unitCanonical : initial 1 = encoded unitDomain Empty.elim (0 : Fin 1) := unitEq
  let localInput : Inputs (domains domain) StandardFiniteTable.readOnly Empty.elim := fun name => by
    rcases name with ⟨name, readonly⟩
    by_cases scalar : name = 0
    · subst name; exact input ⟨0, rfl⟩
    · have singleton : name = 1 := by
        have accepted : name.val < 2 := of_decide_eq_true readonly
        apply Fin.ext
        omega
      subst name
      exact (0 : Fin 1)
  obtain ⟨ticks, localOutput, final, cost, trace, correct, canonical, outside, immutable⟩ :=
    execute Empty.elim localInput (fun name => (domains domain name).width Empty.elim) readOnly initial
      (fun _ => rfl)
      (by intro name premise; fin_cases name <;> first | rfl | contradiction)
      trivial
      (by intro name readonly; fin_cases name <;> first | exact represented.1 0 rfl | exact unitCanonical | contradiction)
      (by intro name writable; exact represented.region name)
      (by intro parameter; cases parameter)
  let output : Outputs (domains domain) StandardFiniteTable.outputTapes Empty.elim :=
    fun _ => localOutput ()
  refine ⟨ticks, output, final, cost, ?_, correct, ?_⟩
  · rw [MultiTape.wire_refl] at trace
    exact trace
  · intro name
    cases name
    exact canonical ()

end Polytime2.StandardFinitePredicate
