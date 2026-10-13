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

import Polytime2.StandardFinitePredicate

/-! # Finite scalar tests with an internal zero-bit tape -/

namespace Polytime2.Examples.FinitePredicate

open MultiTape CallingConvention StandardFinitePredicate

private noncomputable def initial (domain : EncodedDomain.{0, 0} Empty) (value : domain.Carrier Empty.elim)
    (oldFlag : Binary.Symbol) : Tapes Alphabet := fun name =>
  if name = 0 then encoded domain Empty.elim value else if name = 1 then buffer [] else buffer [oldFlag]

private theorem execute_predicate (domain : EncodedDomain.{0, 0} Empty) (value : domain.Carrier Empty.elim)
    (predicate : ∀ assignment, domain.Carrier assignment → Bool) (oldFlag : Binary.Symbol) :
    ∃ ticks final,
      Runs (fun name => (domains domain name).width Empty.elim) readOnly (machine domain predicate) ticks
        StandardFiniteTable.entry (fun _ => 0) (initial domain value oldFlag)
        StandardFiniteTable.exit (fun _ => 0) final ∧
      final 2 = encoded EncodedDomain.booleans Empty.elim (predicate Empty.elim value) := by
  obtain ⟨sizeReadOnly, halts, bound, execute⟩ := contract domain predicate
  let input : Inputs (domains domain) readOnly Empty.elim := fun name => by
    rcases name with ⟨name, readonly⟩
    have argument : name = 0 := of_decide_eq_true readonly
    subst name
    exact value
  have represented : Entry (domains domain) readOnly Empty.elim input (initial domain value oldFlag) := by
    refine ⟨?_, ?_⟩
    · intro name readonly
      have argument : name = 0 := of_decide_eq_true readonly
      subst name
      rfl
    · intro name writable
      fin_cases name
      · contradiction
      · exact ⟨[], rfl, rfl⟩
      · exact ⟨[oldFlag], rfl, rfl⟩
  obtain ⟨ticks, output, final, cost, trace, correct, canonical⟩ :=
    execute Empty.elim input (initial domain value oldFlag) trivial represented (by intro parameter; cases parameter)
  change output ⟨2, rfl⟩ = predicate Empty.elim value at correct
  exact ⟨ticks, final, trace, (canonical 2 rfl).trans (congrArg (encoded EncodedDomain.booleans Empty.elim) correct)⟩

/-- The Boolean test overwrites a blank result symbol. -/
example : ∃ ticks final,
    Runs (fun name => (domains (EncodedDomain.booleans (Parameter := Empty)) name).width Empty.elim) readOnly
      (machine (EncodedDomain.booleans (Parameter := Empty)) (fun _ (value : Bool) => !value)) ticks
      StandardFiniteTable.entry (fun _ => 0) (initial EncodedDomain.booleans true 0)
      StandardFiniteTable.exit (fun _ => 0) final ∧
    final 2 = encoded EncodedDomain.booleans Empty.elim false :=
  execute_predicate EncodedDomain.booleans true (fun _ (value : Bool) => !value) 0

/-- Both scalar and private singleton have zero bits; the blank Boolean output
is still written and both empty argument heads return to their starts. -/
example :
    let domain := EncodedDomain.fixed (Parameter := Empty) (Equiv.refl (Fin 1))
    ∃ ticks final,
      Runs (fun name => (domains domain name).width Empty.elim) readOnly
        (machine domain (fun _ (_value : Fin 1) => true)) ticks
        StandardFiniteTable.entry (fun _ => 0) (initial domain (0 : Fin 1) 0)
        StandardFiniteTable.exit (fun _ => 0) final ∧
      final 2 = encoded EncodedDomain.booleans Empty.elim true := by
  intro domain
  exact execute_predicate domain (0 : Fin 1) (fun _ (_value : Fin 1) => true) 0

end Polytime2.Examples.FinitePredicate
