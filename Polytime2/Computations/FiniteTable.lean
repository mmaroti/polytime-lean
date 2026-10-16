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

import Polytime2.Computation.Layout
import Polytime2.StandardFinitePredicate
import Polytime2.StandardRowCombineContract

/-! # Two separate mathematical arguments implemented by a fixed finite table -/

namespace Polytime2.Computation

open MultiTape CallingConvention Realizable

-- carrierLevel: arbitrary mathematical carriers of specialization-fixed domains.
universe carrierLevel

/-- False and true name the two arguments, whose carrier types may differ. -/
def finiteTable (firstDomain secondDomain outputDomain : EncodedDomain.{0, carrierLevel} Empty)
    (operation : ∀ sizes, firstDomain.Carrier sizes → secondDomain.Carrier sizes →
      outputDomain.Carrier sizes) : Computation Empty Bool where
  inputDomains | false => firstDomain | true => secondDomain
  outputDomain := outputDomain
  precondition _ _ := True
  compute sizes arguments := operation sizes (arguments.val false) (arguments.val true)

/-- The existing finite-table machine certifies a public binary computation. -/
theorem finiteTable_realizable
    (firstDomain secondDomain outputDomain : EncodedDomain.{0, carrierLevel} Empty)
    (operation : ∀ sizes, firstDomain.Carrier sizes → secondDomain.Carrier sizes →
      outputDomain.Carrier sizes) : (finiteTable firstDomain secondDomain outputDomain operation).Realizable := by
  classical
  let computation := finiteTable firstDomain secondDomain outputDomain operation
  let scratchDomains : Empty → EncodedDomain.{0, carrierLevel} Empty := Empty.elim
  let wiring : Fin 3 ↪ Internal.TapeName computation Empty :=
    ⟨(fun name => match name.val with
      | 0 => Internal.inputTape computation false
      | 1 => Internal.inputTape computation true
      | _ => (Internal.outputTape computation)), by
      intro first second equal
      fin_cases first <;> fin_cases second <;> first | rfl | cases equal⟩
  refine ⟨Empty, inferInstance, scratchDomains,
    StandardFiniteTable.State (firstDomain.width Empty.elim)
      (secondDomain.width Empty.elim) (outputDomain.width Empty.elim), inferInstance,
    MultiTape.wire (Alphabet := Alphabet (Internal.TapeName computation Empty)) wiring
      (StandardFiniteTable.algorithm firstDomain secondDomain outputDomain operation),
    StandardFiniteTable.entry, StandardFiniteTable.exit, ?_⟩
  have certificate := StandardFiniteTable.contract firstDomain secondDomain outputDomain operation
  obtain ⟨bound, execute⟩ := certificate.wired_runs wiring
  refine ⟨(by intro parameter; cases parameter), (by intro name; rfl),
    (by intro symbols; simp [MultiTape.wire, certificate.2.2.1]), bound, ?_⟩
  intro sizes input initial valid represented headers
  let arguments := Internal.arguments computation scratchDomains sizes input
  let localInput : Inputs (StandardFiniteTable.domains firstDomain secondDomain outputDomain)
      StandardFiniteTable.readOnly sizes
    | ⟨0, _⟩ => arguments false
    | ⟨1, _⟩ => arguments true
    | ⟨2, impossible⟩ => False.elim (Bool.noConfusion impossible)
  obtain ⟨ticks, localOutput, final, cost, trace, correct, canonical, outside, immutable⟩ :=
    execute sizes localInput
      (fun name => (Internal.domains computation scratchDomains name).width sizes)
      (Internal.readOnly computation) initial
      (by intro name; fin_cases name <;> rfl)
      (by intro name readonly; fin_cases name <;> first | rfl | contradiction)
      True.intro
      (by
        intro name readonly
        fin_cases name
        · exact represented.1 (Internal.inputTape computation false) rfl
        · exact represented.1 (Internal.inputTape computation true) rfl
        · contradiction)
      (by intro name writable; exact represented.region (wiring name))
      (by intro parameter; cases parameter)
  let output : Outputs (Internal.domains computation scratchDomains)
      (Internal.outputTapes computation Empty) sizes :=
    fun _ => operation sizes (arguments false) (arguments true)
  refine ⟨ticks, output, final, cost, trace, ⟨True.intro, rfl⟩, ?_⟩
  intro name
  cases name
  exact (canonical ()).trans (congrArg (encoded outputDomain sizes) correct)

/-- A unary specialization-fixed predicate returns a single Boolean. -/
noncomputable def finitePredicate (domain : EncodedDomain.{0, 0} Empty)
    (predicate : ∀ sizes, domain.Carrier sizes → Bool) : Computation Empty Unit :=
  unaryMap domain EncodedDomain.booleans (fun _ _ => True)
    (fun sizes value => predicate sizes value.val)

namespace Realizable.Internal

private def predicateLayout : Fin 3 ≃ Empty ⊕ (Unit ⊕ (Unit ⊕ Unit)) where
  toFun | 0 => .inr (.inl ())
        | 1 => .inr (.inr (.inr ()))
        | 2 => .inr (.inr (.inl ()))
  invFun | .inl empty => nomatch empty
         | .inr (.inl _) => 0
         | .inr (.inr (.inl _)) => 2
         | .inr (.inr (.inr _)) => 1
  left_inv name := by fin_cases name <;> rfl
  right_inv name := by
    rcases name with empty | argument | result | scratch
    · exact Empty.elim empty
    · cases argument; rfl
    · cases result; rfl
    · cases scratch; rfl

end Realizable.Internal

open Realizable.Internal in
/-- The singleton workspace is private and has no mathematical return contract. -/
theorem finitePredicate_realizable (domain : EncodedDomain.{0, 0} Empty)
    (predicate : ∀ sizes, domain.Carrier sizes → Bool) :
    (finitePredicate domain predicate).Realizable := by
  let computation := finitePredicate domain predicate
  let scratchDomains : Unit → EncodedDomain Empty := fun _ => StandardFinitePredicate.unitDomain
  have domainsEqual (name : Fin 3) : domains computation scratchDomains (predicateLayout name) =
      StandardFinitePredicate.domains domain name := by fin_cases name <;> rfl
  let values name sizes := Equiv.cast (congrArg (fun domain => domain.Carrier sizes) (domainsEqual name))
  refine ofLayout computation scratchDomains (StandardFinitePredicate.domains domain)
    StandardFinitePredicate.readOnly StandardFiniteTable.sizeTapes StandardFiniteTable.outputTapes
    (StandardFinitePredicate.machine domain predicate) StandardFiniteTable.entry StandardFiniteTable.exit
    _ _ (StandardFinitePredicate.contract domain predicate) predicateLayout.toEmbedding values
    (by intro name sizes; exact congrArg (fun domain => domain.width sizes) (domainsEqual name))
    (by intro name sizes value; fin_cases name <;> rfl)
    (by intro name; fin_cases name <;> rfl) (by intro parameter; cases parameter) () rfl
    (by intro sizes input valid; trivial) ?_
  intro sizes input valid output correct
  exact congrArg (encoded EncodedDomain.booleans sizes) correct

/-- Three separate arguments from one fixed domain compute one mathematical result. -/
def finiteTernary (domain : EncodedDomain.{0, carrierLevel} Empty)
    (operation : ∀ sizes, domain.Carrier sizes → domain.Carrier sizes → domain.Carrier sizes → domain.Carrier sizes) :
    Computation Empty (Fin 3) where
  inputDomains _ := domain
  outputDomain := domain
  precondition _ _ := True
  compute sizes arguments := operation sizes (arguments.val 0) (arguments.val 1) (arguments.val 2)

namespace Realizable.Internal

private def ternaryLayout : Fin 5 ≃ Empty ⊕ (Fin 3 ⊕ (Unit ⊕ Unit)) where
  toFun | 0 => .inr (.inl 0)
        | 1 => .inr (.inl 1)
        | 2 => .inr (.inl 2)
        | 3 => .inr (.inr (.inl ()))
        | 4 => .inr (.inr (.inr ()))
  invFun | .inl empty => nomatch empty
         | .inr (.inl 0) => 0
         | .inr (.inl 1) => 1
         | .inr (.inl 2) => 2
         | .inr (.inr (.inl _)) => 3
         | .inr (.inr (.inr _)) => 4
  left_inv name := by fin_cases name <;> rfl
  right_inv name := by
    rcases name with empty | argument | result | scratch
    · exact Empty.elim empty
    · fin_cases argument <;> rfl
    · cases result; rfl
    · cases scratch; rfl

end Realizable.Internal

open Realizable.Internal in
theorem finiteTernary_realizable (domain : EncodedDomain.{0, carrierLevel} Empty)
    (operation : ∀ sizes, domain.Carrier sizes → domain.Carrier sizes → domain.Carrier sizes → domain.Carrier sizes) :
    (finiteTernary domain operation).Realizable := by
  let computation := finiteTernary domain operation
  let scratchDomains : Unit → EncodedDomain Empty := fun _ => domain
  have domainsEqual (name : Fin 5) : domains computation scratchDomains (ternaryLayout name) = domain := by
    fin_cases name <;> rfl
  let values name sizes := Equiv.cast (congrArg (fun domain => domain.Carrier sizes) (domainsEqual name))
  refine ofLayout computation scratchDomains (StandardRowCombine.domains domain)
    StandardRowCombine.readOnly StandardRowCombine.sizeTapes StandardRowCombine.outputTapes
    (StandardRowCombine.algorithm domain (fun sizes first second third =>
      (operation sizes first second third, operation sizes first second third)))
    StandardRowCombine.entry StandardRowCombine.exit _ _ (StandardRowCombine.contract domain _)
    ternaryLayout.toEmbedding values
    (by intro name sizes; exact congrArg (fun domain => domain.width sizes) (domainsEqual name))
    (by intro name sizes value; fin_cases name <;> rfl)
    (by intro name; fin_cases name <;> rfl) (by intro parameter; cases parameter) false rfl
    (by intro sizes input valid; trivial) ?_
  intro sizes input valid output correct
  exact congrArg (encoded domain sizes) (congrArg Prod.fst correct)

end Polytime2.Computation
