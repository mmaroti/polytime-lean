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

namespace Realizable.Internal

private def tablePlacement : PublicTape Empty Bool ↪ Fin 3 :=
  ⟨(fun role => match role with
    | .inl empty => nomatch empty
    | .inr (.inl false) => 0 | .inr (.inl true) => 1 | .inr (.inr _) => 2), by
    intro first second equal
    fin_cases first <;> fin_cases second <;> first | rfl | cases equal⟩

end Realizable.Internal

open Realizable.Internal in
/-- The existing finite-table machine certifies a public binary computation. -/
theorem finiteTable_realizable
    (firstDomain secondDomain outputDomain : EncodedDomain.{0, carrierLevel} Empty)
    (operation : ∀ sizes, firstDomain.Carrier sizes → secondDomain.Carrier sizes →
      outputDomain.Carrier sizes) : (finiteTable firstDomain secondDomain outputDomain operation).Realizable := by
  refine ofNamedLayout (finiteTable firstDomain secondDomain outputDomain operation)
    (StandardFiniteTable.domains firstDomain secondDomain outputDomain) StandardFiniteTable.readOnly
    StandardFiniteTable.sizeTapes StandardFiniteTable.outputTapes
    (StandardFiniteTable.algorithm firstDomain secondDomain outputDomain operation)
    StandardFiniteTable.entry StandardFiniteTable.exit _ _
    (StandardFiniteTable.contract firstDomain secondDomain outputDomain operation) tablePlacement
    (by intro role; fin_cases role <;> rfl) (by intro role; fin_cases role <;> rfl)
    (by intro name outside; fin_cases name <;> first
      | rfl
      | exact False.elim (outside ⟨.inr (.inl false), rfl⟩)
      | exact False.elim (outside ⟨.inr (.inl true), rfl⟩))
    (by intro empty; cases empty) () rfl (by intro sizes input valid; trivial) ?_
  intro sizes input valid output correct
  exact congrArg (encoded outputDomain sizes) correct

/-- A unary specialization-fixed predicate returns a single Boolean. -/
noncomputable def finitePredicate (domain : EncodedDomain.{0, 0} Empty)
    (predicate : ∀ sizes, domain.Carrier sizes → Bool) : Computation Empty Unit :=
  unaryMap domain EncodedDomain.booleans (fun _ _ => True)
    (fun sizes value => predicate sizes value.val)

namespace Realizable.Internal

private def predicatePlacement : PublicTape Empty Unit ↪ Fin 3 :=
  ⟨(fun role => match role with
    | .inl empty => nomatch empty
    | .inr (.inl _) => 0 | .inr (.inr _) => 2), by
    intro first second equal
    fin_cases first <;> fin_cases second <;> first | rfl | cases equal⟩

end Realizable.Internal

open Realizable.Internal in
/-- The singleton workspace is private and has no mathematical return contract. -/
theorem finitePredicate_realizable (domain : EncodedDomain.{0, 0} Empty)
    (predicate : ∀ sizes, domain.Carrier sizes → Bool) :
    (finitePredicate domain predicate).Realizable := by
  refine ofNamedLayout (finitePredicate domain predicate) (StandardFinitePredicate.domains domain)
    StandardFinitePredicate.readOnly StandardFiniteTable.sizeTapes StandardFiniteTable.outputTapes
    (StandardFinitePredicate.machine domain predicate) StandardFiniteTable.entry StandardFiniteTable.exit
    _ _ (StandardFinitePredicate.contract domain predicate) predicatePlacement
    (by intro role; fin_cases role <;> rfl) (by intro role; fin_cases role <;> rfl)
    (by intro name outside; fin_cases name <;> first
      | rfl | exact False.elim (outside ⟨.inr (.inl ()), rfl⟩))
    (by intro empty; cases empty) () rfl (by intro sizes input valid; trivial) ?_
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

private def ternaryPlacement : PublicTape Empty (Fin 3) ↪ Fin 5 :=
  ⟨(fun role => match role with
    | .inl empty => nomatch empty
    | .inr (.inl name) => ⟨name.val, by omega⟩ | .inr (.inr _) => 3), by
    intro first second equal
    fin_cases first <;> fin_cases second <;> first | rfl | cases equal⟩

end Realizable.Internal

open Realizable.Internal in
theorem finiteTernary_realizable (domain : EncodedDomain.{0, carrierLevel} Empty)
    (operation : ∀ sizes, domain.Carrier sizes → domain.Carrier sizes → domain.Carrier sizes → domain.Carrier sizes) :
    (finiteTernary domain operation).Realizable := by
  refine ofNamedLayout (finiteTernary domain operation) (StandardRowCombine.domains domain)
    StandardRowCombine.readOnly StandardRowCombine.sizeTapes StandardRowCombine.outputTapes
    (StandardRowCombine.algorithm domain (fun sizes first second third =>
      (operation sizes first second third, operation sizes first second third)))
    StandardRowCombine.entry StandardRowCombine.exit _ _ (StandardRowCombine.contract domain _)
    ternaryPlacement (by intro role; fin_cases role <;> rfl) (by intro role; fin_cases role <;> rfl)
    (by intro name outside; fin_cases name <;> first
      | rfl
      | exact False.elim (outside ⟨.inr (.inl 0), rfl⟩)
      | exact False.elim (outside ⟨.inr (.inl 1), rfl⟩)
      | exact False.elim (outside ⟨.inr (.inl 2), rfl⟩))
    (by intro empty; cases empty) false rfl (by intro sizes input valid; trivial) ?_
  intro sizes input valid output correct
  exact congrArg (encoded domain sizes) (congrArg Prod.fst correct)

end Polytime2.Computation
