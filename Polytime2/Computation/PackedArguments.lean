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

import Polytime2.Computation.Records

/-! # Calling a two-argument computation from a pair tape -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

universe carrierLevel
variable {Parameter : Type} [Fintype Parameter]

/-- Pack two immutable input tapes into one pair without changing their meaning. -/
noncomputable def withPairArgument (computation : Computation.{carrierLevel} Parameter Bool) :
    Computation Parameter Unit where
  inputDomains _ := (computation.inputDomains false).prod (computation.inputDomains true)
  outputDomain := computation.outputDomain
  precondition sizes arguments := computation.precondition sizes
    (fun | false => (arguments ()).1 | true => (arguments ()).2)
  compute sizes arguments := computation.compute sizes
    ⟨(fun | false => (arguments.val ()).1 | true => (arguments.val ()).2), arguments.property⟩

/-- Projection and composition account for unpacking, including partial calls. -/
theorem Realizable.withPairArgument {computation : Computation.{carrierLevel} Parameter Bool}
    (realizable : computation.Realizable) : computation.withPairArgument.Realizable := by
  let packed := computation.withPairArgument
  let left := computation.inputDomains false
  let right := computation.inputDomains true
  have first := (pairProjection_realizable left right false).withPrecondition packed.precondition
    (by intros; trivial)
  let domains : Unit ⊕ Unit → EncodedDomain Parameter := Sum.elim packed.inputDomains (fun _ => left)
  have second := ((pairProjection_realizable left right true).withArguments domains
    ⟨Sum.inl, Sum.inl_injective⟩ (by intro name; cases name; rfl)).withPrecondition
      (fun sizes arguments => computation.precondition sizes
        (fun | false => arguments (.inr ()) | true => (arguments (.inl ())).2))
      (by intros; trivial)
  let finalDomains : (Unit ⊕ Unit) ⊕ Unit → EncodedDomain Parameter :=
    Sum.elim domains (fun _ => right)
  have call := realizable.withArguments finalDomains
    ⟨(fun choice => if choice then (Sum.inr () : (Unit ⊕ Unit) ⊕ Unit) else .inl (.inr ())), by
      intro first second equal; cases first <;> cases second <;> simp_all⟩
    (by intro choice; cases choice <;> rfl)
  have continuation := second.letThen call (fun _ => rfl) rfl (by
    intro sizes arguments valid
    change computation.precondition sizes _ at valid ⊢
    convert valid using 1
    funext choice
    cases choice <;> rfl)
  have complete := first.letThen continuation (fun _ => rfl) rfl (by
    intro sizes arguments valid
    exact valid)
  exact complete.withSpecification packed.precondition packed.compute (by intros; assumption)
    (by
      intro sizes arguments valid
      change computation.compute sizes _ = computation.compute sizes _
      congr 1
      apply Subtype.ext
      funext choice
      cases choice <;> rfl)

end Polytime2.Computation
