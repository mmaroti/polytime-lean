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

import Polytime2.Computation.Composition
import Polytime2.Arithmetic.CounterOperations
import Polytime2.Primitives.ConstantOperations
import Polytime2.Primitives.FiniteOperations

/-! # Public specifications compose without exposing implementation witnesses -/

namespace Polytime2.Examples.Computation

open Polytime2.Computation

noncomputable def copiedIncrement : Polytime2.Computation Unit Unit :=
  (copy (EncodedDomain.binaryNaturals ())).followedBy (counterIncrement ()) rfl
    (by intro sizes arguments valid; trivial)

/-- This proof depends only on the two public existence theorems. -/
theorem copiedIncrement_realizable : copiedIncrement.Realizable :=
  (copy_realizable (EncodedDomain.binaryNaturals ())).followedBy
    (counterIncrement_realizable ()) rfl (by intro sizes arguments valid; trivial)

noncomputable def copiedDoubleIncrement : Polytime2.Computation Unit Unit :=
  copiedIncrement.followedBy (counterIncrement ()) rfl
    (by intro sizes arguments valid; trivial)

/-- Nested composition reuses an implementation that already has private scratch. -/
theorem copiedDoubleIncrement_realizable : copiedDoubleIncrement.Realizable :=
  copiedIncrement_realizable.followedBy (counterIncrement_realizable ()) rfl
    (by intro sizes arguments valid; trivial)

example : (copiedDoubleIncrement.compute (fun _ => 3)
    ⟨(fun _ => (5 : Fin 8)), True.intro⟩ : Fin 8) = (7 : Fin 8) := rfl
example : (copiedDoubleIncrement.compute (fun _ => 0)
    ⟨(fun _ => (0 : Fin 1)), True.intro⟩ : Fin 1) = (0 : Fin 1) := rfl

noncomputable def copyWithRoom : Polytime2.Computation Unit Unit :=
  (copy (EncodedDomain.binaryNaturals ())).withPrecondition
    (fun sizes arguments => (arguments ()).val + 1 < 2 ^ sizes ())
    (by intro sizes arguments valid; trivial)

noncomputable def incrementWithRoom : Polytime2.Computation Unit Unit :=
  (counterIncrement ()).withPrecondition
    (fun sizes arguments => (arguments ()).val + 1 < 2 ^ sizes ())
    (by intro sizes arguments valid; trivial)

/-- The next precondition follows from mathematical copying, with no tape proof. -/
example : (copyWithRoom.followedBy incrementWithRoom rfl
    (by intro sizes arguments valid; exact valid)).Realizable := by
  apply Computation.Realizable.followedBy
  · exact (copy_realizable (EncodedDomain.binaryNaturals ())).withPrecondition _ _
  · exact (counterIncrement_realizable ()).withPrecondition _ _

noncomputable def threeElements : EncodedDomain Empty := EncodedDomain.fixed (Equiv.refl (Fin 3))

/-- The two named inputs have different mathematical carriers and separate tapes. -/
noncomputable def conditionalIncrement : Polytime2.Computation Empty Bool :=
  finiteTable threeElements EncodedDomain.booleans threeElements
    (fun _ (value : Fin 3) (flag : Bool) => if flag then value + 1 else value)

theorem conditionalIncrement_realizable : conditionalIncrement.Realizable :=
  finiteTable_realizable threeElements EncodedDomain.booleans threeElements _

/-- Sequencing preserves both named arguments of the first computation. -/
example : (conditionalIncrement.followedBy (copy threeElements) rfl
    (by intro sizes arguments _valid; trivial)).Realizable :=
  conditionalIncrement_realizable.followedBy (copy_realizable threeElements) rfl
    (by intro sizes arguments valid; trivial)

example : (conditionalIncrement.compute Empty.elim
    ⟨(fun | false => (2 : Fin 3) | true => true), True.intro⟩ : Fin 3) = (0 : Fin 3) := rfl

/-- No mathematical arguments are needed to initialize and increment a counter. -/
noncomputable def initializedIncrement : Polytime2.Computation Unit Empty :=
  (counterZero ()).followedBy (counterIncrement ()) rfl
    (by intro sizes arguments valid; trivial)

theorem initializedIncrement_realizable : initializedIncrement.Realizable :=
  (counterZero_realizable ()).followedBy (counterIncrement_realizable ()) rfl
    (by intro sizes arguments valid; trivial)

example : (initializedIncrement.compute (fun _ => 3)
    ⟨(fun argument => nomatch argument), True.intro⟩ : Fin 8) = (1 : Fin 8) := rfl
example : (initializedIncrement.compute (fun _ => 0)
    ⟨(fun argument => nomatch argument), True.intro⟩ : Fin 1) = (0 : Fin 1) := rfl

example : (constant threeElements (fun _ => (2 : Fin 3))).Realizable :=
  constant_realizable threeElements (fun _ => (2 : Fin 3))

end Polytime2.Examples.Computation
