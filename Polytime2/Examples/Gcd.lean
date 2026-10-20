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
import Polytime2.Arithmetic.GcdOperations

/-! # Gcd through its public mathematical specification -/

namespace Polytime2.Examples.Gcd

open Polytime2.Computation

example : gcd.Realizable := gcd_realizable

/-- A client may copy the gcd without knowing any private tape or controller. -/
noncomputable def copiedGcd : Polytime2.Computation Unit Bool :=
  gcd.followedBy (copy (EncodedDomain.binaryNaturals ())) rfl
    (by intro sizes arguments valid; trivial)

theorem copiedGcd_realizable : copiedGcd.Realizable :=
  gcd_realizable.followedBy (copy_realizable (EncodedDomain.binaryNaturals ())) rfl
    (by intro sizes arguments valid; trivial)

example (sizes : Unit → ℕ) (arguments : gcd.Arguments sizes)
    (valid : gcd.precondition sizes arguments) :
    (gcd.compute sizes ⟨arguments, valid⟩).val =
      Nat.gcd (arguments false).val (arguments true).val := rfl

example : (gcd.compute (fun _ => 6)
    ⟨(fun | false => (48 : Fin 64) | true => (18 : Fin 64)), by trivial⟩ : Fin 64) = (6 : Fin 64) := rfl
example : (gcd.compute (fun _ => 7)
    ⟨(fun | false => (0 : Fin 128) | true => (37 : Fin 128)), by trivial⟩ : Fin 128) = (37 : Fin 128) := rfl
example : (gcd.compute (fun _ => 6)
    ⟨(fun | false => (37 : Fin 64) | true => (0 : Fin 64)), by trivial⟩ : Fin 64) = (37 : Fin 64) := rfl
example : (gcd.compute (fun _ => 0)
    ⟨(fun _ => (0 : Fin 1)), by trivial⟩ : Fin 1) = (0 : Fin 1) := rfl

example : (gcd.compute (fun _ => 4)
    ⟨(fun | false => (13 : Fin 16) | true => (15 : Fin 16)), by trivial⟩ : Fin 16) =
      (1 : Fin 16) := rfl
example : (gcd.compute (fun _ => 1)
    ⟨(fun | false => (0 : Fin 2) | true => (1 : Fin 2)), by trivial⟩ : Fin 2) =
      (1 : Fin 2) := rfl

end Polytime2.Examples.Gcd
