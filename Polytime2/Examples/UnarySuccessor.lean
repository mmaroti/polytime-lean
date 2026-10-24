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

import Polytime2.Arithmetic.UnarySuccessor
import Polytime2.TM0.Computation

/-! # Array appending and bounded unary rank increments

Empty arrays append without a default element. Rank zero advances to one,
and the last available rank advances to capacity; a full rank is inadmissible.
-/

namespace Polytime2.Examples.UnarySuccessor

open Polytime2.Computation Polytime2.EncodedDomain

example {Parameter : Type} [Fintype Parameter] (capacity : MvPolynomial Parameter ℕ) :
    (boundedUnarySuccessor capacity).TM0Realizable := (boundedUnarySuccessor_realizable capacity).tm0

example {Parameter : Type} [Fintype Parameter] (element : EncodedDomain Parameter)
    (length : MvPolynomial Parameter ℕ) :
    (arraySnoc element length).TM0Realizable := (arraySnoc_realizable element length).tm0

example : ((boundedUnarySuccessor (Parameter := Empty) 3).compute Empty.elim
    ⟨(fun _ => ⟨0, by norm_num⟩), by dsimp only [boundedUnarySuccessor, unaryMap]; norm_num⟩).val = 1 := rfl

example : ((boundedUnarySuccessor (Parameter := Empty) 3).compute Empty.elim
    ⟨(fun _ => ⟨2, by norm_num⟩), by dsimp only [boundedUnarySuccessor, unaryMap]; norm_num⟩).val = 3 := rfl

example : ¬(boundedUnarySuccessor (Parameter := Empty) 3).precondition Empty.elim
    (fun _ => ⟨3, by norm_num⟩) := by dsimp only [boundedUnarySuccessor, unaryMap]; norm_num

example : ¬(boundedUnarySuccessor (Parameter := Empty) 0).precondition Empty.elim
    (fun _ => ⟨0, by norm_num⟩) := by dsimp only [boundedUnarySuccessor, unaryMap]; norm_num

example : (arraySnoc (Parameter := Empty) booleans 0).compute Empty.elim
    ⟨(fun choice => match choice with | false => fun _ => false | true => true), trivial⟩
    ⟨0, by norm_num⟩ = true := by
  dsimp only [arraySnoc]
  norm_num [snocValues, Fin.snoc]
  exact eq_of_heq (cast_heq _ _)

end Polytime2.Examples.UnarySuccessor
