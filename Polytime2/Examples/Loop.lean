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

import Polytime2.Computation.While

/-! # A guarded countdown using only public mathematical certificates

The counter has fixed binary capacity. Its initial value is at most the size
parameter, so decreasing that value supplies a polynomial iteration bound.
-/

namespace Polytime2.Examples.Loop

open Polytime2.Computation

private def admissible (sizes : Unit → ℕ) (value : Fin (2 ^ sizes ())) : Prop :=
  value.val ≤ sizes ()

private def nonzero (sizes : Unit → ℕ) (value : Fin (2 ^ sizes ())) : Bool :=
  decide (0 < value.val)

private def predecessor (sizes : Unit → ℕ)
    (value : {value : Fin (2 ^ sizes ()) // admissible sizes value ∧ nonzero sizes value = true}) :
    Fin (2 ^ sizes ()) :=
  ⟨value.val.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) value.val.isLt⟩

/-- The answer is zero; the implementation reaches it by a genuine while loop. -/
def countdown : Polytime2.Computation Unit Unit := unaryMap
  (EncodedDomain.binaryNaturals ()) (EncodedDomain.binaryNaturals ()) admissible
  (fun sizes _ => (0 : Fin (2 ^ sizes ())))

theorem countdown_realizable : countdown.Realizable := by
  apply Computation.Realizable.whileLoop (EncodedDomain.binaryNaturals ())
    admissible nonzero predecessor
    (fun sizes _ => (0 : Fin (2 ^ sizes ()))) (fun _ value => value.val)
  · exact counterNonzero_realizable.withPrecondition
      (fun sizes arguments => admissible sizes (arguments ()))
      (by intro sizes arguments valid; trivial)
  · exact (counterDecrement_realizable ()).withPrecondition
      (fun sizes arguments => admissible sizes (arguments ()) ∧ nonzero sizes (arguments ()) = true)
      (by
        intro sizes arguments valid
        change 0 < (arguments ()).val
        exact of_decide_eq_true valid.2)
  · intro sizes value
    change value.val.val - 1 ≤ sizes ()
    have bound := value.property.1
    exact le_trans (Nat.sub_le _ _) bound
  · intro sizes value
    change value.val.val - 1 < value.val.val
    have positive : 0 < value.val.val := of_decide_eq_true value.property.2
    omega
  · intro sizes value
    rfl
  · intro sizes value stopped
    apply Fin.ext
    change 0 = value.val.val
    have zero : ¬0 < value.val.val := of_decide_eq_false stopped
    omega
  · exact ⟨MvPolynomial.X (), by intro sizes value valid; simpa only [MvPolynomial.eval_X, admissible] using valid⟩

example : (countdown.compute (fun _ => 3)
    ⟨(fun _ => (3 : Fin 8)), by change 3 ≤ 3; decide⟩ : Fin 8) = (0 : Fin 8) := rfl
example : (countdown.compute (fun _ => 0)
    ⟨(fun _ => (0 : Fin 1)), by change 0 ≤ 0; decide⟩ : Fin 1) = (0 : Fin 1) := rfl

end Polytime2.Examples.Loop
