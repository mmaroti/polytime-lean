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

import Polytime2.Examples.SMP.Multisorted
import Mathlib.ModelTheory.Algebra.Ring.Basic
import Mathlib.Data.ZMod.Basic

/-! # Exact multisorted SMP inputs over two different finite rings

The specialization has two sorts and three independent size tapes. The second
example has no sorts, covering the empty product and zero generators.
-/

namespace Polytime2.SMP.MultisortedExample

open FirstOrder FirstOrder.Language
open Multisorted

local instance : FirstOrder.Ring.CompatibleRing (ZMod 2) := FirstOrder.Ring.compatibleRingOfRing (ZMod 2)
local instance : FirstOrder.Ring.CompatibleRing (ZMod 4) := FirstOrder.Ring.compatibleRingOfRing (ZMod 4)

private def Carrier : Fin 2 → Type := ![ZMod 2, ZMod 4]
private def cardinality : Fin 2 → ℕ := ![2, 4]

private instance carrierStructure (sort : Fin 2) : Language.ring.Structure (Carrier sort) :=
  Fin.cases (inferInstance : Language.ring.Structure (ZMod 2))
    (Fin.cases (inferInstance : Language.ring.Structure (ZMod 4)) (fun index => Fin.elim0 index)) sort

private instance carrierFinite (sort : Fin 2) : Finite (Carrier sort) :=
  Fin.cases (inferInstance : Finite (ZMod 2))
    (Fin.cases (inferInstance : Finite (ZMod 4)) (fun index => Fin.elim0 index)) sort

private noncomputable def enumeration : ∀ sort, Carrier sort ≃ Fin (cardinality sort) :=
  Fin.cases (Fintype.equivFin (ZMod 2))
    (Fin.cases (Fintype.equivFin (ZMod 4)) (fun sort => Fin.elim0 sort))

/-- The public carrier is literally generators and a target in the product of
powers. -/
example (sizes : Parameter 2 → ℕ) :
    (inputDomain enumeration).Carrier sizes =
      ((Fin (sizes (.inr ())) → ∀ sort : Fin 2, Fin (sizes (.inl sort)) → Carrier sort) ×
        (∀ sort : Fin 2, Fin (sizes (.inl sort)) → Carrier sort)) := rfl

example : (inputDomain enumeration).widthPolynomial =
    (MvPolynomial.X (.inr ()) + 1) * (MvPolynomial.X (.inl 0) + 2 * MvPolynomial.X (.inl 1)) := by
  rw [inputDomain_widthPolynomial]
  simp [cardinality, Fin.sum_univ_succ, show Nat.clog 2 2 = 1 by decide,
    show Nat.clog 2 4 = 2 by decide, mul_comm]

/-- Canonical encoding and decoding preserve the original mathematical values.
-/
example (sizes : Parameter 2 → ℕ) (input : Input Carrier sizes) :
    (inputDomain enumeration).decode sizes ((inputDomain enumeration).encode sizes input) = some input :=
  (inputDomain enumeration).decode_encode sizes input

/-- Any absent sort has no coordinate values to supply. -/
example (sizes : Parameter 2 → ℕ) (absent : sizes (.inl 1) = 0) :
    Subsingleton (Fin (sizes (.inl 1)) → Carrier 1) := by
  rw [absent]
  infer_instance

example : (readPreparedTarget enumeration).Realizable := readPreparedTarget_realizable enumeration
example : (readPreparedTarget enumeration).TM0Realizable := (readPreparedTarget_realizable enumeration).tm0

example (sizes : Parameter 2 → ℕ)
    (input : (preparedDomain enumeration).Carrier sizes) :
    (readPreparedTarget enumeration).compute sizes ⟨(fun _ => input), trivial⟩ = input.1.2 := rfl

/-- The SMP question uses generation in the common ring language. -/
example (sizes : Parameter 2 → ℕ) (input : Input Carrier sizes)
    (generator : Fin (sizes (.inr ()))) (target : input.2 = input.1 generator) :
    IsMember (L := Language.ring) input := by
  change input.2 ∈ Substructure.closure Language.ring (Set.range input.1)
  exact Substructure.subset_closure ⟨generator, target.symm⟩

/-- A consumer can require preparation as a mathematical precondition,
independently of the algorithm that produced its input. -/
example (monolith : ∀ sort, Congruence Language.ring (Carrier sort))
    (graph : ∀ parent child, Quotient (monolith parent).val → Option (Carrier child))
    (bound : ℕ) :
    ((readPreparedTarget enumeration).withPrecondition
      (fun _ arguments => IsPrepared monolith graph bound (arguments ()).1 (arguments ()).2)
      (by intros; trivial)).Realizable :=
  (readPreparedTarget_realizable enumeration).withPrecondition _ _

/-- Empty catalogues give width zero even when the generator count is nonzero.
-/
example (sizes : Parameter 0 → ℕ) :
    (inputDomain (Carrier := Fin.elim0) (cardinality := Fin.elim0) (fun sort => Fin.elim0 sort)).width sizes = 0 := by
  simp [EncodedDomain.width, inputDomain_widthPolynomial]

private def EmptyCarrier : Fin 0 → Type := Fin.elim0

private instance emptyStructure (sort : Fin 0) : Language.ring.Structure (EmptyCarrier sort) :=
  Fin.elim0 sort

private instance emptyFinite (sort : Fin 0) : Finite (EmptyCarrier sort) := Fin.elim0 sort

/-- Preparation over the empty catalogue requires no fictitious factors or
dependencies. -/
example (sizes : Parameter 0 → ℕ) (input : Input EmptyCarrier sizes)
    (dependencies : Dependencies sizes) :
    IsPrepared (L := Language.ring) (Carrier := EmptyCarrier)
      (fun sort => Fin.elim0 sort) (fun sort => Fin.elim0 sort) 0 input dependencies := by
  refine ⟨(fun sort => Fin.elim0 sort), ?_, ?_, ?_⟩
  · intro sort; exact Fin.elim0 sort
  · intro coordinate; exact Fin.elim0 coordinate.1
  · intro coordinate; exact Fin.elim0 coordinate.1

/-- Public dependencies are actual finite sets, with no mask conversion. -/
example (sizes : Parameter 2 → ℕ) :
    (dependencyDomain 2).Carrier sizes = (Coordinate sizes → Finset (Coordinate sizes)) := rfl

/-- The finite-set codec retains exactly the old characteristic bits. -/
example (sizes : Parameter 2 → ℕ) (dependencies : Dependencies sizes) :
    EncodedDomain.ArrayEncoding.bits ((dependencyDomain 2).encode sizes dependencies) =
      EncodedDomain.ArrayEncoding.bits ((DependencyEncoding.maskDomain 2).encode sizes
        (DependencyEncoding.equivalence sizes dependencies)) := rfl

example (sizes : Parameter 2 → ℕ) (parent : Coordinate sizes) :
    DependencyEncoding.equivalence sizes (fun _ => ∅)
      parent.1 parent.2 parent.1 parent.2 = false := by
  simp [DependencyEncoding.equivalence]

example (sizes : Parameter 2 → ℕ) (parent child : Coordinate sizes) :
    DependencyEncoding.equivalence sizes (fun _ => {child})
      parent.1 parent.2 child.1 child.2 = true := by
  classical
  simp [DependencyEncoding.equivalence]

end Polytime2.SMP.MultisortedExample
