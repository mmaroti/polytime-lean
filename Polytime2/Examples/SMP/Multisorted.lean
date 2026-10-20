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

import Polytime2.Examples.SMP.SI
import Polytime2.Computation.Records
import Polytime2.Arrays.NamedTransform
import Polytime2.TM0.Computation

/-! # Exact-size multisorted SMP inputs

The catalogue and its order are specialization data. There is one public size
per sort and one generator count. Ordinary records and arrays encode the
mathematical products directly; no inactive coordinates or sort tags occur.
Preparation is a predicate on this input and encoded dependency masks, independent
of the original algebra or of any algorithm producing the instance.
-/

namespace Polytime2.SMP.Multisorted

open FirstOrder FirstOrder.Language
open Polytime2.Computation

variable {sortCount : ℕ}

/-- Sort multiplicities are named on the left; the generator count is on the
right. -/
abbrev Parameter (sortCount : ℕ) := Fin sortCount ⊕ Unit

/-- A coordinate has its catalogue sort and its exact sort-local position. -/
abbrev Coordinate (sizes : Parameter sortCount → ℕ) :=
  Σ sort : Fin sortCount, Fin (sizes (.inl sort))

/-- The ordinary mathematical product of the catalogue powers. -/
abbrev Tuple (Carrier : Fin sortCount → Type) (sizes : Parameter sortCount → ℕ) :=
  ∀ sort : Fin sortCount, Fin (sizes (.inl sort)) → Carrier sort

/-- Generators followed by the target; zero generators and empty products are
allowed. -/
abbrev Input (Carrier : Fin sortCount → Type) (sizes : Parameter sortCount → ℕ) :=
  (Fin (sizes (.inr ())) → Tuple Carrier sizes) × Tuple Carrier sizes

/-- Boolean masks are runtime dependency sets, not proof-only coordinate
indices. -/
abbrev Dependencies (sizes : Parameter sortCount → ℕ) :=
  ∀ sort : Fin sortCount, Fin (sizes (.inl sort)) →
    ∀ child : Fin sortCount, Fin (sizes (.inl child)) → Bool

section Encoding

variable {Carrier : Fin sortCount → Type} {cardinality : Fin sortCount → ℕ}
variable (enumeration : ∀ sort, Carrier sort ≃ Fin (cardinality sort))

/-- Each sort contributes exactly its declared number of scalar encodings. -/
noncomputable def tupleDomain : EncodedDomain (Parameter sortCount) :=
  EncodedDomain.record sortCount (fun sort =>
    (EncodedDomain.fixed (enumeration sort)).array (.inl sort))

/-- Each coordinate stores its target and generator column together. The
carrier remains ordinary generators and a target, with no runtime transpose. -/
noncomputable def inputDomain : EncodedDomain (Parameter sortCount) :=
  (EncodedDomain.record sortCount (fun sort =>
    let scalar := EncodedDomain.fixed (enumeration sort)
    (scalar.prod (scalar.array (.inr ()))).array (.inl sort))).reindex
      (Input Carrier) (fun _ =>
        { toFun := fun input sort position =>
            (input.2 sort position, fun generator => input.1 generator sort position)
          invFun := fun columns =>
            ((fun generator sort position => (columns sort position).2 generator),
              fun sort position => (columns sort position).1)
          left_inv := by intro input; rfl
          right_inv := by intro columns; rfl })

/-- The domain carrier is the mathematical input, without a representation
layer. -/
theorem inputDomain_carrier (sizes : Parameter sortCount → ℕ) :
    (inputDomain enumeration).Carrier sizes = Input Carrier sizes := rfl

/-- The exact width is polynomial in all multiplicities and the generator count.
-/
theorem inputDomain_widthPolynomial :
    (inputDomain enumeration).widthPolynomial =
      (MvPolynomial.X (.inr ()) + 1) *
        ∑ sort, MvPolynomial.X (.inl sort) * MvPolynomial.C (Nat.clog 2 (cardinality sort)) := by
  change (EncodedDomain.record sortCount (fun sort =>
    let scalar : EncodedDomain (Parameter sortCount) := EncodedDomain.fixed (enumeration sort)
    (scalar.prod (scalar.array (.inr ()))).array (.inl sort))).widthPolynomial = _
  rw [EncodedDomain.record_widthPolynomial]
  simp only [EncodedDomain.prod, EncodedDomain.ofCodec, EncodedDomain.array, EncodedDomain.fixed]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro sort member
  ring

/-- Extract targets by projecting each coordinate column, using the shared
array transformer. -/
noncomputable def readTarget : Computation (Parameter sortCount) Unit where
  inputDomains _ := inputDomain enumeration
  outputDomain := tupleDomain enumeration
  precondition _ _ := True
  compute _ arguments := (arguments.val ()).2

theorem readTarget_realizable : (readTarget enumeration).Realizable := by
  let scalar := fun sort : Fin sortCount =>
    (EncodedDomain.fixed (enumeration sort) : EncodedDomain (Parameter sortCount))
  let columns := fun sort => ((scalar sort).prod ((scalar sort).array (.inr ()))).array (.inl sort)
  let storage := EncodedDomain.record sortCount columns
  have view := encodingMap_realizable (inputDomain enumeration) storage
    (fun _ input sort position => (input.2 sort position, fun generator => input.1 generator sort position))
    (by intros; rfl) (by intros; rfl)
  apply Realizable.recordOutputs
  intro sort
  have selected := view.followedBy (recordProjection_realizable sortCount columns sort) rfl (by intros; trivial)
  exact selected.followedBy
    (mapArrayAtParameter_realizable ((scalar sort).prod ((scalar sort).array (.inr ()))) (scalar sort)
      (.inl sort) (fun _ column => column.1)
      (pairProjection_realizable (scalar sort) ((scalar sort).array (.inr ())) false))
    rfl (by intros; trivial)

/-- Standalone export uses precisely the specialization's sort sizes and
generator count. -/
theorem readTarget_tm0 : (readTarget enumeration).TM0Realizable :=
  (readTarget_realizable enumeration).tm0

@[simp] theorem readTarget_compute (sizes : Parameter sortCount → ℕ) (input : Input Carrier sizes) :
    (readTarget enumeration).compute sizes ⟨(fun _ => input), trivial⟩ = input.2 := rfl

end Encoding

/-- A quadratic-size bit mask records every dependency set at exact sort
sizes. Rectangular blocks are grouped by their fixed pair of sorts. -/
noncomputable def dependencyDomain (sortCount : ℕ) : EncodedDomain (Parameter sortCount) :=
  (EncodedDomain.record sortCount (fun parent =>
    EncodedDomain.record sortCount (fun child =>
      (EncodedDomain.booleans.array (.inl child)).array (.inl parent)))).reindex
      (Dependencies) (fun _ =>
        { toFun := fun masks parent child position childPosition => masks parent position child childPosition
          invFun := fun blocks parent position child childPosition => blocks parent child position childPosition
          left_inv := by intro masks; rfl
          right_inv := by intro blocks; rfl })

/-- No bounded-index labels or padding intervene between masks and their
mathematical data. -/
theorem dependencyDomain_carrier (sizes : Parameter sortCount → ℕ) :
    (dependencyDomain sortCount).Carrier sizes = Dependencies sizes := rfl

/-- A prepared input carries its ordinary SMP instance and runtime dependency
masks. -/
noncomputable def preparedDomain {Carrier : Fin sortCount → Type} {cardinality : Fin sortCount → ℕ}
    (enumeration : ∀ sort, Carrier sort ≃ Fin (cardinality sort)) : EncodedDomain (Parameter sortCount) :=
  (inputDomain enumeration).prod (dependencyDomain sortCount)

/-- Access a prepared target through public composition, with no conversion-
specific layout. -/
noncomputable def readPreparedTarget {Carrier : Fin sortCount → Type} {cardinality : Fin sortCount → ℕ}
    (enumeration : ∀ sort, Carrier sort ≃ Fin (cardinality sort)) : Computation (Parameter sortCount) Unit :=
  (pairProjection (inputDomain enumeration) (dependencyDomain sortCount) false).followedBy
    (readTarget enumeration) rfl (by intros; trivial)

theorem readPreparedTarget_realizable {Carrier : Fin sortCount → Type} {cardinality : Fin sortCount → ℕ}
    (enumeration : ∀ sort, Carrier sort ≃ Fin (cardinality sort)) :
    (readPreparedTarget enumeration).Realizable :=
  (pairProjection_realizable _ _ false).followedBy (readTarget_realizable enumeration) rfl (by intros; trivial)

/-- The set of selected coordinates is recovered directly from the encoded mask.
-/
def dependencySet {sizes : Parameter sortCount → ℕ} (dependencies : Dependencies sizes)
    (coordinate : Coordinate sizes) : Set (Coordinate sizes) :=
  {child | dependencies coordinate.1 coordinate.2 child.1 child.2 = true}

section Preparation

variable {L : Language.{0, 0}} [L.IsAlgebraic]
variable {Carrier : Fin sortCount → Type} [∀ sort, L.Structure (Carrier sort)]
variable {sizes : Parameter sortCount → ℕ}

/-- The generated relation uses the original common signature on the product. -/
def generated (input : Input Carrier sizes) : L.Substructure (Tuple Carrier sizes) :=
  Substructure.closure L (Set.range input.1)

/-- Project the generated relation onto the actual distinct dependency
coordinates. -/
def projectedDependencies (input : Input Carrier sizes) (dependencies : Dependencies sizes)
    (coordinate : Coordinate sizes) :=
  (generated (L := L) input).map
    (assemble (fun child : dependencySet dependencies coordinate =>
      (projection child.val.2).comp (projection child.val.1)))

/-- A prepared input has a subdirect generated relation, ordered SI sorts, and
bounded earlier dependency masks. The full graph isomorphisms agree with fixed
catalogue lookups; they are correctness proofs, not runtime function oracles.
The lookup may be undefined for sort pairs not used by a dependency mask. -/
def IsPrepared [∀ sort, Finite (Carrier sort)] (monolith : ∀ sort, Congruence L (Carrier sort))
    (graph : ∀ parent child, Quotient (monolith parent).val → Option (Carrier child))
    (dependencyBound : ℕ) (input : Input Carrier sizes) (dependencies : Dependencies sizes) : Prop :=
  (∀ sort, IsLeast {relation : Congruence L (Carrier sort) | relation.val ≠ ⊥}
    (monolith sort)) ∧
  Monotone (fun sort => Nat.card (Congruence L (Carrier sort))) ∧
  (∀ coordinate : Coordinate sizes, ∀ value : Carrier coordinate.1,
    ∃ tuple ∈ generated (L := L) input, tuple coordinate.1 coordinate.2 = value) ∧
  ∀ coordinate : Coordinate sizes,
    Nat.card (dependencySet dependencies coordinate) ≤ dependencyBound ∧
    (∀ child : dependencySet dependencies coordinate,
      toLex (child.val.1.val, child.val.2.val) < toLex (coordinate.1.val, coordinate.2.val)) ∧
    (Nat.card (Congruence L (Carrier coordinate.1)) = 2 →
      dependencySet dependencies coordinate = ∅) ∧
    ∃ equivalence : Quotient (monolith coordinate.1).val ≃[L]
        projectedDependencies (L := L) input dependencies coordinate,
      (∀ value (child : dependencySet dependencies coordinate),
        some ((equivalence value).val child) = graph coordinate.1 child.val.1 value) ∧
      (fun tuple : Tuple Carrier sizes =>
        ((fun child : dependencySet dependencies coordinate => tuple child.val.1 child.val.2),
          tuple coordinate.1 coordinate.2)) '' (generated (L := L) input : Set (Tuple Carrier sizes)) =
        {pair | pair.1 = (equivalence
          (quotientMap (monolith coordinate.1) pair.2)).val}

/-- The mathematical SMP question is membership of the target in the generated
relation. -/
def IsMember (input : Input Carrier sizes) : Prop := input.2 ∈ generated (L := L) input

end Preparation

end Polytime2.SMP.Multisorted
