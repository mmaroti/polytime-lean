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

import Polytime2.Examples.SMP.Congruence

/-! # Factoring algebra homomorphisms through their kernel quotient

Recursive monolith preparation composes fixed quotient maps. Kernel quotients
return those composites to quotients of the original specialized subalgebra.
-/

namespace Polytime2.SMP

open FirstOrder FirstOrder.Language

variable {L : Language.{0, 0}} [L.IsAlgebraic]
variable {Source Target : Type} [L.Structure Source] [L.Structure Target]

/-- Equality of images is a compatible equivalence relation. -/
def kernel (map : Source →[L] Target) : Congruence L Source :=
  pullback map ⟨⊥, compatible_equality⟩

omit [L.IsAlgebraic] in
@[simp] theorem kernel_iff (map : Source →[L] Target) (first second : Source) :
    (kernel map).val first second ↔ map first = map second := Iff.rfl

/-- The induced map uses actual quotient elements, with the original operations. -/
noncomputable def kernelLift (map : Source →[L] Target) : Quotient (kernel map).val →[L] Target where
  toFun := Quotient.lift map (fun _ _ equal => equal)
  map_fun' {arity} symbol arguments := by
    let representatives : Fin arity → Source := fun index =>
      Classical.choose (quotientMap_surjective (kernel map) (arguments index))
    have represented : arguments = quotientMap (kernel map) ∘ representatives := by
      funext index
      exact (Classical.choose_spec (quotientMap_surjective (kernel map) (arguments index))).symm
    rw [represented, ← (quotientMap (kernel map)).map_fun]
    change map (Structure.funMap symbol representatives) = Structure.funMap symbol (map ∘ representatives)
    exact map.map_fun symbol representatives
  map_rel' symbol := isEmptyElim symbol

@[simp] theorem kernelLift_quotientMap (map : Source →[L] Target) (value : Source) :
    kernelLift map (quotientMap (kernel map) value) = map value := rfl

/-- Equality in the induced image is exactly the kernel equivalence. -/
theorem kernelLift_injective (map : Source →[L] Target) : Function.Injective (kernelLift map) := by
  intro first second
  induction first using Quotient.inductionOn with
  | _ first =>
    induction second using Quotient.inductionOn with
    | _ second =>
      intro equal
      exact Quotient.sound equal

/-- Surjective composites give isomorphisms with their kernel quotients. -/
noncomputable def kernelEquiv (map : Source →[L] Target) (surjective : Function.Surjective map) :
    Quotient (kernel map).val ≃[L] Target where
  toEquiv := _root_.Equiv.ofBijective (kernelLift map) ⟨kernelLift_injective map, by
    intro value
    obtain ⟨source, rfl⟩ := surjective value
    exact ⟨quotientMap (kernel map) source, rfl⟩⟩
  map_fun' := (kernelLift map).map_fun
  map_rel' symbol := isEmptyElim symbol

omit [L.IsAlgebraic] in
/-- Isomorphic finite algebras have equally many congruences. -/
theorem congruence_count_equiv [Finite Source] [Finite Target] (equivalence : Source ≃[L] Target) :
    Nat.card (Congruence L Source) = Nat.card (Congruence L Target) :=
  le_antisymm (congruence_count_le equivalence.symm.toHom equivalence.symm.surjective)
    (congruence_count_le equivalence.toHom equivalence.surjective)

end Polytime2.SMP
