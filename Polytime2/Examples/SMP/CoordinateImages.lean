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

import Polytime2.Examples.SMP.Generation
import Polytime2.Arrays.FoldContract
import Polytime2.Computation.Constant
import Polytime2.Computation.Arguments
import Polytime2.Computation.Composition
import Polytime2.Primitives.ConstantOperations
import Polytime2.Primitives.FiniteOperations

/-! # Polynomial-time coordinate closure over a fixed finite algebra

The accumulator is an actual subalgebra of the specialized algebra. Its finite
encoding and the closure-update table are fixed before runtime. The generator
column may have arbitrary runtime length.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.SMP

open FirstOrder FirstOrder.Language
open _root_.Polytime2.Computation

variable {L : Language.{0, 0}} {Carrier Parameter : Type}
variable [L.Structure Carrier] [Finite Carrier] [Fintype Parameter]

/-- Subalgebras of a fixed finite carrier form a finite specialization catalogue. -/
instance subalgebrasFinite : Finite (L.Substructure Carrier) :=
  Finite.of_injective (fun subalgebra : L.Substructure Carrier => (subalgebra : Set Carrier))
    SetLike.coe_injective

/-- The existing finite-domain encoding is applied directly to carrier elements. -/
noncomputable def elementDomain (Carrier : Type) [Finite Carrier] : EncodedDomain Empty :=
  EncodedDomain.fixed (@Fintype.equivFin Carrier (Fintype.ofFinite Carrier))

/-- Runtime accumulators encode subalgebras themselves, with no intermediate labels. -/
noncomputable def subalgebraDomain (L : Language.{0, 0}) (Carrier : Type)
    [L.Structure Carrier] [Finite Carrier] : EncodedDomain Empty :=
  EncodedDomain.fixed (@Fintype.equivFin (L.Substructure Carrier) (Fintype.ofFinite _))

/-- The finite update used by the column fold and its final specification. -/
def adjoinGenerated (initial : L.Substructure Carrier) (values : Set Carrier) : L.Substructure Carrier :=
  initial ⊔ Substructure.closure L values

omit [Finite Carrier] in
/-- Repeated finite closure updates generate precisely the accumulated elements. -/
theorem fold_closure (entries : List Carrier) (initial : L.Substructure Carrier) :
    entries.foldl (fun current value => current ⊔ Substructure.closure L {value}) initial =
      initial ⊔ Substructure.closure L {value | value ∈ entries} := by
  induction entries generalizing initial with
  | nil => simp
  | cons value entries hypothesis =>
    rw [List.foldl_cons, hypothesis]
    have members : {entry | entry ∈ value :: entries} = insert value {entry | entry ∈ entries} := by
      ext entry; simp
    rw [members, Substructure.closure_insert]
    exact sup_assoc _ _ _

/-- Add a generator column to an existing generated subalgebra. The top-level
preparation algorithm supplies the empty generated subalgebra as its seed. -/
noncomputable def extendColumn (length : MvPolynomial Parameter ℕ) :
    Computation Parameter (Empty ⊕ Bool) where
  inputDomains := Sum.elim Empty.elim (fun choice => if choice then
    (elementDomain Carrier).constant.arrayOfLength length else (subalgebraDomain L Carrier).constant)
  outputDomain := (subalgebraDomain L Carrier).constant
  precondition _ _ := True
  compute _ arguments := adjoinGenerated (L := L) (arguments.val (.inr false)) (Set.range (arguments.val (.inr true)))

/-- Only a certified finite update and a mathematical fold identity are needed.
Width preparation, array traversal, copies, and polynomial costs are internal. -/
theorem extendColumn_realizable (length : MvPolynomial Parameter ℕ) :
    (extendColumn (L := L) (Carrier := Carrier) length).Realizable := by
  let element : EncodedDomain Parameter := (elementDomain Carrier).constant
  let accumulator : EncodedDomain Parameter := (subalgebraDomain L Carrier).constant
  have update : (arrayFoldStep Empty.elim element accumulator (fun _ _ _ _ => True)
      (fun _ _ current value => adjoinGenerated (L := L) current {value})).Realizable :=
    ((finiteTable_realizable (subalgebraDomain L Carrier) (elementDomain Carrier) (subalgebraDomain L Carrier)
      (fun _ current value => adjoinGenerated (L := L) current {value})).withConstantSizes).withArguments _
      ⟨Sum.inr, Sum.inr_injective⟩ (by intro choice; cases choice <;> rfl)
  have folded := arrayFold_total_realizable Empty.elim element accumulator length
    (fun _ _ current value => adjoinGenerated (L := L) current {value}) update
  exact folded.withSpecification (extendColumn (L := L) (Carrier := Carrier) length).precondition
    (extendColumn (L := L) (Carrier := Carrier) length).compute (by intros; trivial) (by
      intro sizes arguments valid
      let column : Fin (MvPolynomial.eval sizes length) → Carrier := arguments (.inr true)
      let initial : L.Substructure Carrier := arguments (.inr false)
      change ArrayFold.prefixValue
        (fun (current : L.Substructure Carrier) (value : Carrier) => adjoinGenerated current {value})
        column initial (MvPolynomial.eval sizes length) = adjoinGenerated initial (Set.range column)
      unfold ArrayFold.prefixValue
      rw [List.take_of_length_le (by simp)]
      change (List.ofFn column).foldl (fun current value => current ⊔ Substructure.closure L {value}) initial =
        initial ⊔ Substructure.closure L (Set.range column)
      rw [fold_closure]
      congr 2
      ext value
      simp)

/-- Compute a coordinate image directly from its generator column. The seed
includes all closed-term values, so empty columns also have the right meaning. -/
noncomputable def columnClosure (length : MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains _ := (elementDomain Carrier).constant.arrayOfLength length
  outputDomain := (subalgebraDomain L Carrier).constant
  precondition _ _ := True
  compute _ arguments := Substructure.closure L (Set.range (arguments.val ()))

/-- The initial generated subalgebra is a private compiled constant. -/
theorem columnClosure_realizable (length : MvPolynomial Parameter ℕ) :
    (columnClosure (L := L) (Carrier := Carrier) length).Realizable := by
  let computation := columnClosure (L := L) (Carrier := Carrier) length
  have seed := ((constant_realizable (subalgebraDomain L Carrier)
    (fun _ => (⊥ : L.Substructure Carrier))).withConstantSizes (Parameter := Parameter)).withArguments
      computation.inputDomains ⟨Empty.elim, by intro impossible; exact impossible.elim⟩
      (by intro impossible; exact impossible.elim)
  let domains : Unit ⊕ Unit → EncodedDomain Parameter :=
    Sum.elim computation.inputDomains (fun _ => (subalgebraDomain L Carrier).constant)
  let selection : Empty ⊕ Bool ↪ Unit ⊕ Unit :=
    ⟨(fun name => match name with
      | .inl impossible => impossible.elim
      | .inr false => .inr ()
      | .inr true => .inl ()), by
      rintro (impossible | first) (impossible' | second) equal
      all_goals first | exact impossible.elim | exact impossible'.elim |
        (cases first <;> cases second <;> simp_all)⟩
  have extend := (extendColumn_realizable (L := L) (Carrier := Carrier) length).withArguments domains selection
    (by rintro (impossible | choice); exact impossible.elim; cases choice <;> rfl)
  have combined := seed.letThen extend (fun _ => rfl) rfl (by intros; trivial)
  exact combined.withSpecification computation.precondition computation.compute (by intros; trivial) (by
    intro sizes arguments valid
    change (⊥ : L.Substructure Carrier) ⊔ Substructure.closure L (Set.range (arguments ())) = _
    exact bot_sup_eq _)

end Polytime2.SMP
