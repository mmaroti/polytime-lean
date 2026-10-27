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

import Polytime2.Encoding.EncodedArray
import Polytime2.Encoding.BinaryEncoding
import Polytime2.Encoding.Records
import Polytime2.Encoding.ParameterRename

/-! # Polynomial substitution and majorization for size assignments

An exact substitution transports domains. The same substitution bounds widths
and runtimes at any smaller, possibly input-dependent, size assignment.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.SizeSubstitution

variable {Parameter NewParameter : Type}

/-- Substitute one caller polynomial for every callee size parameter. -/
noncomputable def polynomial (substitution : NewParameter → MvPolynomial Parameter ℕ)
    (value : MvPolynomial NewParameter ℕ) : MvPolynomial Parameter ℕ :=
  MvPolynomial.eval₂Hom MvPolynomial.C substitution value

/-- The size assignment associated with an exact polynomial substitution. -/
noncomputable def assignment (substitution : NewParameter → MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) : NewParameter → ℕ :=
  fun parameter => MvPolynomial.eval sizes (substitution parameter)

@[simp] theorem polynomial_eval (substitution : NewParameter → MvPolynomial Parameter ℕ)
    (value : MvPolynomial NewParameter ℕ) (sizes : Parameter → ℕ) :
    MvPolynomial.eval sizes (polynomial substitution value) =
      MvPolynomial.eval (assignment substitution sizes) value := by
  induction value using MvPolynomial.induction_on with
  | C value => simp [polynomial]
  | add left right leftEqual rightEqual =>
    simpa [polynomial] using congrArg₂ (· + ·) leftEqual rightEqual
  | mul_X value parameter equality =>
    simpa [polynomial, assignment] using
      congrArg (· * MvPolynomial.eval sizes (substitution parameter)) equality

/-- Substitution by named variables is ordinary parameter renaming. -/
@[simp] theorem polynomial_X (names : NewParameter → Parameter) (value : MvPolynomial NewParameter ℕ) :
    polynomial (fun name => MvPolynomial.X (names name)) value = MvPolynomial.rename names value := by
  simp only [MvPolynomial.rename_eq_aeval, MvPolynomial.aeval, polynomial, Function.comp_def]
  rfl

@[simp] theorem assignment_X (names : NewParameter → Parameter) (sizes : Parameter → ℕ) :
    assignment (fun name => MvPolynomial.X (names name)) sizes = sizes ∘ names := by
  funext name
  exact MvPolynomial.eval_X _

/-- Exact polynomial substitutions compose by substituting into each image. -/
theorem polynomial_comp {ThirdParameter : Type}
    (first : NewParameter → MvPolynomial Parameter ℕ)
    (second : Parameter → MvPolynomial ThirdParameter ℕ) (value : MvPolynomial NewParameter ℕ) :
    polynomial second (polynomial first value) =
      polynomial (fun name => polynomial second (first name)) value := by
  exact (MvPolynomial.eval₂_assoc (f := MvPolynomial.C) (g := second) first value).symm

theorem assignment_comp {ThirdParameter : Type}
    (first : NewParameter → MvPolynomial Parameter ℕ)
    (second : Parameter → MvPolynomial ThirdParameter ℕ) (sizes : ThirdParameter → ℕ) :
    assignment first (assignment second sizes) =
      assignment (fun name => polynomial second (first name)) sizes := by
  funext name
  exact (polynomial_eval second (first name) sizes).symm

/-- Natural-coefficient polynomials are monotone in every size parameter. -/
theorem eval_mono (value : MvPolynomial NewParameter ℕ)
    {sizes bounds : NewParameter → ℕ} (bounded : ∀ parameter, sizes parameter ≤ bounds parameter) :
    MvPolynomial.eval sizes value ≤ MvPolynomial.eval bounds value := by
  induction value using MvPolynomial.induction_on with
  | C value => simp
  | add left right leftBound rightBound =>
    simpa only [map_add] using Nat.add_le_add leftBound rightBound
  | mul_X value parameter valueBound =>
    simpa only [map_mul, MvPolynomial.eval_X] using Nat.mul_le_mul valueBound (bounded parameter)

/-- Computed sizes need only polynomial upper bounds, not exact formulas. -/
theorem eval_le (substitution : NewParameter → MvPolynomial Parameter ℕ)
    (value : MvPolynomial NewParameter ℕ) (sizes : Parameter → ℕ)
    (computed : NewParameter → ℕ)
    (bounded : ∀ parameter, computed parameter ≤ MvPolynomial.eval sizes (substitution parameter)) :
    MvPolynomial.eval computed value ≤ MvPolynomial.eval sizes (polynomial substitution value) := by
  rw [polynomial_eval]
  exact eval_mono value bounded

end Polytime2.SizeSubstitution

namespace Polytime2.EncodedDomain

universe carrierLevel
variable {Parameter NewParameter : Type} [Fintype Parameter] [Fintype NewParameter]

/-- Reparameterization keeps the original carriers and canonical bits. -/
noncomputable def substitute (domain : EncodedDomain.{0, carrierLevel} NewParameter)
    (substitution : NewParameter → MvPolynomial Parameter ℕ) : EncodedDomain Parameter :=
  ofCodec (fun sizes => domain.Carrier (SizeSubstitution.assignment substitution sizes))
    (SizeSubstitution.polynomial substitution domain.widthPolynomial)
    (fun sizes => domain.width (SizeSubstitution.assignment substitution sizes))
    (fun sizes => (SizeSubstitution.polynomial_eval substitution domain.widthPolynomial sizes).symm)
    (fun sizes => domain.encode (SizeSubstitution.assignment substitution sizes))
    (fun sizes => domain.decode (SizeSubstitution.assignment substitution sizes))
    (fun sizes => domain.decode_encode (SizeSubstitution.assignment substitution sizes))
    (fun sizes => domain.encode_decode (SizeSubstitution.assignment substitution sizes))

/-- Exact polynomial word widths reuse the substituted unsigned word codec. -/
theorem binaryNaturals_substitute_bits
    (substitution : NewParameter → MvPolynomial Parameter ℕ) (name : NewParameter)
    (sizes : Parameter → ℕ) (value : Fin (2 ^ MvPolynomial.eval sizes (substitution name))) :
    ArrayEncoding.bits ((binaryNaturalsOfWidth (substitution name)).encode sizes value) =
      ArrayEncoding.bits (((binaryNaturals name).substitute substitution).encode sizes value) := by
  simp only [binaryNaturalsOfWidth, boundedIndexOfWidth, ofCodec, ArrayEncoding.bits_cast,
    EncodedDomain.substitute, binaryNaturals, BitVec.ofNatLT_finVal]
  rfl

@[simp] theorem substitute_width (domain : EncodedDomain.{0, carrierLevel} NewParameter)
    (substitution : NewParameter → MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ) :
    (domain.substitute substitution).width sizes =
      domain.width (SizeSubstitution.assignment substitution sizes) :=
  SizeSubstitution.polynomial_eval substitution domain.widthPolynomial sizes

@[simp] theorem substitute_encode_bits (domain : EncodedDomain.{0, carrierLevel} NewParameter)
    (substitution : NewParameter → MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (value : domain.Carrier (SizeSubstitution.assignment substitution sizes)) :
    ArrayEncoding.bits ((domain.substitute substitution).encode sizes value) =
      ArrayEncoding.bits (domain.encode (SizeSubstitution.assignment substitution sizes) value) := by
  simp only [substitute, ofCodec, ArrayEncoding.bits_cast]

/-- Variable substitution and direct parameter renaming are the same codec. -/
@[simp] theorem substitute_X (domain : EncodedDomain.{0, carrierLevel} NewParameter)
    (names : NewParameter → Parameter) :
    domain.substitute (fun name => MvPolynomial.X (names name)) = domain.renameParameters names := by
  refine ext_of_encode_bits (domain.substitute (fun name => MvPolynomial.X (names name)))
    (domain.renameParameters names) ?_ ?_ ?_
  · funext sizes
    simp only [substitute, renameParameters, ofCodec, SizeSubstitution.assignment_X]
  · exact SizeSubstitution.polynomial_X _ _
  · intro sizes value
    simp only [substitute_encode_bits, renameParameters_bits]
    exact encode_bits_cast_sizes domain (SizeSubstitution.assignment_X names sizes) value

/-- Substitution by the original variables retains the entire codec. -/
@[simp] theorem substitute_id (domain : EncodedDomain.{0, carrierLevel} Parameter) :
    domain.substitute MvPolynomial.X = domain := by
  exact (substitute_X (Parameter := Parameter) domain (id : Parameter → Parameter)).trans
    (renameParameters_id domain)

/-- Composed polynomial substitutions retain canonical bits and carriers. -/
@[simp] theorem substitute_comp {ThirdParameter : Type} [Fintype ThirdParameter]
    (domain : EncodedDomain.{0, carrierLevel} NewParameter)
    (first : NewParameter → MvPolynomial Parameter ℕ)
    (second : Parameter → MvPolynomial ThirdParameter ℕ) :
    (domain.substitute first).substitute second =
      domain.substitute (fun name => SizeSubstitution.polynomial second (first name)) := by
  refine ext_of_encode_bits ((domain.substitute first).substitute second)
    (domain.substitute (fun name => SizeSubstitution.polynomial second (first name))) ?_ ?_ ?_
  · funext sizes
    change domain.Carrier _ = domain.Carrier _
    rw [SizeSubstitution.assignment_comp]
  · exact SizeSubstitution.polynomial_comp _ _ _
  · intro sizes value
    simp only [substitute_encode_bits]
    exact encode_bits_cast_sizes domain (SizeSubstitution.assignment_comp first second sizes) value

/-- Product fields keep their order and bits under exact size substitution. -/
theorem substitute_prod_encode_bits
    (left right : EncodedDomain.{0, carrierLevel} NewParameter)
    (substitution : NewParameter → MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (value : left.Carrier (SizeSubstitution.assignment substitution sizes) ×
      right.Carrier (SizeSubstitution.assignment substitution sizes)) :
    ArrayEncoding.bits (((left.substitute substitution).prod (right.substitute substitution)).encode sizes value) =
      ArrayEncoding.bits (((left.prod right).substitute substitution).encode sizes value) := by
  rw [substitute_encode_bits]
  exact prod_encode_bits_congr (left.substitute substitution) (right.substitute substitution)
    left right sizes (SizeSubstitution.assignment substitution sizes) value value
    (substitute_encode_bits left substitution sizes value.1)
    (substitute_encode_bits right substitution sizes value.2)

end Polytime2.EncodedDomain
