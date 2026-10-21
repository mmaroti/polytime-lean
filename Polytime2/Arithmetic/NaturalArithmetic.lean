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

import Polytime2.Arithmetic.Operations
import Polytime2.Arithmetic.WidthOperations
import Polytime2.Arithmetic.GcdOperations

/-! # Natural arithmetic at derived polynomial word widths

These internal specializations keep the existing unsigned machines and their
mathematical preconditions. Signed arithmetic prepares sufficient word widths
before calling them; callers of the signed interface need no capacity premise.
-/

namespace Polytime2.Computation.Realizable.Internal

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def naturalBinaryAtWidth (width : MvPolynomial Parameter ℕ)
    (allowed : ∀ digits : ℕ, (Bool → Fin (2 ^ digits)) → Prop)
    (result : ∀ digits, {arguments : Bool → Fin (2 ^ digits) // allowed digits arguments} → Fin (2 ^ digits)) :
    Computation Parameter Bool where
  inputDomains _ := binaryNaturalsOfWidth width
  outputDomain := binaryNaturalsOfWidth width
  precondition sizes := allowed (MvPolynomial.eval sizes width)
  compute sizes := result (MvPolynomial.eval sizes width)

private theorem naturalBinaryAtWidth_realizable (width : MvPolynomial Parameter ℕ)
    (allowed : ∀ digits : ℕ, (Bool → Fin (2 ^ digits)) → Prop)
    (result : ∀ digits, {arguments : Bool → Fin (2 ^ digits) // allowed digits arguments} → Fin (2 ^ digits))
    (source : (Computation.mk (fun _ : Bool => (binaryNaturals () : EncodedDomain Unit))
      (binaryNaturals ()) (fun sizes => allowed (sizes ())) (fun sizes => result (sizes ()))).Realizable) :
    (naturalBinaryAtWidth width allowed result).Realizable := by
  have specialized := (source.substitute (fun _ : Unit => width)).reinterpretInputs
    (fun _ => binaryNaturalsOfWidth width) (fun _ _ value => value)
    (by
      intros
      change (binaryNaturalsOfWidth width).width _ =
        ((binaryNaturals ()).substitute (fun _ : Unit => width)).width _
      simp [SizeSubstitution.assignment])
    (fun _ sizes value => binaryNaturals_substitute_bits (fun _ : Unit => width) () sizes value)
    (fun sizes => allowed (MvPolynomial.eval sizes width)) (by intros; assumption)
  exact specialized.reinterpretOutput (binaryNaturalsOfWidth width) (fun _ value => value)
    (by
      intros
      change (binaryNaturalsOfWidth width).width _ =
        ((binaryNaturals ()).substitute (fun _ : Unit => width)).width _
      simp [SizeSubstitution.assignment])
    (fun sizes value => binaryNaturals_substitute_bits (fun _ : Unit => width) () sizes value)

noncomputable def naturalIncrement (width : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  unaryMap (binaryNaturalsOfWidth width) (binaryNaturalsOfWidth width) (fun _ _ => True)
    (fun sizes value => ⟨(value.val.val + 1) % 2 ^ MvPolynomial.eval sizes width,
      Nat.mod_lt _ (by positivity)⟩)

theorem naturalIncrement_realizable (width : MvPolynomial Parameter ℕ) :
    (naturalIncrement width).Realizable := by
  have source := ((counterIncrement_realizable ()).substitute (fun _ : Unit => width)).reinterpretInputs
    (fun _ => binaryNaturalsOfWidth width) (fun _ _ value => value)
    (by
      intros
      change (binaryNaturalsOfWidth width).width _ =
        ((binaryNaturals ()).substitute (fun _ : Unit => width)).width _
      simp [SizeSubstitution.assignment])
    (fun _ sizes value => binaryNaturals_substitute_bits (fun _ : Unit => width) () sizes value)
    (fun _ _ => True) (by intros; trivial)
  exact source.reinterpretOutput (binaryNaturalsOfWidth width) (fun _ value => value)
    (by
      intros
      change (binaryNaturalsOfWidth width).width _ =
        ((binaryNaturals ()).substitute (fun _ : Unit => width)).width _
      simp [SizeSubstitution.assignment])
    (fun sizes value => binaryNaturals_substitute_bits (fun _ : Unit => width) () sizes value)

noncomputable def naturalAdd (width : MvPolynomial Parameter ℕ) : Computation Parameter Bool :=
  naturalBinaryAtWidth width
    (fun digits arguments => (arguments false).val + (arguments true).val < 2 ^ digits)
    (fun _ arguments => ⟨(arguments.val false).val + (arguments.val true).val, arguments.property⟩)

theorem naturalAdd_realizable (width : MvPolynomial Parameter ℕ) : (naturalAdd width).Realizable :=
  naturalBinaryAtWidth_realizable width _ _ binaryAdd_realizable

noncomputable def naturalSubtract (width : MvPolynomial Parameter ℕ) : Computation Parameter Bool :=
  naturalBinaryAtWidth width (fun _ arguments => (arguments true).val ≤ (arguments false).val)
    (fun _ arguments => ⟨(arguments.val false).val - (arguments.val true).val,
      (Nat.sub_le _ _).trans_lt (arguments.val false).isLt⟩)

theorem naturalSubtract_realizable (width : MvPolynomial Parameter ℕ) : (naturalSubtract width).Realizable :=
  naturalBinaryAtWidth_realizable width _ _ binarySubtract_realizable

noncomputable def naturalGcd (width : MvPolynomial Parameter ℕ) : Computation Parameter Bool :=
  naturalBinaryAtWidth width (fun _ _ => True)
    (fun digits arguments => gcdValue digits (arguments.val false) (arguments.val true))

theorem naturalGcd_realizable (width : MvPolynomial Parameter ℕ) : (naturalGcd width).Realizable :=
  naturalBinaryAtWidth_realizable width _ _ gcd_realizable

noncomputable def naturalDivision (width : MvPolynomial Parameter ℕ) : Computation Parameter Bool where
  inputDomains _ := binaryNaturalsOfWidth width
  outputDomain := (binaryNaturalsOfWidth width).prod (binaryNaturalsOfWidth width)
  precondition _ arguments := 0 < (arguments true).val
  compute _ arguments :=
    (⟨(arguments.val false).val / (arguments.val true).val,
      (Nat.div_le_self _ _).trans_lt (arguments.val false).isLt⟩,
     ⟨(arguments.val false).val % (arguments.val true).val,
      (Nat.mod_lt _ arguments.property).trans (arguments.val true).isLt⟩)

theorem naturalDivision_realizable (width : MvPolynomial Parameter ℕ) :
    (naturalDivision width).Realizable := by
  have source := (binaryDivision_realizable.substitute (fun _ : Unit => width)).reinterpretInputs
    (fun _ => binaryNaturalsOfWidth width) (fun _ _ value => value)
    (by
      intros
      change (binaryNaturalsOfWidth width).width _ =
        ((binaryNaturals ()).substitute (fun _ : Unit => width)).width _
      simp [SizeSubstitution.assignment])
    (fun _ sizes value => binaryNaturals_substitute_bits (fun _ : Unit => width) () sizes value)
    (naturalDivision width).precondition (by intros; assumption)
  apply source.reinterpretOutput ((binaryNaturalsOfWidth width).prod (binaryNaturalsOfWidth width))
    (fun _ value => value)
    (by
      intro sizes
      change ((binaryNaturalsOfWidth width).prod (binaryNaturalsOfWidth width)).width sizes =
        (((binaryNaturals ()).prod (binaryNaturals ())).substitute (fun _ : Unit => width)).width sizes
      simp [EncodedDomain.width, SizeSubstitution.assignment])
  intro sizes answer
  exact (bits_prod_encode (binaryNaturalsOfWidth width) (binaryNaturalsOfWidth width) sizes answer).trans
    ((congrArg₂ List.append
      (binaryNaturals_substitute_bits (fun _ : Unit => width) () sizes answer.1)
      (binaryNaturals_substitute_bits (fun _ : Unit => width) () sizes answer.2)).trans
      ((bits_prod_encode ((binaryNaturals ()).substitute (fun _ : Unit => width))
        ((binaryNaturals ()).substitute (fun _ : Unit => width)) sizes answer).symm.trans
        (substitute_prod_encode_bits (binaryNaturals ()) (binaryNaturals ())
          (fun _ : Unit => width) sizes answer)))

/-- The existing multiplier permits independent operand capacities. -/
noncomputable def naturalMultiplyAtWidths (leftWidth rightWidth : MvPolynomial Parameter ℕ) :
    Computation Parameter Bool where
  inputDomains name := binaryNaturalsOfWidth (if name then rightWidth else leftWidth)
  outputDomain := binaryNaturalsOfWidth leftWidth
  precondition sizes arguments := (arguments false).val * (arguments true).val < 2 ^ MvPolynomial.eval sizes leftWidth
  compute _ arguments := ⟨(arguments.val false).val * (arguments.val true).val, arguments.property⟩

theorem naturalMultiplyAtWidths_realizable (leftWidth rightWidth : MvPolynomial Parameter ℕ) :
    (naturalMultiplyAtWidths leftWidth rightWidth).Realizable := by
  let substitution : Bool → MvPolynomial Parameter ℕ := fun name => if name then rightWidth else leftWidth
  have source := (binaryMultiply_realizable.substitute substitution).reinterpretInputs
    (naturalMultiplyAtWidths leftWidth rightWidth).inputDomains (fun _ _ value => value)
    (by
      intro name sizes
      change (binaryNaturalsOfWidth (substitution name)).width sizes =
        ((binaryNaturals name).substitute substitution).width sizes
      simp [SizeSubstitution.assignment])
    (fun name sizes value => binaryNaturals_substitute_bits substitution name sizes value)
    (naturalMultiplyAtWidths leftWidth rightWidth).precondition (by intros; assumption)
  exact source.reinterpretOutput (binaryNaturalsOfWidth leftWidth) (fun _ value => value)
    (by
      intro sizes
      change (binaryNaturalsOfWidth (substitution false)).width sizes =
        ((binaryNaturals false).substitute substitution).width sizes
      simp [SizeSubstitution.assignment])
    (fun sizes value => binaryNaturals_substitute_bits substitution false sizes value)

end Polytime2.Computation.Realizable.Internal
