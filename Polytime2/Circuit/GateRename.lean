import Polytime2.Circuit.Construction
import Polytime2.Computation.ParameterRename

/-! # Canonical gate coordinates after size renaming

Only finite bounds change presentation. Natural wire numbers, discriminator
bits, and inactive fields remain unchanged.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Circuit

open EncodedDomain Polytime2.Computation

variable {Parameter NewParameter : Type} [Fintype Parameter] [Fintype NewParameter]

/-- Move a size renaming inside the canonical gate codec. -/
noncomputable def gateRename (wires : MvPolynomial Parameter ℕ) (names : Parameter → NewParameter) :
    Computation NewParameter Unit :=
  encodingMap ((gateDomain wires).renameParameters names) (gateDomain (MvPolynomial.rename names wires))
    (fun sizes gate => gate.map id (fun pair =>
      (pair.1.cast (MvPolynomial.eval_rename names sizes wires).symm,
       pair.2.cast (MvPolynomial.eval_rename names sizes wires).symm)))

theorem gateRename_realizable (wires : MvPolynomial Parameter ℕ) (names : Parameter → NewParameter) :
    (gateRename wires names).Realizable := by
  apply encodingMap_realizable
  · intro sizes
    simp [gateDomain, EncodedDomain.sum, reindex, EncodedDomain.width, variant_widthPolynomial,
      SumEncoding.alternatives, Fin.sum_univ_two, arrayPosition, boundedIndexOfWidth,
      booleans, fixed, ofCodec, MvPolynomial.eval_rename]
  · intro sizes gate
    rw [renameParameters_bits]
    change Bool ⊕ (Fin (MvPolynomial.eval (sizes ∘ names) wires) × Fin (MvPolynomial.eval (sizes ∘ names) wires)) at gate
    rcases gate with value | ⟨left, right⟩ <;>
      simp [gateDomain, EncodedDomain.sum, reindex, bits_variant_encode, SumEncoding.equivalence,
        VariantEncoding.fields, SumEncoding.alternatives, bits_record_encode,
        bits_prod_encode, arrayPosition, boundedIndexOfWidth, ofCodec, ofBoundedCodec,
        MvPolynomial.eval_rename, ArrayEncoding.bits_cast, map_add, map_one, booleans, fixed]
    all_goals simp [ArrayEncoding.bits_append, ArrayEncoding.bits, BitVec.getLsbD_append,
      BitVec.getLsbD_ofNat, ← BitVec.getLsbD_eq_getElem, MvPolynomial.eval_rename]

theorem gateRename_value (wires : MvPolynomial Parameter ℕ) (names : Parameter → NewParameter)
    (sizes : NewParameter → ℕ) (gate : (gateDomain wires).Carrier (sizes ∘ names)) :
    gateValue ((gateRename wires names).compute sizes ⟨(fun _ => gate), trivial⟩) = gateValue gate := by
  cases gate <;> rfl

end Polytime2.Circuit
