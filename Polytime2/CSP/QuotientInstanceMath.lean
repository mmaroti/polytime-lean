import Polytime2.CSP.Instance
import Polytime2.Arrays.QuotientLabelsMath

/-! # Mathematical contract for numbered quotient instances

The representatives enumerate exactly the fixed labels of an equation list.
Push forward the original relations through that quotient. A solution is
equivalent to a solution of the original relations satisfying the equations.
No codec, machine, padding convention, or default carrier value is used.
-/

namespace Polytime2.CSP

open FirstOrder FirstOrder.Language

universe languageLevel carrierLevel

variable {L : Language.{languageLevel, languageLevel}} [L.IsRelational]
variable {vertices classes : ℕ}

/-- Relation images specified by original-vertex labels and one representative
for each output vertex. No quotient-validity assumptions are needed. -/
@[instance_reducible]
def instanceImage (input : Instance L vertices) (labels : Fin vertices → Fin vertices)
    (representatives : Fin classes → Fin vertices) : Instance L classes where
  funMap symbol := isEmptyElim symbol
  RelMap symbol tuple := ∃ original : Fin _ → Fin vertices,
    input.RelMap symbol original ∧
      ∀ coordinate, labels (original coordinate) = representatives (tuple coordinate)

/-- A dense presentation of the relation images on the numbered classes.
The relation test uses labels and actual representatives, not quotient syntax. -/
@[instance_reducible]
def quotientInstance (input : Instance L vertices) (equations : List (Fin vertices × Fin vertices))
    (representatives : Fin classes → Fin vertices) : Instance L classes :=
  instanceImage input (ArrayQuotient.labels equations) representatives

/-- Renaming equal finite bounds and transporting the data preserves relation
images. This separates mathematical transport from codec conversions. -/
theorem instanceImage_heq {otherVertices otherClasses : ℕ}
    (sameVertices : vertices = otherVertices) (sameClasses : classes = otherClasses)
    (input : Instance L vertices) (otherInput : Instance L otherVertices)
    (labels : Fin vertices → Fin vertices) (otherLabels : Fin otherVertices → Fin otherVertices)
    (representatives : Fin classes → Fin vertices)
    (otherRepresentatives : Fin otherClasses → Fin otherVertices)
    (sameInput : HEq input otherInput)
    (sameLabels : ∀ (first : Fin vertices) (second : Fin otherVertices), first.val = second.val →
      (labels first).val = (otherLabels second).val)
    (sameRepresentatives : ∀ (first : Fin classes) (second : Fin otherClasses), first.val = second.val →
      (representatives first).val = (otherRepresentatives second).val) :
    HEq (instanceImage input labels representatives) (instanceImage otherInput otherLabels otherRepresentatives) := by
  cases sameVertices
  cases sameClasses
  cases sameInput
  have labelEquality : labels = otherLabels := funext (fun index => Fin.ext (sameLabels index index rfl))
  have representativeEquality : representatives = otherRepresentatives :=
    funext (fun index => Fin.ext (sameRepresentatives index index rfl))
  cases labelEquality
  cases representativeEquality
  rfl

/-- Number a vertex by the class of its fixed representative. -/
def quotientNumber (equations : List (Fin vertices × Fin vertices))
    (representatives : Fin classes ≃ {value : Fin vertices // ArrayQuotient.labels equations value = value})
    (value : Fin vertices) : Fin classes :=
  representatives.symm ⟨ArrayQuotient.labels equations value, ArrayQuotient.labels_idempotent equations value⟩

theorem representative_quotientNumber (equations : List (Fin vertices × Fin vertices))
    (representatives : Fin classes ≃ {value : Fin vertices // ArrayQuotient.labels equations value = value})
    (value : Fin vertices) :
    (representatives (quotientNumber equations representatives value)).val = ArrayQuotient.labels equations value :=
  congrArg Subtype.val (representatives.apply_symm_apply _)

/-- Numbering the quotient neither adds nor loses solutions, including empty
carriers, empty equation lists, and nullary relation symbols. -/
theorem quotientInstance_satisfiable_iff (input : Instance L vertices)
    (equations : List (Fin vertices × Fin vertices))
    (representatives : Fin classes ≃ {value : Fin vertices // ArrayQuotient.labels equations value = value})
    (Carrier : Type carrierLevel) [L.Structure Carrier] :
    Instance.Satisfiable L (quotientInstance input equations (fun index => (representatives index).val)) Carrier ↔
      ∃ assignment : Fin vertices → Carrier,
        (∀ arity (symbol : L.Relations arity) (tuple : Fin arity → Fin vertices),
          input.RelMap symbol tuple → Structure.RelMap symbol (assignment ∘ tuple)) ∧
        ∀ equation ∈ equations, assignment equation.1 = assignment equation.2 := by
  rw [Instance.satisfiable_iff_exists_assignment]
  constructor
  · rintro ⟨assignment, preserves⟩
    let original value := assignment (quotientNumber equations representatives value)
    refine ⟨original, ?_, ?_⟩
    · intro arity symbol tuple related
      exact preserves arity symbol (quotientNumber equations representatives ∘ tuple)
        ⟨tuple, related, fun coordinate => (representative_quotientNumber equations representatives (tuple coordinate)).symm⟩
    · intro equation member
      have same : quotientNumber equations representatives equation.1 =
          quotientNumber equations representatives equation.2 :=
        congrArg representatives.symm (Subtype.ext (ArrayQuotient.collapse_identifies equations id member))
      exact congrArg assignment same
  · rintro ⟨assignment, preserves, respects⟩
    refine ⟨fun index => assignment (representatives index).val, ?_⟩
    intro arity symbol tuple related
    obtain ⟨original, originalRelated, sameClasses⟩ := related
    have equal : (fun coordinate => assignment (representatives (tuple coordinate)).val) = assignment ∘ original := by
      funext coordinate
      exact (congrArg assignment (sameClasses coordinate).symm).trans
        (ArrayQuotient.labels_factors assignment equations respects (original coordinate))
    change Structure.RelMap symbol (fun coordinate => assignment (representatives (tuple coordinate)).val)
    rw [equal]
    exact preserves arity symbol original originalRelated

end Polytime2.CSP
