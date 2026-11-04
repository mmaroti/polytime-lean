import Polytime2.CSP.CanonicalGadget
import Mathlib.Basic.Finite.Sigma
import Mathlib.Basic.Finite.Sum

/-! # Gluing fresh relational gadget copies

Take disjoint copies of the gadget variables, adjoin the shared boundary
variables, and identify each local boundary with its prescribed shared
variable. The resulting quotient carries precisely the images of the gadget
relations. Its universal homomorphism contract formalizes conjunction with
fresh existential variables, including coincident boundary variables.
-/

namespace Polytime2.CSP

open FirstOrder FirstOrder.Language

universe languageLevel blockLevel occurrenceLevel hostLevel boundaryLevel carrierLevel

variable {L : Language.{languageLevel, languageLevel}} [L.IsRelational]
variable {Blocks : Type blockLevel} {Occurrence : Type occurrenceLevel}
variable {Host : Occurrence → Type hostLevel} [hostStructure : ∀ occurrence, L.Structure (Host occurrence)]
variable {Boundary : Occurrence → Type boundaryLevel}

section Construction

/-- Only a boundary of a particular fresh copy is identified with a shared
variable. The quotient supplies the equivalence closure of these equations. -/
def boundaryIdentification (boundary : ∀ occurrence, Boundary occurrence → Host occurrence)
    (scope : ∀ occurrence, Boundary occurrence → Blocks)
    (first second : Blocks ⊕ (Σ occurrence, Host occurrence)) : Prop :=
  ∃ occurrence coordinate,
    first = Sum.inr ⟨occurrence, boundary occurrence coordinate⟩ ∧
      second = Sum.inl (scope occurrence coordinate)

/-- Mathematical variables of the glued instance. Each occurrence has its
own copy of all gadget variables before boundary identification. -/
abbrev GluedVariables (boundary : ∀ occurrence, Boundary occurrence → Host occurrence)
    (scope : ∀ occurrence, Boundary occurrence → Blocks) := Quot (boundaryIdentification boundary scope)

variable (boundary : ∀ occurrence, Boundary occurrence → Host occurrence)
variable (scope : ∀ occurrence, Boundary occurrence → Blocks)

def sharedVariable (block : Blocks) : GluedVariables boundary scope :=
  Quot.mk _ (Sum.inl block)

def localVariable (occurrence : Occurrence) (variableValue : Host occurrence) : GluedVariables boundary scope :=
  Quot.mk _ (Sum.inr ⟨occurrence, variableValue⟩)

theorem localVariable_boundary (occurrence : Occurrence) (coordinate : Boundary occurrence) :
    localVariable boundary scope occurrence (boundary occurrence coordinate) =
      sharedVariable boundary scope (scope occurrence coordinate) :=
  Quot.sound ⟨occurrence, coordinate, rfl, rfl⟩

/-- Relations are exactly the images of relations asserted in gadget copies.
There are no extra relation symbols or equality constraints in the instance. -/
instance gluedStructure : L.Structure (GluedVariables boundary scope) where
  funMap symbol := isEmptyElim symbol
  RelMap symbol tuple := ∃ occurrence, ∃ localTuple : Fin _ → Host occurrence,
    Structure.RelMap symbol localTuple ∧
      (fun index => localVariable boundary scope occurrence (localTuple index)) = tuple

def gadgetInclusion (occurrence : Occurrence) : Host occurrence →[L] GluedVariables boundary scope where
  toFun := localVariable boundary scope occurrence
  map_fun' symbol := isEmptyElim symbol
  map_rel' _symbol tuple related := ⟨occurrence, tuple, related, rfl⟩

variable {Carrier : Type carrierLevel} [L.Structure Carrier]

/-- An assignment on the shared variables extends precisely when it extends
over each separate gadget. No inhabitance or distinct-boundary assumption is
needed; the empty family and nullary relations are included. -/
theorem glued_extends_iff (assignment : Blocks → Carrier) :
    (∃ homomorphism : GluedVariables boundary scope →[L] Carrier,
      ∀ block, homomorphism (sharedVariable boundary scope block) = assignment block) ↔
    ∀ occurrence, ∃ homomorphism : Host occurrence →[L] Carrier,
      ∀ coordinate, homomorphism (boundary occurrence coordinate) = assignment (scope occurrence coordinate) := by
  classical
  constructor
  · rintro ⟨homomorphism, agrees⟩ occurrence
    refine ⟨homomorphism.comp (gadgetInclusion boundary scope occurrence), ?_⟩
    intro coordinate
    change homomorphism (localVariable boundary scope occurrence (boundary occurrence coordinate)) = _
    rw [localVariable_boundary, agrees]
  · intro localExtensions
    choose homomorphisms agrees using localExtensions
    let rawAssignment : Blocks ⊕ (Σ occurrence, Host occurrence) → Carrier :=
      Sum.elim assignment (fun localValue => homomorphisms localValue.1 localValue.2)
    have respects : ∀ first second, boundaryIdentification boundary scope first second →
        rawAssignment first = rawAssignment second := by
      rintro first second ⟨occurrence, coordinate, rfl, rfl⟩
      exact agrees occurrence coordinate
    let result : GluedVariables boundary scope → Carrier := Quot.lift rawAssignment respects
    refine ⟨{
      toFun := result
      map_fun' := fun symbol => isEmptyElim symbol
      map_rel' := ?_ }, fun _ => rfl⟩
    intro arity symbol tuple related
    obtain ⟨occurrence, localTuple, localRelated, rfl⟩ := related
    exact (homomorphisms occurrence).map_rel symbol localTuple localRelated

end Construction

section Counts

/-- A relation symbol and one of its tuples. The arity is part of the symbol. -/
abbrev RelationFact (L : Language.{languageLevel, languageLevel}) (Variables : Type hostLevel) :=
  Σ symbol : RelationSymbol L, Fin symbol.1 → Variables

/-- Enabled relation facts count distinct asserted constraints, including
nullary facts. This is independent of any dense-table encoding. -/
abbrev EnabledFact (L : Language.{languageLevel, languageLevel}) (Variables : Type hostLevel)
    [L.Structure Variables] :=
  {fact : RelationFact L Variables // Structure.RelMap fact.1.2 fact.2}

variable (boundary : ∀ occurrence, Boundary occurrence → Host occurrence)
variable (scope : ∀ occurrence, Boundary occurrence → Blocks)
variable [Finite Blocks] [Fintype Occurrence] [∀ occurrence, Finite (Host occurrence)]

theorem glued_variable_count_le :
    Nat.card (GluedVariables boundary scope) ≤ Nat.card Blocks +
      ∑ occurrence : Occurrence, Nat.card (Host occurrence) := by
  classical
  simpa only [Nat.card_sum, Nat.card_sigma] using
    Nat.card_le_card_of_surjective (Quot.mk (boundaryIdentification boundary scope)) Quot.mk_surjective

omit [Finite Blocks] in
theorem glued_constraint_count_le [Finite (RelationSymbol L)] :
    Nat.card (EnabledFact L (GluedVariables boundary scope)) ≤
      ∑ occurrence : Occurrence, Nat.card (EnabledFact L (Host occurrence)) := by
  classical
  let factMap (fact : Σ occurrence, EnabledFact L (Host occurrence)) :
      EnabledFact L (GluedVariables boundary scope) :=
    ⟨⟨fact.2.val.1, fun index => localVariable boundary scope fact.1 (fact.2.val.2 index)⟩,
      fact.1, fact.2.val.2, fact.2.property, rfl⟩
  have surjective : Function.Surjective factMap := by
    rintro ⟨⟨symbol, tuple⟩, enabled⟩
    obtain ⟨occurrence, localTuple, related, equal⟩ := enabled
    refine ⟨⟨occurrence, ⟨⟨symbol, localTuple⟩, related⟩⟩, ?_⟩
    exact Subtype.ext (congrArg (Sigma.mk symbol) equal)
  simpa only [Nat.card_sigma] using Nat.card_le_card_of_surjective factMap surjective

end Counts

end Polytime2.CSP
