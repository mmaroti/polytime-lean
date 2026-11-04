import Polytime2.CSP.GadgetGluing

/-! # Uniform allocation of fixed relational gadgets

One finite pool contains the variables of every specialization-fixed gadget.
An occurrence uses its selected component; equations collapse the other pool
slots onto that component. The quotient is equivalent to the original fresh
copy construction, so internal allocation adds no output variables.

These are mathematical retractions and quotient proofs. There are no codecs,
machines, polynomial-time interfaces, or assumptions on relation reflexivity.
-/

namespace Polytime2.CSP.GadgetAllocation

universe originalLevel paddedLevel kindLevel hostLevel blockLevel occurrenceLevel boundaryLevel

section Retraction

variable {Original : Type originalLevel} {Padded : Type paddedLevel}

/-- Retain the original equations on the included variables and collapse every
allocated slot onto the included representative of its projection. -/
def allocationEquations (inclusion : Original → Padded) (project : Padded → Original)
    (equations : Original → Original → Prop) (first second : Padded) : Prop :=
  (∃ left right, equations left right ∧ first = inclusion left ∧ second = inclusion right) ∨
    second = inclusion (project first)

/-- Collapsing all extra slots gives exactly the original quotient, rather
than a quotient with extra unused variables. -/
noncomputable def quotientEquiv (inclusion : Original → Padded) (project : Padded → Original)
    (retracts : Function.LeftInverse project inclusion) (equations : Original → Original → Prop) :
    Quot (allocationEquations inclusion project equations) ≃ Quot equations where
  toFun := Quot.lift (fun value => Quot.mk equations (project value)) (by
    intro first second related
    rcases related with ⟨left, right, originalRelated, rfl, rfl⟩ | rfl
    · rw [retracts left, retracts right]
      exact Quot.sound originalRelated
    · rw [retracts])
  invFun := Quot.lift (fun value => Quot.mk _ (inclusion value)) (by
    intro first second related
    exact Quot.sound (Or.inl ⟨first, second, related, rfl, rfl⟩))
  left_inv := by
    intro value
    refine Quot.inductionOn value ?_
    intro representative
    change Quot.mk (allocationEquations inclusion project equations) (inclusion (project representative)) =
      Quot.mk (allocationEquations inclusion project equations) representative
    symm
    apply Quot.sound
    exact Or.inr rfl
  right_inv := by
    intro value
    refine Quot.inductionOn value ?_
    intro representative
    change Quot.mk equations (project (inclusion representative)) = Quot.mk equations representative
    rw [retracts]

theorem quotient_card (inclusion : Original → Padded) (project : Padded → Original)
    (retracts : Function.LeftInverse project inclusion) (equations : Original → Original → Prop) :
    Nat.card (Quot (allocationEquations inclusion project equations)) = Nat.card (Quot equations) :=
  Nat.card_congr (quotientEquiv inclusion project retracts equations)

end Retraction

section FixedPool

variable {Kind : Type kindLevel} [DecidableEq Kind] {Host : Kind → Type hostLevel}
variable {Blocks : Type blockLevel} {Occurrence : Type occurrenceLevel}

/-- Project an allocated pool slot to the selected gadget. Unused components
map to a specialization-fixed variable of that gadget. -/
def poolProjection (defaults : ∀ kind, Host kind) (selected : Kind) (value : Σ kind, Host kind) : Host selected :=
  if same : value.1 = selected then same ▸ value.2 else defaults selected

theorem poolProjection_include (defaults : ∀ kind, Host kind) (selected : Kind) (value : Host selected) :
    poolProjection defaults selected ⟨selected, value⟩ = value := by
  simp [poolProjection]

/-- Include the original shared variables and occurrence-specific gadget
variables in a layout with one whole fixed pool per occurrence. -/
def includeVariable (selected : Occurrence → Kind) :
    (Blocks ⊕ (Σ occurrence, Host (selected occurrence))) → (Blocks ⊕ (Occurrence × (Σ kind, Host kind)))
  | .inl shared => .inl shared
  | .inr ⟨occurrence, value⟩ => .inr (occurrence, ⟨selected occurrence, value⟩)

def projectVariable (defaults : ∀ kind, Host kind) (selected : Occurrence → Kind) :
    (Blocks ⊕ (Occurrence × (Σ kind, Host kind))) → (Blocks ⊕ (Σ occurrence, Host (selected occurrence)))
  | .inl shared => .inl shared
  | .inr (occurrence, value) => .inr ⟨occurrence, poolProjection defaults (selected occurrence) value⟩

theorem projectVariable_include (defaults : ∀ kind, Host kind) (selected : Occurrence → Kind) :
    Function.LeftInverse (projectVariable (Blocks := Blocks) defaults selected) (includeVariable selected) := by
  rintro (shared | ⟨occurrence, value⟩)
  · rfl
  · simp only [projectVariable, includeVariable, poolProjection_include]

omit [DecidableEq Kind] in
/-- The raw uniform allocation has a fixed number of slots per occurrence.
These slots are internal; their quotient has the original glued cardinality. -/
theorem allocated_card [Finite Blocks] [Finite Occurrence] [Fintype Kind] [∀ kind, Finite (Host kind)] :
    Nat.card (Blocks ⊕ (Occurrence × (Σ kind, Host kind))) =
      Nat.card Blocks + Nat.card Occurrence * ∑ kind, Nat.card (Host kind) := by
  rw [Nat.card_sum, Nat.card_prod, Nat.card_sigma]

/-- The uniformly allocated quotient has the original glued variables exactly.
Boundary repetitions and an empty occurrence family require no extra cases. -/
noncomputable def gluedVariablesEquiv (defaults : ∀ kind, Host kind) (selected : Occurrence → Kind)
    {Boundary : Occurrence → Type boundaryLevel}
    (boundary : ∀ occurrence, Boundary occurrence → Host (selected occurrence))
    (scope : ∀ occurrence, Boundary occurrence → Blocks) :
    Quot (allocationEquations (includeVariable selected) (projectVariable defaults selected)
      (boundaryIdentification boundary scope)) ≃ GluedVariables boundary scope :=
  quotientEquiv (includeVariable selected) (projectVariable defaults selected)
    (projectVariable_include defaults selected) (boundaryIdentification boundary scope)

end FixedPool

end Polytime2.CSP.GadgetAllocation
