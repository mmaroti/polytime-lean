import Polytime2.CSP.GadgetEquationEndpoints
import Polytime2.CSP.RelationMaterialize

/-! # Certified local facts of the uniform gadget construction

A fixed pool tuple contributes one optional scope. Domain facts use the fixed
domain table; clause facts read the three Boolean literal signs. All variable
renaming uses the certified positions of the mathematical allocation layout.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.CSP.GadgetExpansion

open FirstOrder FirstOrder.Language EncodedDomain Polytime2.Computation GadgetAllocation

variable {L : Language.{0, 0}} [L.IsRelational]
variable {Carrier : Type} [L.Structure Carrier] [Finite Carrier] [Nonempty Carrier]
variable {dimension poolSize arity : ℕ}
variable (domainFormula : L.Formula (Fin dimension))
variable (clauseFormulas : (Fin 3 → Bool) → L.Formula (Fin 3 × Fin dimension))
variable (enumeration : Pool (Carrier := Carrier) domainFormula clauseFormulas ≃ Fin poolSize)
variable {Parameter : Type} [Fintype Parameter]

/-- The actual numbered scope of a local domain tuple. -/
noncomputable def domainFactScope (wires clauses : MvPolynomial Parameter ℕ)
    (localTuple : Fin arity → Pool (Carrier := Carrier) domainFormula clauseFormulas)
    (sizes : Parameter → ℕ) (source : Fin (MvPolynomial.eval sizes wires)) :
    Fin arity → Fin (MvPolynomial.eval sizes (allocationSize wires clauses dimension poolSize)) :=
  fun coordinate => allocationEquiv enumeration wires clauses dimension sizes (.inr (.inl source, localTuple coordinate))

/-- A fixed local domain relation contributes its scope precisely when true. -/
noncomputable def domainFact (wires clauses : MvPolynomial Parameter ℕ) (symbol : L.Relations arity)
    (localTuple : Fin arity → Pool (Carrier := Carrier) domainFormula clauseFormulas) :
    Computation Parameter Unit := by
  classical
  exact {
    inputDomains := fun _ => arrayPosition wires
    outputDomain := relationFactDomain (allocationSize wires clauses dimension poolSize) arity
    precondition := fun _ _ => True
    compute := fun sizes arguments =>
      if poolRelation domainFormula clauseFormulas (.inl ()) symbol localTuple then
        some (domainFactScope domainFormula clauseFormulas enumeration wires clauses localTuple sizes (arguments.val ()))
      else none }

omit [L.IsRelational] [Finite Carrier] in
theorem domainFact_realizable (wires clauses : MvPolynomial Parameter ℕ) (symbol : L.Relations arity)
    (localTuple : Fin arity → Pool (Carrier := Carrier) domainFormula clauseFormulas) :
    (domainFact domainFormula clauseFormulas enumeration wires clauses symbol localTuple).Realizable := by
  classical
  let computation := domainFact domainFormula clauseFormulas enumeration wires clauses symbol localTuple
  let inputs := computation.inputDomains
  let vertices := allocationSize wires clauses dimension poolSize
  have position (coordinate : Fin arity) :
      (Computation.mk inputs (arrayPosition vertices) (fun _ _ => True)
        (fun sizes arguments => domainFactScope domainFormula clauseFormulas enumeration wires clauses
          localTuple sizes (arguments.val ()) coordinate)).Realizable :=
    domainPoolPosition_realizable domainFormula clauseFormulas enumeration wires clauses (localTuple coordinate)
  have scopeReady := Realizable.recordOutputs inputs arity (fun _ => arrayPosition vertices)
    (fun _ _ => True) (fun coordinate sizes arguments =>
      domainFactScope domainFormula clauseFormulas enumeration wires clauses localTuple sizes (arguments.val ()) coordinate)
    position
  by_cases related : poolRelation domainFormula clauseFormulas (.inl ()) symbol localTuple
  · have present := scopeReady.followedBy (optionalSome_realizable (record arity (fun _ => arrayPosition vertices)))
      rfl (by intros; trivial)
    apply present.withSpecification (fun _ _ => True) computation.compute (by intros; trivial)
    intro sizes arguments valid
    simp only [computation, domainFact, related, ite_true, followedBy, optionalSome, unaryMap]
  · have absent := (optionalNone_realizable (record arity (fun _ => arrayPosition vertices))).onResults inputs
      (fun _ _ => True) (fun empty => nomatch empty) (by intros; trivial) (fun empty => nomatch empty)
    apply absent.withSpecification (fun _ _ => True) computation.compute (by intros; trivial)
    intro sizes arguments valid
    simp only [onResults, optionalNone, computation, domainFact, related, ite_false]

omit [L.IsRelational] [Finite Carrier] in
theorem domainFact_some_iff (wires clauses : MvPolynomial Parameter ℕ) (symbol : L.Relations arity)
    (localTuple : Fin arity → Pool (Carrier := Carrier) domainFormula clauseFormulas) (sizes : Parameter → ℕ)
    (source : Fin (MvPolynomial.eval sizes wires))
    (tuple : Fin arity → Fin (MvPolynomial.eval sizes (allocationSize wires clauses dimension poolSize))) :
    (domainFact domainFormula clauseFormulas enumeration wires clauses symbol localTuple).compute sizes
      ⟨fun _ => source, trivial⟩ = some tuple ↔
      poolRelation domainFormula clauseFormulas (.inl ()) symbol localTuple ∧
        domainFactScope domainFormula clauseFormulas enumeration wires clauses localTuple sizes source = tuple := by
  classical
  by_cases related : poolRelation domainFormula clauseFormulas (.inl ()) symbol localTuple
  · simp only [domainFact, related, ite_true, true_and]
    exact ⟨Option.some.inj, congrArg some⟩
  · simp [domainFact, related]

/-- The actual numbered scope of a local clause tuple. -/
noncomputable def clauseFactScope (wires clauses : MvPolynomial Parameter ℕ)
    (localTuple : Fin arity → Pool (Carrier := Carrier) domainFormula clauseFormulas)
    (sizes : Parameter → ℕ) (clause : Fin (MvPolynomial.eval sizes clauses)) :
    Fin arity → Fin (MvPolynomial.eval sizes (allocationSize wires clauses dimension poolSize)) :=
  fun coordinate => allocationEquiv enumeration wires clauses dimension sizes (.inr (.inr clause, localTuple coordinate))

/-- Only the clause occurrence and its three Boolean signs enter a local fact. -/
noncomputable def clauseFact (wires clauses : MvPolynomial Parameter ℕ) (symbol : L.Relations arity)
    (localTuple : Fin arity → Pool (Carrier := Carrier) domainFormula clauseFormulas) :
    Computation Parameter (Option (Fin 3)) := by
  classical
  exact {
    inputDomains := fun name => match name with | none => arrayPosition clauses | some _ => booleans
    outputDomain := relationFactDomain (allocationSize wires clauses dimension poolSize) arity
    precondition := fun _ _ => True
    compute := fun sizes arguments =>
      if poolRelation domainFormula clauseFormulas (.inr (fun coordinate => arguments.val (some coordinate))) symbol localTuple then
        some (clauseFactScope domainFormula clauseFormulas enumeration wires clauses localTuple sizes (arguments.val none))
      else none }

omit [L.IsRelational] [Finite Carrier] in
theorem clauseFact_realizable (wires clauses : MvPolynomial Parameter ℕ) (symbol : L.Relations arity)
    (localTuple : Fin arity → Pool (Carrier := Carrier) domainFormula clauseFormulas) :
    (clauseFact domainFormula clauseFormulas enumeration wires clauses symbol localTuple).Realizable := by
  classical
  let computation := clauseFact domainFormula clauseFormulas enumeration wires clauses symbol localTuple
  let inputs := computation.inputDomains
  let vertices := allocationSize wires clauses dimension poolSize
  have position (coordinate : Fin arity) :
      (Computation.mk inputs (arrayPosition vertices) (fun _ _ => True)
        (fun sizes arguments => clauseFactScope domainFormula clauseFormulas enumeration wires clauses
          localTuple sizes (arguments.val none) coordinate)).Realizable :=
    clausePoolPosition_realizable domainFormula clauseFormulas enumeration wires clauses (fun _ => localTuple coordinate)
  have scopeReady := Realizable.recordOutputs inputs arity (fun _ => arrayPosition vertices)
    (fun _ _ => True) (fun coordinate sizes arguments =>
      clauseFactScope domainFormula clauseFormulas enumeration wires clauses localTuple sizes (arguments.val none) coordinate)
    position
  let enabled (pattern : Fin 3 → Bool) := poolRelation domainFormula clauseFormulas (.inr pattern) symbol localTuple
  have enabledReady := (booleanOperation_realizable (fun pattern : Fin 3 → Bool => decide (enabled pattern))).onArguments
    inputs (fun _ _ => True) some (by intros; rfl) (by intros; trivial)
  have selected := (optionalWhen_realizable (record arity (fun _ => arrayPosition vertices))).onResults inputs
    (fun _ _ => True)
    (fun name sizes arguments => match name with
      | false => decide (enabled (fun coordinate => arguments.val (some coordinate)))
      | true => clauseFactScope domainFormula clauseFormulas enumeration wires clauses localTuple sizes (arguments.val none))
    (by intros; trivial) (by
      intro name
      cases name
      · exact enabledReady
      · exact scopeReady)
  apply selected.withSpecification (fun _ _ => True) computation.compute (by intros; trivial)
  intro sizes arguments valid
  by_cases related : enabled (fun coordinate => arguments (some coordinate))
  · simp [onResults, optionalWhen, computation, clauseFact, enabled] at related ⊢
  · simp [onResults, optionalWhen, computation, clauseFact, enabled] at related ⊢

omit [L.IsRelational] [Finite Carrier] in
theorem clauseFact_some_iff (wires clauses : MvPolynomial Parameter ℕ) (symbol : L.Relations arity)
    (localTuple : Fin arity → Pool (Carrier := Carrier) domainFormula clauseFormulas) (sizes : Parameter → ℕ)
    (clause : Fin (MvPolynomial.eval sizes clauses)) (pattern : Fin 3 → Bool)
    (tuple : Fin arity → Fin (MvPolynomial.eval sizes (allocationSize wires clauses dimension poolSize))) :
    (clauseFact domainFormula clauseFormulas enumeration wires clauses symbol localTuple).compute sizes
      ⟨(fun name => match name with | none => clause | some coordinate => pattern coordinate), trivial⟩ = some tuple ↔
      poolRelation domainFormula clauseFormulas (.inr pattern) symbol localTuple ∧
        clauseFactScope domainFormula clauseFormulas enumeration wires clauses localTuple sizes clause = tuple := by
  classical
  by_cases related : poolRelation domainFormula clauseFormulas (.inr pattern) symbol localTuple
  · simp only [clauseFact, related, ite_true, true_and]
    exact ⟨Option.some.inj, congrArg some⟩
  · simp [clauseFact, related]

end Polytime2.CSP.GadgetExpansion
