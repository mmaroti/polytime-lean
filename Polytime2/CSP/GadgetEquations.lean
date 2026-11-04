import Polytime2.CSP.GadgetEquationEndpoints
import Polytime2.Arrays.BoundedPositions
import Polytime2.Computation.Records

/-! # Certified local allocation equations

Pool collapse and boundary identification return pairs of mathematical
allocated variables. The canonical equation codec uses bounded indices; its
narrowing from the address codec is supplied by the existing array rule.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.CSP.GadgetExpansion

open FirstOrder FirstOrder.Language EncodedDomain Polytime2.Computation GadgetAllocation

variable {Parameter InputName : Type} [Fintype Parameter] [Fintype InputName]

private theorem equation_realizable (vertices : MvPolynomial Parameter ℕ)
    {inputs : InputName → EncodedDomain Parameter}
    {left right : (sizes : Parameter → ℕ) → {_arguments : (name : InputName) → (inputs name).Carrier sizes // True} →
      Fin (MvPolynomial.eval sizes vertices)}
    (leftReady : (Computation.mk inputs (arrayPosition vertices) (fun _ _ => True) left).Realizable)
    (rightReady : (Computation.mk inputs (arrayPosition vertices) (fun _ _ => True) right).Realizable) :
    (Computation.mk inputs ((boundedIndex vertices).prod (boundedIndex vertices)) (fun _ _ => True)
      (fun sizes arguments => (left sizes arguments, right sizes arguments))).Realizable :=
  (leftReady.followedBy (arrayPositionToIndex_realizable vertices) rfl (by intros; trivial)).prodMk
    (rightReady.followedBy (arrayPositionToIndex_realizable vertices) rfl (by intros; trivial))

variable {L : Language.{0, 0}} [L.IsRelational]
variable {Carrier : Type} [L.Structure Carrier] [Finite Carrier] [Nonempty Carrier]
variable {dimension poolSize : ℕ}
variable (domainFormula : L.Formula (Fin dimension))
variable (clauseFormulas : (Fin 3 → Bool) → L.Formula (Fin 3 × Fin dimension))
variable (enumeration : Pool (Carrier := Carrier) domainFormula clauseFormulas ≃ Fin poolSize)

/-- Collapse one domain pool slot onto the selected domain component. -/
noncomputable def domainProjectionEquation (wires clauses : MvPolynomial Parameter ℕ)
    (value : Pool (Carrier := Carrier) domainFormula clauseFormulas) : Computation Parameter Unit where
  inputDomains _ := arrayPosition wires
  outputDomain := (boundedIndex (allocationSize wires clauses dimension poolSize)).prod
    (boundedIndex (allocationSize wires clauses dimension poolSize))
  precondition _ _ := True
  compute sizes arguments :=
    ((domainPoolPosition domainFormula clauseFormulas enumeration wires clauses value).compute sizes arguments,
      (domainPoolPosition domainFormula clauseFormulas enumeration wires clauses
        (selectedPool domainFormula clauseFormulas (.inl ()) value)).compute sizes arguments)

omit [L.IsRelational] [Finite Carrier] in
theorem domainProjectionEquation_realizable (wires clauses : MvPolynomial Parameter ℕ)
    (value : Pool (Carrier := Carrier) domainFormula clauseFormulas) :
    (domainProjectionEquation domainFormula clauseFormulas enumeration wires clauses value).Realizable :=
  equation_realizable _
    (domainPoolPosition_realizable domainFormula clauseFormulas enumeration wires clauses value)
    (domainPoolPosition_realizable domainFormula clauseFormulas enumeration wires clauses
      (selectedPool domainFormula clauseFormulas (.inl ()) value))

/-- Identify a domain boundary coordinate with its shared source coordinate. -/
noncomputable def domainBoundaryEquation (wires clauses : MvPolynomial Parameter ℕ)
    (coordinate : Fin dimension) : Computation Parameter Unit where
  inputDomains _ := arrayPosition wires
  outputDomain := (boundedIndex (allocationSize wires clauses dimension poolSize)).prod
    (boundedIndex (allocationSize wires clauses dimension poolSize))
  precondition _ _ := True
  compute sizes arguments :=
    ((domainPoolPosition domainFormula clauseFormulas enumeration wires clauses
        (poolBoundary (Carrier := Carrier) domainFormula clauseFormulas (.inl ()) coordinate)).compute sizes arguments,
      (sharedPosition wires clauses dimension poolSize coordinate).compute sizes arguments)

omit [L.IsRelational] [Nonempty Carrier] in
theorem domainBoundaryEquation_realizable (wires clauses : MvPolynomial Parameter ℕ)
    (coordinate : Fin dimension) :
    (domainBoundaryEquation domainFormula clauseFormulas enumeration wires clauses coordinate).Realizable :=
  equation_realizable _
    (domainPoolPosition_realizable domainFormula clauseFormulas enumeration wires clauses
      (poolBoundary (Carrier := Carrier) domainFormula clauseFormulas (.inl ()) coordinate))
    (sharedPosition_realizable wires clauses dimension poolSize coordinate)

/-- Collapse a clause pool slot according to the actual literal signs. -/
noncomputable def clauseProjectionEquation (wires clauses : MvPolynomial Parameter ℕ)
    (value : Pool (Carrier := Carrier) domainFormula clauseFormulas) : Computation Parameter (Option (Fin 3)) where
  inputDomains name := match name with | none => arrayPosition clauses | some _ => booleans
  outputDomain := (boundedIndex (allocationSize wires clauses dimension poolSize)).prod
    (boundedIndex (allocationSize wires clauses dimension poolSize))
  precondition _ _ := True
  compute sizes arguments :=
    ((clausePoolPosition domainFormula clauseFormulas enumeration wires clauses (fun _ => value)).compute sizes arguments,
      (clausePoolPosition domainFormula clauseFormulas enumeration wires clauses
        (fun pattern => selectedPool domainFormula clauseFormulas (.inr pattern) value)).compute sizes arguments)

omit [L.IsRelational] [Finite Carrier] in
theorem clauseProjectionEquation_realizable (wires clauses : MvPolynomial Parameter ℕ)
    (value : Pool (Carrier := Carrier) domainFormula clauseFormulas) :
    (clauseProjectionEquation domainFormula clauseFormulas enumeration wires clauses value).Realizable :=
  equation_realizable _
    (clausePoolPosition_realizable domainFormula clauseFormulas enumeration wires clauses (fun _ => value))
    (clausePoolPosition_realizable domainFormula clauseFormulas enumeration wires clauses
      (fun pattern => selectedPool domainFormula clauseFormulas (.inr pattern) value))

/-- Identify one clause boundary with its literal's shared source coordinate.
The source variable and occurrence are ordinary inputs, so repeated literals
require no special treatment. -/
noncomputable def clauseBoundaryEquation (wires clauses : MvPolynomial Parameter ℕ)
    (coordinate : Fin 3 × Fin dimension) : Computation Parameter (Unit ⊕ Option (Fin 3)) where
  inputDomains name := match name with
    | .inl _ => arrayPosition wires
    | .inr clauseName => match clauseName with
      | none => arrayPosition clauses
      | some _ => booleans
  outputDomain := (boundedIndex (allocationSize wires clauses dimension poolSize)).prod
    (boundedIndex (allocationSize wires clauses dimension poolSize))
  precondition _ _ := True
  compute sizes arguments :=
    ((clausePoolPosition domainFormula clauseFormulas enumeration wires clauses
        (fun pattern => poolBoundary (Carrier := Carrier) domainFormula clauseFormulas (.inr pattern) coordinate)).compute sizes
          ⟨fun name => arguments.val (.inr name), trivial⟩,
      (sharedPosition wires clauses dimension poolSize coordinate.2).compute sizes
        ⟨fun _ => arguments.val (.inl ()), trivial⟩)

omit [L.IsRelational] [Nonempty Carrier] in
theorem clauseBoundaryEquation_realizable (wires clauses : MvPolynomial Parameter ℕ)
    (coordinate : Fin 3 × Fin dimension) :
    (clauseBoundaryEquation domainFormula clauseFormulas enumeration wires clauses coordinate).Realizable := by
  let inputs := (clauseBoundaryEquation domainFormula clauseFormulas enumeration wires clauses coordinate).inputDomains
  have localReady := (clausePoolPosition_realizable domainFormula clauseFormulas enumeration wires clauses
    (fun pattern => poolBoundary (Carrier := Carrier) domainFormula clauseFormulas (.inr pattern) coordinate)).onArguments
      inputs (fun _ _ => True) Sum.inr (by intros; rfl) (by intros; trivial)
  have sharedReady := (sharedPosition_realizable wires clauses dimension poolSize coordinate.2).onArguments
    inputs (fun _ _ => True) (fun _ => .inl ()) (by intros; rfl) (by intros; trivial)
  exact equation_realizable _ localReady sharedReady

end Polytime2.CSP.GadgetExpansion
