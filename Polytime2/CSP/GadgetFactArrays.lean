import Polytime2.CSP.GadgetFacts
import Polytime2.SAT.TseitinEncoding
import Polytime2.Arrays.Tabulate
import Polytime2.Arrays.FlattenRecords
import Polytime2.Arrays.Append
import Polytime2.Arrays.Operations

/-! # Certified arrays of fresh gadget facts

Tabulate each source variable's fixed domain facts and each clause occurrence's
fixed local tuples. Flatten the records and append both arrays using the
existing canonical array operations. No raw tape wiring is introduced.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.CSP.GadgetExpansion

open FirstOrder FirstOrder.Language EncodedDomain Polytime2.Computation GadgetAllocation

variable {L : Language.{0, 0}} [L.IsRelational]
variable {Carrier : Type} [L.Structure Carrier] [Finite Carrier] [Nonempty Carrier]
variable {dimension poolSize arity localCount : ℕ}
variable (domainFormula : L.Formula (Fin dimension))
variable (clauseFormulas : (Fin 3 → Bool) → L.Formula (Fin 3 × Fin dimension))
variable (enumeration : Pool (Carrier := Carrier) domainFormula clauseFormulas ≃ Fin poolSize)
variable (localTuples : Fin localCount → Fin arity → Pool (Carrier := Carrier) domainFormula clauseFormulas)
variable {Parameter : Type} [Fintype Parameter]

/-- The fixed family of domain facts at every source variable. -/
noncomputable def domainFactRows (wires clauses : MvPolynomial Parameter ℕ) (symbol : L.Relations arity) :=
  arrayTabulate (Empty.elim : Empty → EncodedDomain Parameter)
    (record localCount (fun _ => relationFactDomain (allocationSize wires clauses dimension poolSize) arity)) wires
    (fun sizes _ source index =>
      (domainFact domainFormula clauseFormulas enumeration wires clauses symbol (localTuples index)).compute sizes
        ⟨fun _ => source, trivial⟩)

omit [L.IsRelational] [Finite Carrier] in
theorem domainFactRows_realizable (wires clauses : MvPolynomial Parameter ℕ) (symbol : L.Relations arity) :
    (domainFactRows domainFormula clauseFormulas enumeration localTuples wires clauses symbol).Realizable := by
  apply arrayTabulate_realizable
  apply Realizable.recordOutputs
  intro index
  have selected := (domainFact_realizable domainFormula clauseFormulas enumeration wires clauses symbol
    (localTuples index)).onArguments
    (Sum.elim (Empty.elim : Empty → EncodedDomain Parameter) (fun _ : Unit => arrayPosition wires))
    (fun _ _ => True) (fun _ => .inr ()) (by intros; rfl) (by intros; trivial)
  exact selected.withSpecification (fun _ _ => True) _ (by intros; trivial) (by intros; rfl)

private noncomputable def clauseRowInputs (wires clauses : MvPolynomial Parameter ℕ) :
    Unit ⊕ Unit → EncodedDomain Parameter :=
  Sum.elim (fun _ => (SAT.clauseDomain wires).arrayOfLength clauses) (fun _ => arrayPosition clauses)

/-- One clause occurrence contributes a fixed record of optional local facts. -/
noncomputable def clauseFactRow (wires clauses : MvPolynomial Parameter ℕ) (symbol : L.Relations arity) :
    Computation Parameter (Unit ⊕ Unit) where
  inputDomains := clauseRowInputs wires clauses
  outputDomain := record localCount (fun _ => relationFactDomain (allocationSize wires clauses dimension poolSize) arity)
  precondition _ _ := True
  compute sizes arguments index :=
    (clauseFact domainFormula clauseFormulas enumeration wires clauses symbol (localTuples index)).compute sizes
      ⟨(fun name => match name with
        | none => arguments.val (.inr ())
        | some coordinate => (arguments.val (.inl ()) (arguments.val (.inr ())) coordinate).2), trivial⟩

omit [L.IsRelational] [Finite Carrier] in
theorem clauseFactRow_realizable (wires clauses : MvPolynomial Parameter ℕ) (symbol : L.Relations arity) :
    (clauseFactRow domainFormula clauseFormulas enumeration localTuples wires clauses symbol).Realizable := by
  let computation := clauseFactRow domainFormula clauseFormulas enumeration localTuples wires clauses symbol
  let inputs := computation.inputDomains
  have lookup := (Realizable.Internal.arrayLookupWithIndex_realizable (SAT.clauseDomain wires) (arrayPosition clauses)
    (fun _ index => index.val) (arrayPosition_value clauses) clauses).onResults inputs (fun _ _ => True)
    (fun name _ arguments => match name with
      | false => arguments.val (.inr ())
      | true => arguments.val (.inl ())) (by
        intro sizes arguments
        exact (arguments.val (.inr ())).isLt) (by
          intro name
          cases name
          · exact Realizable.argument inputs (.inr ()) (fun _ _ => True)
          · exact Realizable.argument inputs (.inl ()) (fun _ _ => True))
  have sign (coordinate : Fin 3) := (lookup.followedBy
    (recordProjection_realizable 3 (fun _ => SAT.literalDomain wires) coordinate) rfl (by intros; trivial)).snd
  have each (index : Fin localCount) :=
    (clauseFact_realizable domainFormula clauseFormulas enumeration wires clauses symbol (localTuples index)).onResults
      inputs (fun _ _ => True)
      (fun name _ arguments => match name with
        | none => arguments.val (.inr ())
        | some coordinate => (arguments.val (.inl ()) (arguments.val (.inr ())) coordinate).2)
      (by intros; trivial) (by
        intro name
        cases name with
        | none => exact Realizable.argument inputs (.inr ()) (fun _ _ => True)
        | some coordinate =>
          exact (sign coordinate).withSpecification (fun _ _ => True) _
            (by intros; trivial) (by intros; rfl))
  have combined := Realizable.recordOutputs inputs localCount
    (fun _ => relationFactDomain (allocationSize wires clauses dimension poolSize) arity) (fun _ _ => True)
    (fun index sizes arguments => (computation.compute sizes arguments) index)
    (fun index => (each index).withSpecification (fun _ _ => True) _ (by intros; trivial) (by intros; rfl))
  exact combined

/-- Read each actual clause and tabulate its fixed optional fact record. -/
noncomputable def clauseFactRows (wires clauses : MvPolynomial Parameter ℕ) (symbol : L.Relations arity) :=
  arrayTabulate (fun _ : Unit => (SAT.clauseDomain wires).arrayOfLength clauses)
    (record localCount (fun _ => relationFactDomain (allocationSize wires clauses dimension poolSize) arity)) clauses
    (fun sizes arguments clause =>
      (clauseFactRow domainFormula clauseFormulas enumeration localTuples wires clauses symbol).compute sizes
        ⟨(fun name => match name with | .inl name => arguments name | .inr _ => clause), trivial⟩)

omit [L.IsRelational] [Finite Carrier] in
theorem clauseFactRows_realizable (wires clauses : MvPolynomial Parameter ℕ) (symbol : L.Relations arity) :
    (clauseFactRows domainFormula clauseFormulas enumeration localTuples wires clauses symbol).Realizable := by
  apply arrayTabulate_realizable
  exact (clauseFactRow_realizable domainFormula clauseFormulas enumeration localTuples wires clauses symbol).withSpecification
    (fun _ _ => True) _ (by intros; trivial) (by intros; rfl)

/-- All optional facts for one target symbol, at their fixed polynomial count. -/
noncomputable def gadgetFactArray (wires clauses : MvPolynomial Parameter ℕ) (symbol : L.Relations arity) :=
  let element := relationFactDomain (allocationSize wires clauses dimension poolSize) arity
  let context : Unit → EncodedDomain Parameter := fun _ => (SAT.clauseDomain wires).arrayOfLength clauses
  let domains := ((domainFactRows domainFormula clauseFormulas enumeration localTuples wires clauses symbol).followedBy
    (arrayFlattenRecords element localCount wires) rfl (by intros; trivial)).onResults context
      (fun _ _ => True) (fun empty => nomatch empty) (by intros; trivial)
  let clausesReady := (clauseFactRows domainFormula clauseFormulas enumeration localTuples wires clauses symbol).followedBy
    (arrayFlattenRecords element localCount clauses) rfl (by intros; trivial)
  (Computation.mk context
    ((element.arrayOfLength (wires * MvPolynomial.C localCount)).prod
      (element.arrayOfLength (clauses * MvPolynomial.C localCount))) (fun _ _ => True)
    (fun sizes arguments => (domains.compute sizes arguments, clausesReady.compute sizes arguments))).followedBy
      (arrayAppend element (wires * MvPolynomial.C localCount) (clauses * MvPolynomial.C localCount))
      rfl (by intros; trivial)

omit [L.IsRelational] [Finite Carrier] in
theorem gadgetFactArray_realizable (wires clauses : MvPolynomial Parameter ℕ) (symbol : L.Relations arity) :
    (gadgetFactArray domainFormula clauseFormulas enumeration localTuples wires clauses symbol).Realizable := by
  let element := relationFactDomain (allocationSize wires clauses dimension poolSize) arity
  have domains := ((domainFactRows_realizable domainFormula clauseFormulas enumeration localTuples wires clauses symbol).followedBy
    (arrayFlattenRecords_realizable element localCount wires) rfl (by intros; trivial)).onResults
      (fun _ : Unit => (SAT.clauseDomain wires).arrayOfLength clauses) (fun _ _ => True)
      (fun empty => nomatch empty) (by intros; trivial) (fun empty => nomatch empty)
  have clausesReady := (clauseFactRows_realizable domainFormula clauseFormulas enumeration localTuples wires clauses symbol).followedBy
    (arrayFlattenRecords_realizable element localCount clauses) rfl (by intros; trivial)
  exact (domains.prodMk clausesReady).followedBy
    (arrayAppend_realizable element (wires * MvPolynomial.C localCount) (clauses * MvPolynomial.C localCount))
    rfl (by intros; trivial)

omit [L.IsRelational] [Finite Carrier] in
/-- Flattening and concatenation retain precisely the per-occurrence facts. -/
theorem gadgetFactArray_list (wires clauses : MvPolynomial Parameter ℕ) (symbol : L.Relations arity)
    (sizes : Parameter → ℕ) (input : ((SAT.clauseDomain wires).arrayOfLength clauses).Carrier sizes) :
    List.ofFn ((gadgetFactArray domainFormula clauseFormulas enumeration localTuples wires clauses symbol).compute sizes
      ⟨fun _ => input, trivial⟩) =
      (List.ofFn (fun source : Fin (MvPolynomial.eval sizes wires) => List.ofFn (fun index : Fin localCount =>
        (domainFact domainFormula clauseFormulas enumeration wires clauses symbol (localTuples index)).compute sizes
          ⟨fun _ => source, trivial⟩))).flatten ++
      (List.ofFn (fun clause : Fin (MvPolynomial.eval sizes clauses) => List.ofFn (fun index : Fin localCount =>
        (clauseFact domainFormula clauseFormulas enumeration wires clauses symbol (localTuples index)).compute sizes
          ⟨(fun name => match name with
            | none => clause | some coordinate => (input clause coordinate).2), trivial⟩))).flatten := by
  dsimp only [gadgetFactArray, followedBy]
  rw [arrayAppend_list]
  dsimp only [onResults]
  rw [arrayFlattenRecords_list, arrayFlattenRecords_list]
  rfl

omit [L.IsRelational] [Finite Carrier] in
/-- An asserted raw scope comes from one domain or clause occurrence and one
of the selected fixed local tuples. -/
theorem gadgetFactArray_some_iff (wires clauses : MvPolynomial Parameter ℕ) (symbol : L.Relations arity)
    (sizes : Parameter → ℕ) (input : ((SAT.clauseDomain wires).arrayOfLength clauses).Carrier sizes)
    (tuple : Fin arity → Fin (MvPolynomial.eval sizes (allocationSize wires clauses dimension poolSize))) :
    (∃ index, (gadgetFactArray domainFormula clauseFormulas enumeration localTuples wires clauses symbol).compute sizes
      ⟨fun _ => input, trivial⟩ index = some tuple) ↔
      (∃ source : Fin (MvPolynomial.eval sizes wires), ∃ index : Fin localCount,
        poolRelation domainFormula clauseFormulas (.inl ()) symbol (localTuples index) ∧
          domainFactScope domainFormula clauseFormulas enumeration wires clauses (localTuples index) sizes source = tuple) ∨
      (∃ clause : Fin (MvPolynomial.eval sizes clauses), ∃ index : Fin localCount,
        poolRelation domainFormula clauseFormulas (.inr (fun coordinate => (input clause coordinate).2))
          symbol (localTuples index) ∧
        clauseFactScope domainFormula clauseFormulas enumeration wires clauses (localTuples index) sizes clause = tuple) := by
  rw [← List.mem_ofFn, gadgetFactArray_list]
  simp [List.mem_ofFn]
  apply or_congr
  · apply exists_congr
    intro source
    apply exists_congr
    intro index
    exact domainFact_some_iff domainFormula clauseFormulas enumeration wires clauses symbol
      (localTuples index) sizes source tuple
  · apply exists_congr
    intro clause
    apply exists_congr
    intro index
    exact clauseFact_some_iff domainFormula clauseFormulas enumeration wires clauses symbol
      (localTuples index) sizes clause (fun coordinate => (input clause coordinate).2) tuple

end Polytime2.CSP.GadgetExpansion
