import Polytime2.CSP.GadgetExpansionAllocation
import Polytime2.CSP.GadgetPositions
import Polytime2.Primitives.FiniteOperations

/-! # Endpoints of the uniform gadget equations

Each endpoint is an ordinary allocated variable. Fixed pool choices may depend
on the three literal signs, but not on unbounded runtime data. Their finite
tables and the existing allocation address programs supply the certificates.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.CSP.GadgetExpansion

open FirstOrder FirstOrder.Language EncodedDomain Polytime2.Computation GadgetAllocation

variable {Parameter Argument : Type} [Fintype Parameter] [Fintype Argument]
variable {poolSize : ℕ}

private noncomputable def poolChoice (choose : (Argument → Bool) → Fin poolSize) :
    Computation Parameter Argument where
  inputDomains _ := booleans
  outputDomain := arrayPosition (MvPolynomial.C poolSize)
  precondition _ _ := True
  compute sizes arguments := ⟨(choose arguments.val).val, by
    simpa only [MvPolynomial.eval_C] using (choose arguments.val).isLt⟩

private theorem poolChoice_realizable (choose : (Argument → Bool) → Fin poolSize) :
    (poolChoice (Parameter := Parameter) choose).Realizable := by
  let output : EncodedDomain Empty := arrayPosition (MvPolynomial.C poolSize)
  let operation (values : Argument → Bool) : output.Carrier Empty.elim :=
    ⟨(choose values).val, by simpa only [MvPolynomial.eval_C] using (choose values).isLt⟩
  have raw := (finiteOperation_realizable (fun _ : Argument => booleans) output operation).withConstantSizes
    (Parameter := Parameter)
  have inputs := raw.reinterpretInputs (fun _ => booleans) (fun _ _ value => value)
    (by intros; simp [withConstantSizes, finiteOperation, booleans, width])
    (by intros; simp [withConstantSizes, finiteOperation, constant_encode_bits, booleans, fixed_encode_bits])
    (fun _ _ => True) (by intros; trivial)
  have result := inputs.reinterpretOutput (arrayPosition (MvPolynomial.C poolSize))
    (fun sizes value => ⟨value.val, by simpa only [MvPolynomial.eval_C] using value.isLt⟩)
    (by intros; simp [reinterpretInputs, withConstantSizes, finiteOperation, output, arrayPosition,
      EncodedDomain.constant, width, boundedIndexOfWidth])
    (by
      intro sizes value
      simp only [reinterpretInputs, withConstantSizes, finiteOperation, output, constant_encode_bits,
        arrayPosition, boundedIndexOfWidth, BitVec.ofNatLT_eq_ofNat]
      exact congrArg (fun width => ArrayEncoding.bits (BitVec.ofNat width value.val)) (by simp))
  exact result.withSpecification (fun _ _ => True) _ (by intros; trivial) (by intros; rfl)

variable {L : Language.{0, 0}} [L.IsRelational]
variable {Carrier : Type} [L.Structure Carrier] [Finite Carrier] [Nonempty Carrier]
variable {dimension : ℕ}
variable (domainFormula : L.Formula (Fin dimension))
variable (clauseFormulas : (Fin 3 → Bool) → L.Formula (Fin 3 × Fin dimension))
variable (enumeration : Pool (Carrier := Carrier) domainFormula clauseFormulas ≃ Fin poolSize)

/-- Place a fixed pool variable at a source variable's domain occurrence. -/
noncomputable def domainPoolPosition (wires clauses : MvPolynomial Parameter ℕ)
    (value : Pool (Carrier := Carrier) domainFormula clauseFormulas) : Computation Parameter Unit where
  inputDomains _ := arrayPosition wires
  outputDomain := arrayPosition (allocationSize wires clauses dimension poolSize)
  precondition _ _ := True
  compute sizes arguments := allocationEquiv enumeration wires clauses dimension sizes
    (.inr (.inl (arguments.val ()), value))

omit [L.IsRelational] [Finite Carrier] [Nonempty Carrier] in
theorem domainPoolPosition_realizable (wires clauses : MvPolynomial Parameter ℕ)
    (value : Pool (Carrier := Carrier) domainFormula clauseFormulas) :
    (domainPoolPosition domainFormula clauseFormulas enumeration wires clauses value).Realizable := by
  let inputs := (domainPoolPosition domainFormula clauseFormulas enumeration wires clauses value).inputDomains
  have fixed := (poolChoice_realizable (Parameter := Parameter) (fun _ : Empty → Bool => enumeration value)).onResults
    inputs (fun _ _ => True) (fun empty => nomatch empty) (by intros; trivial) (fun empty => nomatch empty)
  have result := (domainPosition_realizable wires clauses dimension poolSize).onResults inputs (fun _ _ => True)
    (fun name sizes arguments => match name with
      | false => arguments.val ()
      | true => (poolChoice (fun _ : Empty → Bool => enumeration value)).compute sizes
          ⟨Empty.elim, trivial⟩) (by intros; trivial) (by
        intro name
        cases name
        · exact Realizable.argument inputs () (fun _ _ => True)
        · exact fixed)
  apply result.withSpecification (fun _ _ => True) _ (by intros; trivial)
  intro sizes arguments valid
  apply Fin.ext
  simp [onResults, domainPosition, allocationEquiv, layout_domain_val, poolChoice]

/-- Place a pool variable chosen by the three signs at a clause occurrence.
Only the finite choice table is specialization-fixed; the signs are runtime data. -/
noncomputable def clausePoolPosition (wires clauses : MvPolynomial Parameter ℕ)
    (choose : (Fin 3 → Bool) → Pool (Carrier := Carrier) domainFormula clauseFormulas) :
    Computation Parameter (Option (Fin 3)) where
  inputDomains name := match name with | none => arrayPosition clauses | some _ => booleans
  outputDomain := arrayPosition (allocationSize wires clauses dimension poolSize)
  precondition _ _ := True
  compute sizes arguments := allocationEquiv enumeration wires clauses dimension sizes
    (.inr (.inr (arguments.val none), choose (fun coordinate => arguments.val (some coordinate))))

omit [L.IsRelational] [Finite Carrier] [Nonempty Carrier] in
theorem clausePoolPosition_realizable (wires clauses : MvPolynomial Parameter ℕ)
    (choose : (Fin 3 → Bool) → Pool (Carrier := Carrier) domainFormula clauseFormulas) :
    (clausePoolPosition domainFormula clauseFormulas enumeration wires clauses choose).Realizable := by
  let inputs := (clausePoolPosition domainFormula clauseFormulas enumeration wires clauses choose).inputDomains
  have chosen := (poolChoice_realizable (Parameter := Parameter) (fun pattern => enumeration (choose pattern))).onArguments
    inputs (fun _ _ => True) some (by intros; rfl) (by intros; trivial)
  have result := (clausePosition_realizable wires clauses dimension poolSize).onResults inputs (fun _ _ => True)
    (fun name sizes arguments => match name with
      | false => arguments.val none
      | true => (poolChoice (fun pattern => enumeration (choose pattern))).compute sizes
          ⟨fun coordinate => arguments.val (some coordinate), trivial⟩) (by intros; trivial) (by
        intro name
        cases name
        · exact Realizable.argument inputs none (fun _ _ => True)
        · exact chosen)
  apply result.withSpecification (fun _ _ => True) _ (by intros; trivial)
  intro sizes arguments valid
  apply Fin.ext
  simp [onResults, clausePosition, allocationEquiv, layout_clause_val, poolChoice]

end Polytime2.CSP.GadgetExpansion
