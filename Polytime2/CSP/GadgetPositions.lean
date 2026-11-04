import Polytime2.CSP.GadgetLayout
import Polytime2.Arithmetic.NaturalPolynomial

/-! # Certified positions in the uniform gadget layout

The layout equivalence proves every address fits. The existing polynomial
evaluator certifies all arithmetic and derives its scratch widths internally.
Callers supply source variables or clause occurrences and actual pool indices.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.CSP.GadgetAllocation

open EncodedDomain Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

/-- Exact number of shared and fresh mathematical variables before gluing. -/
noncomputable def allocationSize (wires clauses : MvPolynomial Parameter ℕ) (dimension poolSize : ℕ) :
    MvPolynomial Parameter ℕ :=
  wires * MvPolynomial.C (dimension + poolSize) + clauses * MvPolynomial.C poolSize

/-- The mathematical layout at polynomial source dimensions, with only the
established equality of the resulting finite bounds transported. -/
noncomputable def allocationEquiv {Pool : Type} {poolSize : ℕ} (enumeration : Pool ≃ Fin poolSize)
    (wires clauses : MvPolynomial Parameter ℕ) (dimension : ℕ) (sizes : Parameter → ℕ) :
    ((Fin (MvPolynomial.eval sizes wires) × Fin dimension) ⊕
      ((Fin (MvPolynomial.eval sizes wires) ⊕ Fin (MvPolynomial.eval sizes clauses)) × Pool)) ≃
        Fin (MvPolynomial.eval sizes (allocationSize wires clauses dimension poolSize)) :=
  (layoutEquiv enumeration (MvPolynomial.eval sizes wires) (MvPolynomial.eval sizes clauses) dimension).trans
    (finCongr (by simp only [allocationSize, map_add, map_mul, MvPolynomial.eval_C]))

private def poolIndex (poolSize : ℕ) (sizes : Parameter → ℕ)
    (index : (arrayPosition (MvPolynomial.C poolSize)).Carrier sizes) : Fin poolSize :=
  ⟨index.val, by simpa only [MvPolynomial.eval_C] using index.isLt⟩

/-- Position of a shared block coordinate of one source variable. -/
noncomputable def sharedPosition (wires clauses : MvPolynomial Parameter ℕ) (dimension poolSize : ℕ)
    (coordinate : Fin dimension) : Computation Parameter Unit where
  inputDomains _ := arrayPosition wires
  outputDomain := arrayPosition (allocationSize wires clauses dimension poolSize)
  precondition _ _ := True
  compute sizes arguments := ⟨(arguments.val ()).val * (dimension + poolSize) + coordinate.val, by
    have bound := (layoutEquiv (Equiv.refl (Fin poolSize)) (MvPolynomial.eval sizes wires)
      (MvPolynomial.eval sizes clauses) dimension (.inl (arguments.val (), coordinate))).isLt
    simpa only [layout_shared_val, allocationSize, map_add, map_mul, MvPolynomial.eval_C] using bound⟩

theorem sharedPosition_realizable (wires clauses : MvPolynomial Parameter ℕ) (dimension poolSize : ℕ)
    (coordinate : Fin dimension) : (sharedPosition wires clauses dimension poolSize coordinate).Realizable := by
  let computation := sharedPosition wires clauses dimension poolSize coordinate
  let expression : MvPolynomial (Parameter ⊕ Unit) ℕ :=
    MvPolynomial.X (.inr ()) * MvPolynomial.C (dimension + poolSize) + MvPolynomial.C coordinate.val
  have ready := (polynomialPosition_realizable (fun _ : Unit => wires) expression
    (allocationSize wires clauses dimension poolSize)).onArguments computation.inputDomains (fun _ _ => True)
    id (by intros; rfl) (by
      intro sizes arguments
      have bound := (computation.compute sizes arguments).isLt
      simpa [computation, sharedPosition, polynomialPosition, expression] using bound)
  apply ready.withSpecification (fun _ _ => True) computation.compute (by intros; trivial)
  intro sizes arguments valid
  apply Fin.ext
  simp [onResults, polynomialPosition, expression, computation, sharedPosition]

/-- The address program agrees with the mathematical layout, independently
of the fixed pool enumeration. -/
theorem sharedPosition_compute {Pool : Type} {poolSize : ℕ} (enumeration : Pool ≃ Fin poolSize)
    (wires clauses : MvPolynomial Parameter ℕ) (dimension : ℕ) (coordinate : Fin dimension)
    (sizes : Parameter → ℕ) (source : Fin (MvPolynomial.eval sizes wires)) :
    (sharedPosition wires clauses dimension poolSize coordinate).compute sizes ⟨fun _ => source, trivial⟩ =
      allocationEquiv enumeration wires clauses dimension sizes (.inl (source, coordinate)) := by
  apply Fin.ext
  simp [sharedPosition, allocationEquiv, layout_shared_val]

/-- A source variable and a pool coordinate select its domain-gadget variable. -/
noncomputable def domainPosition (wires clauses : MvPolynomial Parameter ℕ) (dimension poolSize : ℕ) :
    Computation Parameter Bool where
  inputDomains name := if name then arrayPosition (MvPolynomial.C poolSize) else arrayPosition wires
  outputDomain := arrayPosition (allocationSize wires clauses dimension poolSize)
  precondition _ _ := True
  compute sizes arguments :=
    ⟨(arguments.val false).val * (dimension + poolSize) + dimension + (arguments.val true).val, by
      have bound := (layoutEquiv (Equiv.refl (Fin poolSize)) (MvPolynomial.eval sizes wires)
        (MvPolynomial.eval sizes clauses) dimension
        (.inr (.inl (arguments.val false), poolIndex poolSize sizes (arguments.val true)))).isLt
      simpa only [layout_domain_val, Equiv.refl_apply, poolIndex, allocationSize, map_add, map_mul,
        MvPolynomial.eval_C] using bound⟩

theorem domainPosition_realizable (wires clauses : MvPolynomial Parameter ℕ) (dimension poolSize : ℕ) :
    (domainPosition wires clauses dimension poolSize).Realizable := by
  let computation := domainPosition wires clauses dimension poolSize
  let bounds : Bool → MvPolynomial Parameter ℕ := fun name => if name then MvPolynomial.C poolSize else wires
  let expression : MvPolynomial (Parameter ⊕ Bool) ℕ :=
    MvPolynomial.X (.inr false) * MvPolynomial.C (dimension + poolSize) +
      MvPolynomial.C dimension + MvPolynomial.X (.inr true)
  have ready := (polynomialPosition_realizable bounds expression
    (allocationSize wires clauses dimension poolSize)).onArguments computation.inputDomains (fun _ _ => True)
    id (by intro name; cases name <;> rfl) (by
      intro sizes arguments
      have bound := (computation.compute sizes arguments).isLt
      simpa [computation, domainPosition, polynomialPosition, expression] using bound)
  apply ready.withSpecification (fun _ _ => True) computation.compute (by intros; trivial)
  intro sizes arguments valid
  apply Fin.ext
  simp [onResults, polynomialPosition, expression, computation, domainPosition]

/-- A clause occurrence and a pool coordinate select its fresh variable. -/
noncomputable def clausePosition (wires clauses : MvPolynomial Parameter ℕ) (dimension poolSize : ℕ) :
    Computation Parameter Bool where
  inputDomains name := if name then arrayPosition (MvPolynomial.C poolSize) else arrayPosition clauses
  outputDomain := arrayPosition (allocationSize wires clauses dimension poolSize)
  precondition _ _ := True
  compute sizes arguments :=
    ⟨MvPolynomial.eval sizes wires * (dimension + poolSize) +
      (arguments.val false).val * poolSize + (arguments.val true).val, by
      have bound := (layoutEquiv (Equiv.refl (Fin poolSize)) (MvPolynomial.eval sizes wires)
        (MvPolynomial.eval sizes clauses) dimension
        (.inr (.inr (arguments.val false), poolIndex poolSize sizes (arguments.val true)))).isLt
      simpa only [layout_clause_val, Equiv.refl_apply, poolIndex, allocationSize, map_add, map_mul,
        MvPolynomial.eval_C] using bound⟩

theorem clausePosition_realizable (wires clauses : MvPolynomial Parameter ℕ) (dimension poolSize : ℕ) :
    (clausePosition wires clauses dimension poolSize).Realizable := by
  let computation := clausePosition wires clauses dimension poolSize
  let bounds : Bool → MvPolynomial Parameter ℕ := fun name => if name then MvPolynomial.C poolSize else clauses
  let expression : MvPolynomial (Parameter ⊕ Bool) ℕ :=
    MvPolynomial.rename Sum.inl wires * MvPolynomial.C (dimension + poolSize) +
      MvPolynomial.X (.inr false) * MvPolynomial.C poolSize + MvPolynomial.X (.inr true)
  have ready := (polynomialPosition_realizable bounds expression
    (allocationSize wires clauses dimension poolSize)).onArguments computation.inputDomains (fun _ _ => True)
    id (by intro name; cases name <;> rfl) (by
      intro sizes arguments
      have bound := (computation.compute sizes arguments).isLt
      simpa [computation, clausePosition, polynomialPosition, expression, MvPolynomial.eval_rename,
        Function.comp_def] using bound)
  apply ready.withSpecification (fun _ _ => True) computation.compute (by intros; trivial)
  intro sizes arguments valid
  apply Fin.ext
  simp [onResults, polynomialPosition, expression, computation, clausePosition,
    MvPolynomial.eval_rename, Function.comp_def]

end Polytime2.CSP.GadgetAllocation
