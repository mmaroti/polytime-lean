import Polytime2.CSP.Encoding
import Polytime2.Arrays.Tabulate
import Polytime2.Computation.RecordArguments

/-! # Certified construction of arbitrary fixed-arity dense relation tables

A certified Boolean query receives immutable context and one coordinate per
argument. Nested tabulation returns exactly the canonical scope-table codec.
The arity is specialization-fixed, while the vertex count is a size polynomial.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.CSP

open EncodedDomain Polytime2.Computation

variable {Parameter Context : Type} [Fintype Parameter] [Fintype Context]

noncomputable def scopeQuery (context : Context → EncodedDomain Parameter)
    (vertices : MvPolynomial Parameter ℕ) (arity : ℕ)
    (query : ∀ sizes, (∀ name, (context name).Carrier sizes) →
      (Fin arity → Fin (MvPolynomial.eval sizes vertices)) → Bool) :
    Computation Parameter (Context ⊕ Fin arity) where
  inputDomains := Sum.elim context (fun _ => arrayPosition vertices)
  outputDomain := booleans
  precondition _ _ := True
  compute sizes arguments := query sizes (fun name => arguments.val (.inl name))
    (fun coordinate => arguments.val (.inr coordinate))

/-- Dense tabulation with exactly the existing canonical table bits. -/
noncomputable def scopeTabulate (context : Context → EncodedDomain Parameter)
    (vertices : MvPolynomial Parameter ℕ) (arity : ℕ)
    (query : ∀ sizes, (∀ name, (context name).Carrier sizes) →
      (Fin arity → Fin (MvPolynomial.eval sizes vertices)) → Bool) : Computation Parameter Context where
  inputDomains := context
  outputDomain := (scopeDomain arity).substitute (fun _ => vertices)
  precondition _ _ := True
  compute sizes arguments := query sizes arguments.val

/-- The nullary scope table is exactly one Boolean bit after substitution. -/
theorem scopeDomain_substitute_zero_bits (vertices : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (table : (Fin 0 → Fin (MvPolynomial.eval sizes vertices)) → Bool) :
    ArrayEncoding.bits (((scopeDomain 0).substitute (fun _ => vertices)).encode sizes table) =
      ArrayEncoding.bits (booleans.encode sizes (table Fin.elim0)) := by
  rw [substitute_encode_bits, scopeDomain_zero_bits]
  simp only [booleans, fixed_encode_bits]

/-- Currying the first coordinate preserves exactly the canonical table bits. -/
theorem scopeDomain_substitute_succ_bits (vertices : MvPolynomial Parameter ℕ) (arity : ℕ)
    (sizes : Parameter → ℕ) (table : (Fin (arity + 1) → Fin (MvPolynomial.eval sizes vertices)) → Bool) :
    ArrayEncoding.bits (((scopeDomain (arity + 1)).substitute (fun _ => vertices)).encode sizes table) =
      ArrayEncoding.bits ((((scopeDomain arity).substitute (fun _ => vertices)).arrayOfLength vertices).encode
        sizes (fun first rest => table (Fin.cons first rest))) := by
  simp only [substitute_encode_bits, scopeDomain_succ_bits, array_encode_bits,
    arrayOfLength_encode_bits, ArrayEncoding.bits_encode]
  rfl

/-- Fixed-arity scope queries lift to dense tables by ordinary array tabulation.
Nullary tables retain their one Boolean bit, including at zero vertices. -/
theorem scopeTabulate_realizable (context : Context → EncodedDomain Parameter)
    (vertices : MvPolynomial Parameter ℕ) (arity : ℕ)
    (query : ∀ sizes, (∀ name, (context name).Carrier sizes) →
      (Fin arity → Fin (MvPolynomial.eval sizes vertices)) → Bool)
    (ready : (scopeQuery context vertices arity query).Realizable) :
    (scopeTabulate context vertices arity query).Realizable := by
  induction arity generalizing Context with
  | zero =>
    have queried := ready.onResults context (fun _ _ => True)
      (fun name _ arguments => match name with
        | .inl name => arguments.val name
        | .inr empty => empty.elim0) (by intros; trivial) (by
          intro name
          cases name with
          | inl name => exact Realizable.argument context name (fun _ _ => True)
          | inr empty => exact empty.elim0)
    have converted := queried.reinterpretOutput ((scopeDomain 0).substitute (fun _ => vertices))
      (fun _ value _ => value) (by
        have clog : Nat.clog 2 2 = 1 := by decide
        simp [onResults, scopeQuery, EncodedDomain.width, scopeDomain_widthPolynomial, booleans, clog]) (by
        intro sizes value
        change ArrayEncoding.bits ((((scopeDomain 0).substitute (fun _ => vertices)).encode sizes (fun _ => value))) =
          ArrayEncoding.bits (booleans.encode sizes value)
        rw [substitute_encode_bits, scopeDomain_zero_bits]
        simp only [booleans, fixed_encode_bits])
    apply converted.withSpecification (fun _ _ => True) _ (by intros; trivial)
    intro sizes arguments valid
    funext tuple
    simp only [reinterpretOutput, onResults, scopeQuery]
    congr 1
    exact Subsingleton.elim _ _
  | succ arity hypothesis =>
    let extended : Context ⊕ Unit → EncodedDomain Parameter := Sum.elim context (fun _ => arrayPosition vertices)
    let remainingQuery sizes (arguments : ∀ name, (extended name).Carrier sizes)
        (rest : Fin arity → Fin (MvPolynomial.eval sizes vertices)) :=
      query sizes (fun name => arguments (.inl name)) (Fin.cons (arguments (.inr ())) rest)
    have queryReady : (scopeQuery extended vertices arity remainingQuery).Realizable := by
      let step := scopeQuery extended vertices arity remainingQuery
      have rearranged := ready.onArguments step.inputDomains step.precondition
        (fun name => match name with
          | .inl name => .inl (.inl name)
          | .inr coordinate => Fin.cases (.inl (.inr ())) (fun rest => .inr rest) coordinate)
        (by
          intro name
          cases name with
          | inl name => rfl
          | inr coordinate => exact Fin.cases rfl (fun _ => rfl) coordinate) (by intros; trivial)
      apply rearranged.withSpecification step.precondition step.compute (by intros; trivial)
      intro sizes arguments valid
      change query sizes _ _ = query sizes _ _
      congr 1
      funext coordinate
      exact Fin.cases rfl (fun _ => rfl) coordinate
    have nested := hypothesis extended remainingQuery queryReady
    have tabulated := arrayTabulate_realizable context
      ((scopeDomain arity).substitute (fun _ => vertices)) vertices
      (fun sizes arguments first rest => query sizes arguments (Fin.cons first rest)) nested
    have converted := tabulated.reinterpretOutput ((scopeDomain (arity + 1)).substitute (fun _ => vertices))
      (fun _ table tuple => table (tuple 0) (Fin.tail tuple)) (by
        intro sizes
        have lengths := congrArg List.length (scopeDomain_substitute_succ_bits vertices arity sizes (fun _ => false))
        simpa only [ArrayEncoding.bits, List.length_ofFn, EncodedDomain.width, arrayTabulate] using lengths) (by
        intro sizes table
        have correct := scopeDomain_substitute_succ_bits vertices arity sizes (fun tuple => table (tuple 0) (Fin.tail tuple))
        simp only [Fin.cons_zero, Fin.tail_cons] at correct
        have eta : (fun first rest => table first rest) = table := by
          funext first rest
          rfl
        rw [eta] at correct
        exact correct)
    apply converted.withSpecification (fun _ _ => True) _ (by intros; trivial)
    intro sizes arguments valid
    funext tuple
    simp only [reinterpretOutput, arrayTabulate, Fin.cons_self_tail]

end Polytime2.CSP
