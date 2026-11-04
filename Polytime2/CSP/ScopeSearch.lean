import Polytime2.CSP.ScopeProgram
import Polytime2.Computation.BooleanBits
import Polytime2.Arrays.Contains

/-! # Certified existential search in dense scope tables

Search the canonical Boolean bits of a relation table for true. The codec's
tuple order is immaterial to existential quantification. The proof includes
nullary tables and empty positive-arity scope sets.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.CSP

open EncodedDomain Polytime2.Computation

theorem scope_encode_has_true_iff (arity : ℕ) (sizes : Unit → ℕ)
    (table : (Fin arity → Fin (sizes ())) → Bool) :
    true ∈ ArrayEncoding.bits ((scopeDomain arity).encode sizes table) ↔
      ∃ tuple, table tuple = true := by
  induction arity with
  | zero =>
    rw [scopeDomain_zero_bits]
    have bits (value : Bool) : ArrayEncoding.bits ((booleans : EncodedDomain Unit).encode sizes value) = [value] := by
      cases value <;> simp only [booleans, fixed_encode_bits] <;> decide
    rw [bits]
    simp only [List.mem_singleton]
    constructor
    · intro accepted
      exact ⟨Fin.elim0, accepted.symm⟩
    · rintro ⟨tuple, accepted⟩
      have empty : tuple = Fin.elim0 := Subsingleton.elim _ _
      exact (empty ▸ accepted).symm
  | succ arity hypothesis =>
    rw [scopeDomain_succ_bits, array_encode_bits, ArrayEncoding.bits_encode, List.mem_flatten]
    constructor
    · rintro ⟨bits, member, contains⟩
      obtain ⟨first, rfl⟩ := List.mem_ofFn.mp member
      obtain ⟨rest, accepted⟩ := (hypothesis (scopeSplit (sizes ()) arity table first)).mp contains
      exact ⟨Fin.cons first rest, accepted⟩
    · rintro ⟨tuple, accepted⟩
      refine ⟨ArrayEncoding.bits ((scopeDomain arity).encode sizes
        (scopeSplit (sizes ()) arity table (tuple 0))), List.mem_ofFn.mpr ⟨tuple 0, rfl⟩, ?_⟩
      apply (hypothesis _).mpr
      refine ⟨Fin.tail tuple, ?_⟩
      simpa only [scopeSplit, Equiv.coe_fn_mk, Fin.cons_self_tail] using accepted

variable {Parameter : Type} [Fintype Parameter]

/-- Decide whether some tuple is enabled in the supplied dense table. -/
noncomputable def scopeExists (vertices : MvPolynomial Parameter ℕ) (arity : ℕ) :
    Computation Parameter Unit := by
  classical
  exact unaryMap ((scopeDomain arity).substitute (fun _ => vertices)) booleans
    (fun _ _ => True) (fun _ table => decide (∃ tuple, table.val tuple = true))

theorem scopeExists_realizable (vertices : MvPolynomial Parameter ℕ) (arity : ℕ) :
    (scopeExists vertices arity).Realizable := by
  let domain := (scopeDomain arity).substitute (fun _ => vertices)
  let width := domain.widthPolynomial
  let computation := scopeExists vertices arity
  have flags := (encode_realizable domain).reinterpretOutput
    (booleans.arrayOfLength width) (fun _ word index => word.getLsbD index.val)
    (by
      have clog : Nat.clog 2 2 = 1 := by decide
      intros
      simp [EncodedDomain.width, arrayOfLength_widthPolynomial, booleans, encodingMap, unaryMap, clog, width]) (by
        intro sizes word
        rw [FirstFalse.boolean_bits]
        rfl)
  have searched := (arrayContains_realizable booleans width).onResults computation.inputDomains computation.precondition
    (fun name sizes arguments => match name with
      | false => fun index => (domain.encode sizes (arguments.val ())).getLsbD index.val
      | true => true) (by intros; trivial) (by
        intro name
        cases name
        · exact flags
        · exact (booleanOperation_realizable (fun _ : Empty → Bool => true)).onResults
            computation.inputDomains computation.precondition (fun empty => nomatch empty)
            (by intros; trivial) (fun empty => nomatch empty))
  apply searched.withSpecification computation.precondition computation.compute (by intros; trivial)
  intro sizes arguments valid
  apply Bool.eq_iff_iff.mpr
  simp only [onResults, arrayContains, computation, scopeExists, unaryMap, decide_eq_true_eq]
  have correct : true ∈ ArrayEncoding.bits (domain.encode sizes (arguments ())) ↔
      ∃ tuple, (arguments ()) tuple = true := by
    rw [substitute_encode_bits]
    exact scope_encode_has_true_iff arity _ _
  simpa only [ArrayEncoding.bits, List.mem_ofFn] using correct


end Polytime2.CSP
