import Polytime2.CSP.ScopeProgram
import Polytime2.Arrays.Operations

/-! # Certified lookup in fixed-arity scope tables

The arguments are an ordinary dense relation table and its finite coordinate
tuple. Repeated coordinates and nullary tables need no special preconditions.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.CSP

open EncodedDomain Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

noncomputable def scopeLookup (vertices : MvPolynomial Parameter ℕ) (arity : ℕ) :
    Computation Parameter (Option (Fin arity)) where
  inputDomains
    | none => (scopeDomain arity).substitute (fun _ => vertices)
    | some _ => arrayPosition vertices
  outputDomain := booleans
  precondition _ _ := True
  compute _ arguments := arguments.val none (fun coordinate => arguments.val (some coordinate))

theorem scopeLookup_realizable (vertices : MvPolynomial Parameter ℕ) (arity : ℕ) :
    (scopeLookup vertices arity).Realizable := by
  induction arity with
  | zero =>
    have interpreted := (copy_realizable (booleans : EncodedDomain Parameter)).reinterpretInputs
      (fun _ : Unit => (scopeDomain 0).substitute (fun _ => vertices))
      (fun _ _ table => table Fin.elim0) (by
        intro name sizes
        have widths := congrArg List.length
          (scopeDomain_substitute_zero_bits vertices sizes (fun _ => false))
        simpa only [ArrayEncoding.bits, List.length_ofFn, EncodedDomain.width, copy, unaryMap] using widths)
      (fun _ sizes table => scopeDomain_substitute_zero_bits vertices sizes table)
      (fun _ _ => True) (by intros; trivial)
    have selected := interpreted.onArguments (scopeLookup vertices 0).inputDomains (fun _ _ => True)
      (fun _ => none) (by intros; rfl) (by intros; trivial)
    apply selected.withSpecification (fun _ _ => True) (scopeLookup vertices 0).compute (by intros; trivial)
    intro sizes arguments valid
    change (arguments none) Fin.elim0 = (arguments none) (fun coordinate => arguments (some coordinate))
    have empty : (fun coordinate : Fin 0 => arguments (some coordinate)) =
        (Fin.elim0 : Fin 0 → Fin (MvPolynomial.eval sizes vertices)) := Subsingleton.elim _ _
    rw [empty]
  | succ arity hypothesis =>
    let smaller := (scopeDomain arity).substitute (fun _ => vertices)
    let inputs := (scopeLookup vertices (arity + 1)).inputDomains
    have split := (copy_realizable (smaller.arrayOfLength vertices)).reinterpretInputs
      (fun _ : Unit => (scopeDomain (arity + 1)).substitute (fun _ => vertices))
      (fun _ sizes table => fun first rest => table (Fin.cons first rest)) (by
        intro name sizes
        have widths := congrArg List.length
          (scopeDomain_substitute_succ_bits vertices arity sizes (fun _ => false))
        simpa only [ArrayEncoding.bits, List.length_ofFn, EncodedDomain.width, copy, unaryMap, smaller] using widths)
      (fun _ sizes table => scopeDomain_substitute_succ_bits vertices arity sizes table)
      (fun _ _ => True) (by intros; trivial)
    have row := (Realizable.Internal.arrayLookupWithIndex_realizable smaller (arrayPosition vertices)
      (fun _ coordinate => coordinate.val) (arrayPosition_value vertices) vertices).onResults inputs (fun _ _ => True)
      (fun name _ arguments => match name with
        | false => arguments.val (some 0)
        | true => fun first rest => arguments.val none (Fin.cons first rest))
      (by intro sizes arguments; exact (arguments.val (some 0)).isLt) (by
        intro name
        cases name
        · exact Realizable.argument inputs (some 0) (fun _ _ => True)
        · exact split.onArguments inputs (fun _ _ => True) (fun _ => none)
            (by intros; rfl) (by intros; trivial))
    have selected := hypothesis.onResults inputs (fun _ _ => True)
      (fun name _ arguments => match name with
        | none => fun rest => arguments.val none (Fin.cons (arguments.val (some 0)) rest)
        | some coordinate => arguments.val (some coordinate.succ)) (by intros; trivial) (by
          intro name
          cases name with
          | none =>
            exact row.withSpecification (fun _ _ => True) _ (by intros; trivial) (by intros; rfl)
          | some coordinate => exact Realizable.argument inputs (some coordinate.succ) (fun _ _ => True))
    apply selected.withSpecification (fun _ _ => True) (scopeLookup vertices (arity + 1)).compute
      (by intros; trivial)
    intro sizes arguments valid
    change arguments none (Fin.cons (arguments (some 0)) (fun coordinate => arguments (some coordinate.succ))) =
      arguments none (fun coordinate => arguments (some coordinate))
    apply congrArg (arguments none)
    funext coordinate
    exact Fin.cases rfl (fun _ => rfl) coordinate

end Polytime2.CSP
