import Polytime2.Complexity.WordArrays
import Polytime2.TM0.LocalComputation
import Polytime2.Arrays.Append
import Polytime2.Arrays.PositionPolynomial

/-! # Initial finite tape for a direct word verifier

The input is an ordinary word array. The result is its initial marked TM0 tape
on a symmetric interval containing the word and twice the time allowance.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity

open Turing EncodedDomain Polytime2.Computation Computation.Realizable.Internal

variable {Symbol State : Type} [Inhabited Symbol]
  [Fintype Symbol] [Fintype State]

private noncomputable abbrev wordLength : MvPolynomial Unit ℕ := MvPolynomial.X ()
noncomputable abbrev directRadius (time : MvPolynomial Unit ℕ) := 2 * time + wordLength
noncomputable abbrev directLength (time : MvPolynomial Unit ℕ) := directRadius time + (wordLength + (2 * time + 1))

theorem directLength_eval (time : MvPolynomial Unit ℕ) (sizes : Unit → ℕ) :
    MvPolynomial.eval sizes (directLength time) = 2 * MvPolynomial.eval sizes (directRadius time) + 1 := by
  simp [directLength, directRadius]; ring

omit [Fintype Symbol] in
private theorem initial_nth (word : List Symbol) (position : ℤ) :
    (Tape.mk₁ word).nth position = if position < 0 then default else word.getI position.toNat := by
  cases position with
  | ofNat position => simp [Tape.mk₁, Tape.mk₂, ListBlank.nth_mk]
  | negSucc position => simp [Tape.nth, Tape.mk₁, Tape.mk₂, Tape.mk', ListBlank.nth_mk]

/-- Prepare the exact initial window; there is no framing precondition. -/
noncomputable def directInitial (entry : State) (letters : Letter → Symbol)
    (time : MvPolynomial Unit ℕ) : Computation Unit Unit :=
  unaryMap (letterDomain.arrayOfLength wordLength) (cellDomain.arrayOfLength (directLength time))
    (fun _ _ => True) (fun sizes word index =>
      windowArray (MvPolynomial.eval sizes (directRadius time))
        (cells 0 ⟨entry, Tape.mk₁ ((List.ofFn word.val).map letters)⟩)
        (index.cast (directLength_eval time sizes)))

theorem directInitial_realizable (entry : State) (letters : Letter → Symbol)
    (time : MvPolynomial Unit ℕ) : (directInitial entry letters time).Realizable := by
  let domain := cellDomain (Symbol := Symbol) (State := State) (Parameter := Unit)
  let inputs := (directInitial entry letters time).inputDomains
  let allowed := fun (sizes : Unit → ℕ) (_ : ∀ name, (inputs name).Carrier sizes) => True
  have constant := (constant_realizable (fixed (Fintype.equivFin (Cell Symbol State)))
    (fun _ => (default, none))).withConstantSizes (Parameter := Unit)
  have blank (count : MvPolynomial Unit ℕ) :=
    (arrayTabulate_realizable inputs domain count (fun _ _ _ => (default, none))
      (constant.onArguments _ (fun _ _ => True) Empty.elim
        (by intro empty; cases empty) (by intros; trivial)))
  have scalar := (finiteOperation_realizable (fun _ : Unit => fixed (Fintype.equivFin Letter))
    (fixed (Fintype.equivFin (Cell Symbol State))) (fun values => (letters (values ()), none))).withConstantSizes
    (Parameter := Unit)
  have mapped := mapArray_realizable letterDomain domain wordLength (fun _ value => (letters value, none)) scalar
  have suffix := mapped.prodMk (blank (2 * time + 1))
  have tail := suffix.followedBy (arrayAppend_realizable domain wordLength (2 * time + 1)) rfl (by intros; trivial)
  have pair := (blank (directRadius time)).prodMk tail
  have concatenated := pair.followedBy (arrayAppend_realizable domain (directRadius time)
    (wordLength + (2 * time + 1))) rfl (by intros; trivial)
  let values sizes (arguments : {arguments : ∀ name, (inputs name).Carrier sizes // True}) :=
    (arrayAppend domain (directRadius time) (wordLength + (2 * time + 1))).compute sizes
      ⟨(fun _ => ((fun _ => (default, none)),
        (arrayAppend domain wordLength (2 * time + 1)).compute sizes
          ⟨(fun _ => ((fun index => (letters (arguments.val () index), none)),
            (fun _ => (default, none)))), trivial⟩)), trivial⟩
  have padded : (Computation.mk inputs (domain.arrayOfLength (directLength time)) allowed values).Realizable :=
    concatenated.withSpecification allowed values (by intros; trivial) (by intros; rfl)
  let coordinate (sizes : Unit → ℕ) : (arrayPosition (directLength time)).Carrier sizes :=
    ⟨MvPolynomial.eval sizes (directRadius time), by change MvPolynomial.eval sizes (directRadius time) < MvPolynomial.eval sizes (directLength time); rw [directLength_eval]; omega⟩
  have address := (positionPolynomial_realizable (directRadius time) (directLength time)).onResults
    inputs allowed (fun empty => nomatch empty) (by intro sizes arguments; change MvPolynomial.eval sizes (directRadius time) < MvPolynomial.eval sizes (directLength time); rw [directLength_eval]; omega)
    (fun empty => nomatch empty)
  have head := (arrayLookupWithIndex_realizable domain (arrayPosition (directLength time))
    (fun _ index => index.val) (arrayPosition_value _) _).onResults inputs allowed
    (fun choice sizes arguments => match choice with
      | false => coordinate sizes
      | true => values sizes arguments)
    (by intro sizes arguments; exact (coordinate sizes).isLt)
    (by intro choice; cases choice; exact address; exact padded)
  have mark := ((finiteOperation_realizable (fun _ : Unit => fixed (Fintype.equivFin (Cell Symbol State)))
    (fixed (Fintype.equivFin (Cell Symbol State))) (fun values => ((values ()).1, some entry))).withConstantSizes
      (Parameter := Unit))
  have marked := head.followedBy mark rfl (by intros; trivial)
  have complete := (arrayUpdateWithIndex_realizable domain (arrayPosition (directLength time))
    (fun _ index => index.val) (arrayPosition_value _) _).onResults inputs allowed
    (fun choice sizes arguments => match choice with
      | 0 => coordinate sizes
      | 1 => values sizes arguments
      | 2 => ((values sizes arguments (coordinate sizes)).1, some entry))
    (by intro sizes arguments; exact (coordinate sizes).isLt)
    (by intro choice; fin_cases choice
        exact address
        exact padded
        exact marked)
  apply complete.withSpecification (fun _ _ => True) (directInitial entry letters time).compute (by intros; trivial)
  intro sizes arguments valid
  have nth (position : ℕ) : ((List.ofFn (arguments ())).map letters).getI position =
      if inside : position < MvPolynomial.eval sizes wordLength then
        letters (arguments () ⟨position, inside⟩) else default := by
    split_ifs with inside
    · rw [List.getI_eq_getElem ((List.ofFn (arguments ())).map letters)
        (by simpa only [List.length_map, List.length_ofFn] using inside)]
      simp only [List.getElem_map, List.getElem_ofFn]
    · exact List.getI_eq_default _ (by simpa using Nat.le_of_not_gt inside)
  funext index
  simp only [onResults, arrayUpdateWithIndex]
  simp only [directInitial, unaryMap, windowArray, cells, windowPosition, Fin.val_cast, sub_zero]
  simp only [initial_nth, nth]
  simp [values, arrayAppend, encodingMap, unaryMap, Fin.append, Fin.addCases, coordinate,
    Function.update_apply, Fin.ext_iff]
  split_ifs <;> try omega
  all_goals first
    | rfl
    | omega
    | (apply Prod.ext <;> first
        | rfl
        | (apply congrArg letters; apply congrArg (arguments ()); apply Fin.ext; simp [directRadius]; omega))

end Polytime2.Complexity
