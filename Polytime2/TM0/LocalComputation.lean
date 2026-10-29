import Polytime2.TM0.FiniteWindow
import Polytime2.Arrays.Shift
import Polytime2.Arrays.ZipWith
import Polytime2.Primitives.ConstantOperations

/-! # Direct certified local tape evolution

Three aligned arrays contain the left, current, and right cell. A fixed finite
table implements the mathematical local transition, without Boolean circuits.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]
variable {Symbol State : Type} [Inhabited Symbol] [Inhabited State]
  [Fintype Symbol] [Fintype State]

noncomputable abbrev cellDomain : EncodedDomain Parameter :=
  (fixed (Parameter := Empty) (Fintype.equivFin (Cell Symbol State))).constant

/-- Apply one local source-machine transition to a finite array of marked cells.
Missing neighbors are blank and unmarked. -/
noncomputable def localTapeStep (machine : Turing.TM0.Machine Symbol State)
    (length : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  unaryMap (cellDomain.arrayOfLength length) (cellDomain.arrayOfLength length) (fun _ _ => True)
    (fun sizes values index => localStep machine
      ((arrayShift cellDomain length .left).compute sizes
        ⟨(fun | false => values.val | true => (default, none)), trivial⟩ index)
      (values.val index)
      ((arrayShift cellDomain length .right).compute sizes
        ⟨(fun | false => values.val | true => (default, none)), trivial⟩ index))

theorem localTapeStep_realizable (machine : Turing.TM0.Machine Symbol State)
    (length : MvPolynomial Parameter ℕ) : (localTapeStep machine length).Realizable := by
  let inputs := (localTapeStep machine length).inputDomains
  let allowed := fun (sizes : Parameter → ℕ) (_ : ∀ name, (inputs name).Carrier sizes) => True
  have blank := ((constant_realizable (fixed (Fintype.equivFin (Cell Symbol State)))
    (fun _ => (default, none))).withConstantSizes (Parameter := Parameter)).onResults inputs allowed
    (fun empty => nomatch empty) (by intros; trivial) (fun empty => nomatch empty)
  have shifted (direction : Turing.Dir) := (arrayShift_realizable
    (cellDomain (Symbol := Symbol) (State := State)) length direction).onResults inputs allowed
    (fun choice _ arguments => match choice with | false => arguments.val () | true => (default, none))
    (by intros; trivial) (by
      intro choice; cases choice
      · exact Realizable.argument inputs () allowed
      · exact blank)
  let operation := fun (sizes : Parameter → ℕ) (_ : ∀ name : Empty, (Empty.elim name : EncodedDomain Parameter).Carrier sizes) (entries : Fin 3 → Cell Symbol State) =>
    localStep machine (entries 0) (entries 1) (entries 2)
  have scalar := ((finiteTernary_realizable (fixed (Fintype.equivFin (Cell Symbol State)))
    (localStep machine)).withConstantSizes (Parameter := Parameter)).onArguments
      (Sum.elim (Empty.elim : Empty → EncodedDomain Parameter) (fun _ : Fin 3 => cellDomain))
      (fun _ _ => True) Sum.inr (by intros; rfl) (by intros; trivial)
  have zipped := arrayZip_realizable (Empty.elim : Empty → EncodedDomain Parameter)
    (fun _ : Fin 3 => cellDomain) cellDomain length operation scalar
  exact zipped.onResults inputs allowed
    (fun name sizes arguments => match name with
      | .inl empty => nomatch empty
      | .inr 0 => (arrayShift cellDomain length .left).compute sizes
          ⟨(fun | false => arguments.val () | true => (default, none)), trivial⟩
      | .inr 1 => arguments.val ()
      | .inr 2 => (arrayShift cellDomain length .right).compute sizes
          ⟨(fun | false => arguments.val () | true => (default, none)), trivial⟩)
    (by intros; trivial) (by
      rintro (empty | name)
      · cases empty
      · fin_cases name
        · exact shifted .left
        · exact Realizable.argument inputs () allowed
        · exact shifted .right)

/-- The certified array update is the existing finite-window dynamics. -/
theorem localTapeStep_window (machine : Turing.TM0.Machine Symbol State)
    (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ) (radius : ℕ)
    (equal : MvPolynomial.eval sizes length = 2 * radius + 1)
    (contents : Fin (2 * radius + 1) → Cell Symbol State) :
    (localTapeStep machine length).compute sizes
      ⟨(fun _ index => contents (index.cast equal)), trivial⟩ =
      fun index => cellTransition (windowNeighbors radius) (windowUpdate machine radius)
        contents (index.cast equal) := by
  funext index
  have bounded := index.isLt
  simp only [localTapeStep, unaryMap, arrayShift, cellTransition, windowUpdate, windowNeighbors, Fin.val_cast]
  congr 1
  by_cases last : index.val = 2 * radius
  · simp [last, equal]
  · have inside : index.val + 1 < MvPolynomial.eval sizes length := by omega
    simp [last, inside, Nat.min_eq_left (show index.val + 1 ≤ 2 * radius by omega)]

end Polytime2.Computation
