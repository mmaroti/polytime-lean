import Polytime2.TM0.LocalComputation
import Polytime2.Arrays.AllTrue

/-! # Observing the accepting symbol in a finite marked tape -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]
variable {Symbol State : Type} [Fintype Symbol] [Fintype State]

/-- Accept precisely when a marked cell contains the specified symbol. -/
noncomputable def localTapeAccept (accepting : Symbol) (length : MvPolynomial Parameter ℕ) :
    Computation Parameter Unit := by
  classical
  exact unaryMap ((cellDomain (Symbol := Symbol) (State := State)).arrayOfLength length) booleans
    (fun _ _ => True) (fun _ values => decide (∃ index state, values.val index = (accepting, some state)))

theorem localTapeAccept_realizable (accepting : Symbol) (length : MvPolynomial Parameter ℕ) :
    (localTapeAccept (State := State) accepting length).Realizable := by
  classical
  let reject := fun cell : Cell Symbol State => decide (∀ state, cell ≠ (accepting, some state))
  have scalar := finitePredicate_realizable (Parameter := Parameter)
    (fixed (Fintype.equivFin (Cell Symbol State))) reject
  have mapped := mapArray_realizable cellDomain booleans length (fun _ => reject) scalar
  have allRejected := mapped.followedBy (arrayAllTrue_realizable length) rfl (by intros; trivial)
  have complete := allRejected.followedBy (booleanOperation_realizable (fun values : Unit → Bool => !values ()))
    rfl (by intros; trivial)
  apply complete.withSpecification (fun _ _ => True) (localTapeAccept (State := State) accepting length).compute
    (by intros; trivial)
  intro sizes arguments valid
  change Unit → (Fin (MvPolynomial.eval sizes length) → Cell Symbol State) at arguments
  apply Bool.eq_iff_iff.mpr
  simp [followedBy, mapArray, arrayAllTrue, booleanOperation, unaryMap, localTapeAccept, reject,
    List.all_eq_false, List.mem_ofFn]
  exact exists_congr (fun _ => decide_eq_false_iff_not.trans (by simp only [not_forall, not_not]))

end Polytime2.Computation
