import Polytime2.Complexity.DirectInitial
import Polytime2.Complexity.MachineTrace
import Polytime2.TM0.LocalObservation
import Polytime2.Computation.Traversal
import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Direct import of polynomial-time Boolean word algorithms

The public input is the canonical ordinary letter array on every word. Machine
alphabets, source states, finite windows, and time allowances remain private.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity

open Turing EncodedDomain Polytime2.Computation

private theorem machineVerifier_realizable {Symbol State : Type} [Inhabited Symbol] [Inhabited State]
    [Fintype Symbol] [Fintype State] (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (timeBound : Polynomial ℕ) (verify : Word → Bool)
    (runs : ∀ word, Internal.Runs machine entry letters word [Sum.inl (verify word)] (timeBound.eval word.length)) :
    (Computation.mk (fun _ : Unit => letterDomain.arrayOfLength (MvPolynomial.X ())) booleans (fun _ _ => True)
      (fun _ arguments => verify (List.ofFn (arguments.val ())))).Realizable := by
  classical
  let time := timeBound.toMvPolynomial ()
  let length := directLength time
  let update := fun sizes values => (localTapeStep machine length).compute sizes ⟨(fun _ => values), trivial⟩
  let domain := (cellDomain (Symbol := Symbol) (State := State)).arrayOfLength length
  let context : Empty → EncodedDomain Unit := Empty.elim
  have step := (localTapeStep_realizable machine length).onArguments
    (iterationStep context domain (fun _ _ _ => True) (fun sizes _ => update sizes)).inputDomains
    (fun _ _ => True) (fun _ => Sum.inr ()) (by intros; rfl) (by intros; trivial)
  have loop := boundedIteration_realizable context domain time (fun _ _ _ => True) (fun _ _ _ => True)
    (fun sizes _ => update sizes) step (fun _ _ _ _ _ => True)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
  have iterated := loop.onArguments (fun _ : Unit => domain) (fun _ _ => True)
    (fun | .inl empty => nomatch empty | .inr _ => ())
    (by rintro (empty | singleton); cases empty; rfl) (by intros; trivial)
  have evolved := (directInitial_realizable entry letters time).followedBy iterated rfl (by intros; trivial)
  have observed := evolved.followedBy (localTapeAccept_realizable (State := State) (letters (Sum.inl true)) length)
    rfl (by intros; trivial)
  apply observed.withSpecification (fun _ _ => True) _ (by intros; trivial)
  intro sizes arguments valid
  let radius := MvPolynomial.eval sizes (directRadius time)
  have equal : MvPolynomial.eval sizes length = 2 * radius + 1 := directLength_eval time sizes
  let initial := windowArray radius (cells 0 ⟨entry, Tape.mk₁ ((List.ofFn (arguments ())).map letters)⟩)
  let transport := fun (contents : Fin (2 * radius + 1) → Cell Symbol State)
    (index : Fin (MvPolynomial.eval sizes length)) => contents (index.cast equal)
  have conjugate : Function.Semiconj transport
      (cellTransition (windowNeighbors radius) (windowUpdate machine radius)) (update sizes) := by
    intro contents
    exact (localTapeStep_window machine length sizes radius equal contents).symm
  have trace := (conjugate.iterate_right (MvPolynomial.eval sizes time)) initial
  have executes : Internal.Runs machine entry letters (List.ofFn (arguments ()))
      [Sum.inl (verify (List.ofFn (arguments ())))] (MvPolynomial.eval sizes time) := by
    simpa [time, MvPolynomial.eval_toMvPolynomial] using runs (List.ofFn (arguments ()))
  have accepted := runs_window_accepting machine entry letters (List.ofFn (arguments ()))
    (verify (List.ofFn (arguments ()))) (MvPolynomial.eval sizes time) radius
    (by simp [radius]) executes
  apply Bool.eq_iff_iff.mpr
  change (decide (∃ index state, ((update sizes)^[MvPolynomial.eval sizes time]
    (transport initial)) index = (letters (Sum.inl true), some state)) = true) ↔ _
  rw [decide_eq_true_eq, ← trace]
  constructor
  · rintro ⟨index, state, hit⟩
    exact accepted.mp ⟨index.cast equal, state, hit⟩
  · intro answer
    obtain ⟨index, state, hit⟩ := accepted.mpr answer
    exact ⟨index.cast equal.symm, state, by simpa [transport, initial] using hit⟩

/-- Call any polynomial-time Boolean word algorithm as a total computation on
ordinary canonical letter arrays, including the empty word. -/
theorem wordVerifier_realizable (verify : Word → Bool) (ready : PolynomialTime id encodeBool verify) :
    (Computation.mk (fun _ : Unit => letterDomain.array ()) booleans (fun _ _ => True)
      (fun _ arguments => verify (List.ofFn (arguments.val ())))).Realizable := by
  obtain ⟨Symbol, finiteSymbols, inhabitedSymbols, State, finiteStates, inhabitedStates,
    letters, machine, entry, timeBound, _nonblank, executes⟩ := ready
  let _ : Fintype Symbol := finiteSymbols
  let _ : Inhabited Symbol := inhabitedSymbols
  let _ : Fintype State := finiteStates
  let _ : Inhabited State := inhabitedStates
  have source := (machineVerifier_realizable machine entry letters timeBound verify
    (fun word => by simpa only [id_eq, encodeBool] using (executes word).1)).reinterpretInputs
      (fun _ : Unit => letterDomain.array ()) (fun _ sizes => arrayParameterEquiv letterDomain () sizes)
      (by intros; rfl) (fun _ sizes value => array_X_encode_bits letterDomain () sizes value)
      (fun _ _ => True) (by intros; trivial)
  apply source.withSpecification (fun _ _ => True) _ (by intros; trivial)
  intro sizes arguments valid
  exact congrArg verify (List.ofFn_congr (MvPolynomial.eval_X (f := sizes) ()).symm (arguments ())).symm

end Polytime2.Complexity
