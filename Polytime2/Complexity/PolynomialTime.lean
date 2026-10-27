import Polytime2.TM0.WordComposition
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! # Polynomial-time word computations

Words use the fixed five-letter alphabet `Bool ⊕ Fin 3`, shared with public
Polytime2 serialization. Their size is list length, counting every header,
separator, and payload symbol. A computation certificate supplies a finite
Mathlib TM0 machine, a nonblank embedding of these letters, and one natural
coefficient polynomial bounding both transitions and output length. All work
symbols and states are fixed independently of the input.

The encodings may describe mathematical carriers. Specializing both encodings
to `id` gives total word functions, including all malformed encodings. A
certificate on a subtype of valid inputs alone does not certify a total word
function. The explicit output bound makes composition independent of a tape
support lemma and is also available from Polytime2's exact output widths.
-/

namespace Polytime2.Complexity

open Turing

abbrev Letter := Bool ⊕ Fin 3
abbrev Word := List Letter

namespace Internal

/-- Exact canonical output on an otherwise blank tape, at a halting state. -/
def Runs {Symbol State : Type} [Inhabited Symbol] [Inhabited State]
    (machine : TM0.Machine Symbol State) (entry : State) (letters : Letter → Symbol)
    (input output : Word) (allowance : ℕ) : Prop :=
  ∃ ticks finalState, ticks ≤ allowance ∧
    (fun current => current.bind (TM0.step machine))^[ticks]
      (some ⟨entry, Tape.mk₁ (input.map letters)⟩) =
        some ⟨finalState, Tape.mk₁ (output.map letters)⟩ ∧
    TM0.step machine ⟨finalState, Tape.mk₁ (output.map letters)⟩ = none

noncomputable def cross {Source Target : Type} [Inhabited Source] [Inhabited Target]
    (letters : Letter ↪ Source) (target : Letter → Target)
    (nonblank : ∀ letter, letters letter ≠ default) : PointedMap Source Target := by
  classical
  refine ⟨fun symbol => if present : ∃ letter, letters letter = symbol then target present.choose else default, ?_⟩
  simp only [dite_eq_right (show ¬ ∃ letter, letters letter = default from by
    rintro ⟨letter, equal⟩; exact nonblank letter equal)]

theorem cross_letter {Source Target : Type} [Inhabited Source] [Inhabited Target]
    (letters : Letter ↪ Source) (target : Letter → Target)
    (nonblank : ∀ letter, letters letter ≠ default) (letter : Letter) :
    cross letters target nonblank (letters letter) = target letter := by
  classical
  simp only [cross, dite_eq_left (show ∃ other, letters other = letters letter from ⟨letter, rfl⟩)]
  congr 1
  exact letters.injective (Exists.choose_spec (show ∃ other, letters other = letters letter from ⟨letter, rfl⟩))

theorem runs_map {Symbol TargetSymbol State : Type}
    [Inhabited Symbol] [Inhabited TargetSymbol] [Inhabited State]
    (machine : TM0.Machine Symbol State) (entry : State) (letters : Letter → Symbol) (targetLetters : Letter → TargetSymbol)
    (forward : PointedMap Symbol TargetSymbol) (backward : TargetSymbol → Symbol)
    (inverse : Function.LeftInverse backward forward)
    (letter_map : ∀ letter, forward (letters letter) = targetLetters letter)
    {input output : Word} {allowance : ℕ} (runs : Runs machine entry letters input output allowance) :
    Runs (TM0Word.mapMachine machine forward backward) entry targetLetters input output allowance := by
  obtain ⟨ticks, finalState, bounded, trace, halt⟩ := runs
  refine ⟨ticks, finalState, bounded, ?_, ?_⟩
  · have lifted := TM0Word.map_trace machine forward backward inverse trace
    simpa [TM0Word.mapConfiguration, TM0.init, Tape.map_mk₁, List.map_map,
      Function.comp_def, letter_map] using lifted
  · have lifted := TM0Word.map_step machine forward backward inverse
      ⟨finalState, Tape.mk₁ (output.map letters)⟩
    rw [halt] at lifted
    simpa [TM0Word.mapConfiguration, Tape.map_mk₁, List.map_map,
      Function.comp_def, letter_map] using lifted

theorem eval_mono (polynomial : Polynomial ℕ) {first second : ℕ} (bounded : first ≤ second) :
    polynomial.eval first ≤ polynomial.eval second := by
  induction polynomial using Polynomial.induction_on' with
  | add left right leftBound rightBound => simpa using Nat.add_le_add leftBound rightBound
  | monomial degree coefficient =>
    simp only [Polynomial.eval_monomial]
    gcongr

end Internal

/-- Polynomial-time computation between specified word encodings. One finite
machine and one polynomial bound time and output length for every source value.
For total word functions use `PolynomialTime id id function`. -/
def PolynomialTime {Source : Type*} {Target : Type*}
    (encodeSource : Source → Word) (encodeTarget : Target → Word) (function : Source → Target) : Prop :=
  ∃ (Symbol : Type) (_finiteSymbols : Fintype Symbol) (inhabitedSymbols : Inhabited Symbol),
    let _symbolInhabited : Inhabited Symbol := inhabitedSymbols
    ∃ (State : Type) (_finiteStates : Fintype State) (inhabitedStates : Inhabited State),
      let _stateInhabited : Inhabited State := inhabitedStates
      ∃ (letters : Letter ↪ Symbol) (machine : TM0.Machine Symbol State) (entry : State) (bound : Polynomial ℕ),
        (∀ letter, letters letter ≠ default) ∧
        ∀ value, Internal.Runs machine entry letters (encodeSource value) (encodeTarget (function value))
          (bound.eval (encodeSource value).length) ∧
          (encodeTarget (function value)).length ≤ bound.eval (encodeSource value).length

/-- The identity needs no transitions; its output is its input. -/
theorem PolynomialTime.id {Source : Type*} (encode : Source → Word) : PolynomialTime encode encode id := by
  refine ⟨Option Letter, inferInstance, inferInstance, Unit, inferInstance, inferInstance,
    ⟨some, Option.some_injective _⟩, (fun _ _ => none), (), Polynomial.X, ?_, ?_⟩
  · intro letter; simp
  · intro value
    exact ⟨⟨0, (), by simp, rfl, rfl⟩, by simp⟩

/-- Composition uses the existing exact TM0 transport and handover rules.
The product alphabet identifies the common external letters without changing
either machine's work symbols or transition count. -/
theorem PolynomialTime.comp {Source Middle Target : Type*}
    {encodeSource : Source → Word} {encodeMiddle : Middle → Word} {encodeTarget : Target → Word}
    {first : Source → Middle} {second : Middle → Target}
    (secondReady : PolynomialTime encodeMiddle encodeTarget second)
    (firstReady : PolynomialTime encodeSource encodeMiddle first) :
    PolynomialTime encodeSource encodeTarget (second ∘ first) := by
  classical
  obtain ⟨FirstSymbol, firstFinite, firstInhabited, FirstState, firstStates, firstStateInhabited,
    firstLetters, firstMachine, firstEntry, firstBound, firstNonblank, firstRuns⟩ := firstReady
  obtain ⟨SecondSymbol, secondFinite, secondInhabited, SecondState, secondStates, secondStateInhabited,
    secondLetters, secondMachine, secondEntry, secondBound, secondNonblank, secondRuns⟩ := secondReady
  let _ : Fintype FirstSymbol := firstFinite
  let _ : Inhabited FirstSymbol := firstInhabited
  let _ : Fintype FirstState := firstStates
  let _ : Inhabited FirstState := firstStateInhabited
  let _ : Fintype SecondSymbol := secondFinite
  let _ : Inhabited SecondSymbol := secondInhabited
  let _ : Fintype SecondState := secondStates
  let _ : Inhabited SecondState := secondStateInhabited
  let jointInhabited : Inhabited (FirstSymbol × SecondSymbol) := ⟨(default, default)⟩
  let _ : Inhabited (FirstSymbol × SecondSymbol) := jointInhabited
  let forwardFirst : PointedMap FirstSymbol (FirstSymbol × SecondSymbol) :=
    ⟨fun symbol => (symbol, Internal.cross firstLetters secondLetters firstNonblank symbol), by simp; rfl⟩
  let forwardSecond : PointedMap SecondSymbol (FirstSymbol × SecondSymbol) :=
    ⟨fun symbol => (Internal.cross secondLetters firstLetters secondNonblank symbol, symbol), by simp; rfl⟩
  let letters : Letter ↪ FirstSymbol × SecondSymbol :=
    ⟨fun letter => (firstLetters letter, secondLetters letter), fun _ _ equal =>
      firstLetters.injective (congrArg Prod.fst equal)⟩
  let firstLift := TM0Word.mapMachine firstMachine forwardFirst Prod.fst
  let secondLift := TM0Word.mapMachine secondMachine forwardSecond Prod.snd
  refine ⟨FirstSymbol × SecondSymbol, inferInstance, jointInhabited,
    Sum FirstState SecondState, inferInstance, inferInstance, letters,
    TM0Word.sequence firstLift secondLift secondEntry, .inl firstEntry, firstBound + secondBound.comp firstBound + 1, ?_, ?_⟩
  · intro letter equal
    exact firstNonblank letter (congrArg Prod.fst equal)
  · intro value
    obtain ⟨firstRun, middleLength⟩ := firstRuns value
    obtain ⟨secondRun, outputLength⟩ := secondRuns (first value)
    have firstMapped := Internal.runs_map firstMachine firstEntry firstLetters letters forwardFirst Prod.fst
      (fun _ => rfl) (fun letter => by simp [forwardFirst, letters, Internal.cross_letter]; rfl) firstRun
    have secondMapped := Internal.runs_map secondMachine secondEntry secondLetters letters forwardSecond Prod.snd
      (fun _ => rfl) (fun letter => by simp [forwardSecond, letters, Internal.cross_letter]; rfl) secondRun
    obtain ⟨firstTicks, firstExit, firstCost, firstTrace, firstHalt⟩ := firstMapped
    obtain ⟨secondTicks, secondExit, secondCost, secondTrace, secondHalt⟩ := secondMapped
    have cost := Internal.eval_mono secondBound middleLength
    constructor
    · refine ⟨firstTicks + 1 + secondTicks, .inr secondExit, ?_, ?_, ?_⟩
      · simp only [Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_one]
        omega
      · simpa only [TM0.step, TM0Word.sequence, Function.comp_apply] using
          TM0Word.sequence_trace firstLift secondLift firstTrace firstHalt secondTrace
      · simpa [TM0.step, TM0Word.sequence] using congrArg (Option.map
          (fun c : TM0.Cfg (FirstSymbol × SecondSymbol) SecondState =>
            (⟨Sum.inr c.q, c.Tape⟩ : TM0.Cfg (FirstSymbol × SecondSymbol) (Sum FirstState SecondState)))) secondHalt
    · simp only [Function.comp_apply, Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_one]
      omega

end Polytime2.Complexity
