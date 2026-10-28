import Polytime2.Complexity.Realizable
import Polytime2.TM0.WordBits
import Mathlib.Data.Fin.VecNotation

/-! # Total word execution of certified Boolean-array computations

The external alphabet has five letters. Three Boolean tracks hold a fixed
injective code for those letters; a fourth track is the unary word length.
Raw input preparation, simulation, extraction, and cleanup are all included in
the polynomial bound. There is no framing precondition on raw input words.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity

/-- A fixed three-bit code for the five external letters. -/
def letterBits : Letter → Fin 3 → Bool
  | .inl false => ![false, false, false]
  | .inl true => ![true, false, false]
  | .inr index => match index.val with
    | 0 => ![false, true, false]
    | 1 => ![true, true, false]
    | _ => ![false, false, true]

theorem letterBits_injective : Function.Injective letterBits := by decide

/-- Format a bit stream with fixed controller memory, emitting one letter per bit. -/
def formatBits {Memory : Type} (format : Memory → Bool → Memory × Letter) : Memory → List Bool → Word
  | _, [] => []
  | memory, bit :: bits => (format memory bit).2 :: formatBits format (format memory bit).1 bits

@[simp] theorem formatBits_length {Memory : Type} (format : Memory → Bool → Memory × Letter)
    (memory : Memory) (bits : List Bool) : (formatBits format memory bits).length = bits.length := by
  induction bits generalizing memory with
  | nil => rfl
  | cons bit bits hypothesis => simp [formatBits, hypothesis]

@[simp] theorem formatBits_binary (bits : List Bool) :
    formatBits (fun _ : Unit => fun bit => ((), Sum.inl bit)) () bits = bits.map Sum.inl := by
  induction bits with
  | nil => rfl
  | cons bit bits hypothesis => simp [formatBits, hypothesis]

namespace Internal

open Turing

noncomputable def rawLetters {Scratch : Type} :
    Letter ↪ Sweep.Alphabet (Tracks.Row (CallingConvention.Alphabet (WordBits.TapeName Scratch))) := by
  refine ⟨fun letter => Sweep.row (WordBits.row (letterBits letter)), ?_⟩
  intro first second equal
  apply letterBits_injective
  funext index
  have bit := congrArg (fun symbol => match symbol with
    | some (.inr row) => row.1 (.inr (.inl index))
    | _ => (0 : Binary.Symbol)) equal
  change Binary.data (letterBits first index) = Binary.data (letterBits second index) at bit
  cases firstBit : letterBits first index <;> cases secondBit : letterBits second index <;>
    simp_all [Binary.data]

private theorem formatBits_rows {Scratch Memory : Type}
    (format : Memory → Bool → Memory × Letter) (memory : Memory) (bits : List Bool) :
    TrackOutput.Stateful.word
      (fun state bit => ((format state bit).1, WordBits.row (Scratch := Scratch) (letterBits (format state bit).2)))
      memory bits = (formatBits format memory bits).map rawLetters := by
  induction bits generalizing memory with
  | nil => rfl
  | cons bit bits hypothesis => simp [TrackOutput.Stateful.word, formatBits, rawLetters, hypothesis]

end Internal

end Polytime2.Complexity

namespace Polytime2.Computation.Realizable

open MultiTape CallingConvention EncodedDomain Complexity

/-- Execute on arbitrary raw words and format the canonical output bits with
fixed finite controller memory. Output sizes depend on the raw input length. -/
theorem onRawWordFormattedOutput {Memory : Type} [Fintype Memory] (outputDomain : EncodedDomain Unit)
    (operation : (size : ℕ) → (Fin 3 → Fin size → Bool) → outputDomain.Carrier (fun _ => size))
    (format : Memory → Bool → Memory × Letter) (initialMemory : Memory)
    (ready : (Computation.mk (fun _ : Fin 3 => (booleans : EncodedDomain Unit).array ())
      outputDomain (fun _ _ => True) (fun sizes arguments => operation (sizes ()) arguments.val)).Realizable) :
    PolynomialTime id id (fun word =>
      formatBits format initialMemory (ArrayEncoding.bits (outputDomain.encode (fun _ => word.length)
        (operation word.length (WordBits.arguments letterBits word))))) := by
  classical
  let _ : Inhabited Memory := ⟨initialMemory⟩
  let computation : Computation Unit (Fin 3) :=
    ⟨(fun _ => booleans.array ()), outputDomain, (fun _ _ => True),
      (fun sizes arguments => operation (sizes ()) arguments.val)⟩
  obtain ⟨Scratch, finiteScratch, scratchDomains, State, finiteStates,
    source, sourceEntry, sourceExit, certificate⟩ := ready
  let _ : Fintype Scratch := finiteScratch
  let _ : Fintype State := finiteStates
  let SourceTape := Internal.TapeName computation Scratch
  let domains := Internal.domains computation scratchDomains
  let readOnly : SourceTape → Bool := Internal.readOnly computation
  let sizeTapes := Internal.sizeTapes computation Scratch
  let resultTape : SourceTape := Internal.outputTape computation
  let precondition (sizes : Unit → ℕ) (initial : Tapes (Alphabet SourceTape)) : Prop :=
    ∃ input : Inputs domains readOnly sizes, Entry domains readOnly sizes input initial ∧
      ∀ parameter, initial (sizeTapes parameter) = unary (sizes parameter)
  let postcondition (sizes : Unit → ℕ) (initial final : Tapes (Alphabet SourceTape)) : Prop :=
    ∃ (input : Inputs domains readOnly sizes) (output : Outputs domains
      (Internal.outputTapes computation Scratch) sizes), Entry domains readOnly sizes input initial ∧
      Internal.resultCorrect computation scratchDomains sizes input output ∧
      Exit domains (Internal.outputTapes computation Scratch) sizes output final
  have physical : MultiTape.Internal.Realizes source sourceEntry sourceExit precondition postcondition := by
    obtain ⟨_, _, halted, bound, execute⟩ := certificate
    refine ⟨halted, bound, ?_⟩
    intro sizes initial valid
    obtain ⟨input, represented, headers⟩ := valid
    obtain ⟨ticks, output, final, cost, trace, correct, returned⟩ :=
      execute sizes input initial trivial represented headers
    exact ⟨ticks, final, cost, trace.steps, input, output, represented, correct, returned⟩
  let names := (Finset.univ : Finset SourceTape).toList
  obtain ⟨simulationBound, rowBound, simulate⟩ := Simulation.realizes_steps names
    (Finset.nodup_toList _) (by intro name; simp [names]) physical (MvPolynomial.X () + 1)
  let outputRow := fun memory bit => ((format memory bit).1,
    WordBits.row (Scratch := Scratch) (letterBits (format memory bit).2))
  have formattedBits (memory : Memory) (bits : List Bool) :
      TrackOutput.Stateful.word outputRow memory bits =
        (formatBits format memory bits).map (Complexity.Internal.rawLetters (Scratch := Scratch)) :=
    Complexity.Internal.formatBits_rows format memory bits
  let runOutput := MultiTape.sequence (Simulation.machine names source) (extractStatefulTo resultTape outputRow) (0, initialMemory)
  let program := MultiTape.sequence (RawInput.machine (WordBits.empty (Scratch := Scratch)) WordBits.mark)
    runOutput (.inl (Simulation.entry names sourceEntry))
  let timeBound : MvPolynomial Unit ℕ :=
    2 * (2 * (MvPolynomial.X () + 1) + 6 + simulationBound + 2 * rowBound + 10) + 1 + outputDomain.widthPolynomial
  refine ⟨Sweep.Alphabet (Tracks.Row (Alphabet SourceTape)), inferInstance, inferInstance,
    SingleTape.Controller _, inferInstance, inferInstance, Complexity.Internal.rawLetters,
    SingleTape.compile program, .inl (.inl (.inl 0)), Complexity.Internal.diagonal timeBound, ?_, ?_⟩
  · intro letter
    change some _ ≠ none
    simp
  · intro word
    let sizes : Unit → ℕ := fun _ => word.length
    let input : Inputs domains readOnly sizes := fun name => match name with
      | ⟨.inl (), _⟩ => PUnit.unit
      | ⟨.inr (.inl bit), _⟩ => WordBits.arguments letterBits word bit
      | ⟨.inr (.inr _), impossible⟩ => False.elim (Bool.noConfusion impossible)
    have entered : Entry domains readOnly sizes input (WordBits.tapes letterBits word) :=
      by
        convert WordBits.entry letterBits word scratchDomains outputDomain operation using 1
        funext name
        rcases name with ⟨name, immutable⟩
        rcases name with parameter | bit | output | scratch
        · cases parameter; rfl
        · rfl
        · cases immutable
        · cases immutable
    have headers : ∀ parameter, WordBits.tapes (Scratch := Scratch) letterBits word (sizeTapes parameter) =
        unary (sizes parameter) := by intro parameter; cases parameter; exact WordBits.size_tape letterBits word
    let rows := RawInput.rows (WordBits.empty (Scratch := Scratch)) WordBits.mark
      (word.map (fun letter => WordBits.row (letterBits letter)))
    have rowCost : rows.length ≤ word.length + 1 := by
      simpa [rows] using RawInput.rows_length (WordBits.empty (Scratch := Scratch)) WordBits.mark
        (word.map (fun letter => WordBits.row (letterBits letter)))
    obtain ⟨simulationTicks, finalRows, final, simulationCost, storage,
      ⟨otherInput, output, otherEntry, correct, returned⟩, represented, simulated⟩ :=
      simulate sizes (WordBits.tapes letterBits word) ⟨input, entered, headers⟩ rows
        (WordBits.represented letterBits word) (by simpa [sizes] using rowCost)
    have sameInput : otherInput = input := otherEntry.inputs_unique entered
    subst otherInput
    obtain ⟨valid, correctValue⟩ := correct
    change output () = operation word.length (WordBits.arguments letterBits word) at correctValue
    have outputRepresentation := represented resultTape
    have returnedValue : final resultTape = encoded outputDomain sizes (output ()) := returned ()
    rw [returnedValue, correctValue] at outputRepresentation
    obtain ⟨extractTicks, extractCost, extracted⟩ := extractStatefulTo_runs resultTape outputRow initialMemory
      outputDomain sizes
      (operation word.length (WordBits.arguments letterBits word)) finalRows outputRepresentation
    have runTrace := sequence_steps (Simulation.machine names source) (extractStatefulTo resultTape outputRow) (0, initialMemory)
      simulated (by intro symbols; rfl) extracted
    have prepared := RawInput.steps (WordBits.empty (Scratch := Scratch)) WordBits.mark
      (word.map (fun letter => WordBits.row (letterBits letter)))
    have complete := sequence_steps (RawInput.machine (WordBits.empty (Scratch := Scratch)) WordBits.mark)
      runOutput (.inl (Simulation.entry names sourceEntry)) prepared (by intro symbols; rfl) runTrace
    let finalMemory := TrackOutput.Stateful.finalMemory outputRow initialMemory
      (ArrayEncoding.bits (outputDomain.encode sizes (operation word.length (WordBits.arguments letterBits word))))
    constructor
    · refine ⟨2 * (2 * rows.length + 6 + (simulationTicks + extractTicks + 1) + 1),
        .inl (.inr (.inr (7, finalMemory))), ?_, ?_, ?_⟩
      · rw [Complexity.Internal.diagonal_eval]
        change _ ≤ MvPolynomial.eval sizes timeBound
        simp only [timeBound, map_add, map_mul, map_ofNat, map_one, MvPolynomial.eval_X]
        dsimp [sizes] at *
        omega
      · have translated := SingleTape.steps program complete
        simp only [formattedBits] at translated
        convert translated using 1 <;>
          simp [SingleTape.configuration, Sweep.tape, Turing.Tape.mk₁, Turing.Tape.mk₂,
          Complexity.Internal.rawLetters, finalMemory, ArrayEncoding.bits,
          rows, List.map_map, Function.comp_def] <;> rfl
      · have halted := SingleTape.halt program
          (.inr (.inr (7, finalMemory)), Sweep.tape [] (TrackOutput.Stateful.word outputRow initialMemory
            (ArrayEncoding.bits (outputDomain.encode sizes
              (operation word.length (WordBits.arguments letterBits word)))))) (by rfl)
        simp only [formattedBits] at halted
        convert halted using 1
        simp [SingleTape.configuration, Sweep.tape, Turing.Tape.mk₁, Turing.Tape.mk₂,
            Complexity.Internal.rawLetters, ArrayEncoding.bits]
        rfl
    · rw [Complexity.Internal.diagonal_eval]
      simp [ArrayEncoding.bits, timeBound]

/-- The ordinary binary exporter specializes the finite-memory formatter. -/
theorem onRawWordOutput (outputDomain : EncodedDomain Unit)
    (operation : (size : ℕ) → (Fin 3 → Fin size → Bool) → outputDomain.Carrier (fun _ => size))
    (ready : (Computation.mk (fun _ : Fin 3 => (booleans : EncodedDomain Unit).array ())
      outputDomain (fun _ _ => True) (fun sizes arguments => operation (sizes ()) arguments.val)).Realizable) :
    PolynomialTime id id (fun word =>
      (ArrayEncoding.bits (outputDomain.encode (fun _ => word.length)
        (operation word.length (WordBits.arguments letterBits word)))).map Sum.inl) := by
  have formatted := onRawWordFormattedOutput outputDomain operation
    (fun _ : Unit => fun bit => ((), Sum.inl bit)) () ready
  simpa only [formatBits_binary] using formatted

/-- A total decision on three Boolean arrays runs on arbitrary raw words.
The mathematical operation receives the word length and the three bit arrays.
No machine, tape layout, or scratch choice is exposed to application proofs. -/
theorem onRawWords
    (operation : (size : ℕ) → (Fin 3 → Fin size → Bool) → Bool)
    (ready : (Computation.mk (fun _ : Fin 3 => (booleans : EncodedDomain Unit).array ())
      booleans (fun _ _ => True) (fun sizes arguments => operation (sizes ()) arguments.val)).Realizable) :
    PolynomialTime id encodeBool
      (fun word => operation word.length (WordBits.arguments letterBits word)) := by
  have raw := onRawWordOutput booleans operation ready
  simpa only [WordBits.boolean_bits, List.map_singleton, PolynomialTime, encodeBool, id_eq] using raw

end Polytime2.Computation.Realizable
