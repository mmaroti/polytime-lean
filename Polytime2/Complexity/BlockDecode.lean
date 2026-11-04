import Polytime2.Complexity.Realizable
import Polytime2.TM0.NativeTrackOutput
import Polytime2.TM0.RawInput
import Polytime2.TM0.Simulation

/-! # Standalone decoding of fixed-width native-symbol streams

A fixed finite block code and a rejecting sentinel describe the input protocol.
The decoder emits the exact native word and ignores the capacity padding after
the sentinel. Raw preparation, simulation, extraction, and startup are charged.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity.BlockDecode

open MultiTape

private abbrev DecoderAlphabet := BlockDecoder.Alphabet (Letter := Letter)
private abbrev Row := Tracks.Row DecoderAlphabet

private def nativeRow (letter : Letter) : Row :=
  ((fun name => match name with
    | false => match letter with | .inl bit => Binary.data bit | .inr _ => (0 : Binary.Symbol)
    | true => match letter with | .inl _ => none | .inr index => some (.inr index)), fun _ => false)

private theorem nativeRow_injective : Function.Injective nativeRow := by
  intro first second equal
  cases first with
  | inl first =>
    cases second with
    | inl second =>
      have bits := congrArg (fun row => row.1 false) equal
      change Binary.data first = Binary.data second at bits
      apply congrArg Sum.inl
      cases first <;> cases second <;> simp_all [Binary.data]
    | inr second =>
      have bits := congrArg (fun row => row.1 false) equal
      cases first <;> have impossible := congrArg Fin.val bits <;> simp [nativeRow, Binary.data] at impossible
  | inr first =>
    cases second with
    | inl second =>
      have bits := congrArg (fun row => row.1 false) equal
      cases second <;> have impossible := congrArg Fin.val bits <;> simp [nativeRow, Binary.data] at impossible
    | inr second =>
      have symbols := congrArg (fun row => row.1 true) equal
      change some (.inr first : Letter) = some (.inr second : Letter) at symbols
      exact Option.some.inj symbols

private def externalLetters : Letter ↪ Sweep.Alphabet Row :=
  ⟨Sweep.row ∘ nativeRow, by
    intro first second equal
    exact nativeRow_injective (Sum.inr.inj (Option.some.inj equal))⟩

private def mark (row : Row) : Row := (row.1, fun _ => true)
private def empty : Row := mark Tracks.blank

private theorem represented (bits : List Bool) :
    Tracks.Represents (RawInput.rows empty mark (bits.map (nativeRow ∘ Sum.inl)))
      (BlockDecoder.tapes (BlockDecoder.wordTape [] (Binary.word bits)) (BlockDecoder.wordTape [] [])) := by
  intro name
  cases bits with
  | nil =>
    refine ⟨[], empty, [], rfl, ?_, rfl, ?_, ?_⟩
    · simp
    · simp
    · cases name <;> rfl
  | cons bit bits =>
    refine ⟨[], mark (nativeRow (.inl bit)), bits.map (nativeRow ∘ Sum.inl), rfl, ?_, rfl, ?_, ?_⟩
    · simp
    · intro row member
      obtain ⟨other, _, rfl⟩ := List.mem_map.mp member
      rfl
    · cases name with
      | false =>
        simp only [BlockDecoder.tapes, BlockDecoder.wordTape, Binary.word, List.map_cons,
          List.reverse_nil, List.map_nil, List.map_map, Function.comp_def, nativeRow, mark]
        rfl
      | true =>
        have blanks : Turing.ListBlank.mk (bits.map (fun _ => (none : Option Letter))) = Turing.ListBlank.mk [] := by
          rw [List.map_const']
          have blankSeq := TrackOutput.mk_append_blanks ([] : List (Option Letter)) bits.length
          exact blankSeq
        simp only [BlockDecoder.tapes, mark, nativeRow, List.reverse_nil, List.map_nil,
          List.map_map, Function.comp_def]
        rw [blanks]
        rfl

/-- The accepted native word, rejecting sentinel, and unused binary padding. -/
def inputBits {width : ℕ} (encode : Letter → Fin width → Bool) (sentinel : Fin width → Bool)
    (value : Word × List Bool) : List Bool :=
  value.1.flatMap (fun letter => List.ofFn (encode letter)) ++ List.ofFn sentinel ++ value.2

/-- The standalone decoder consumes ordinary external binary letters. -/
def inputWord {width : ℕ} (encode : Letter → Fin width → Bool) (sentinel : Fin width → Bool)
    (value : Word × List Bool) : Word :=
  (inputBits encode sentinel value).map Sum.inl

private theorem binary_inputBits {width : ℕ} (encode : Letter → Fin width → Bool)
    (sentinel : Fin width → Bool) (value : Word × List Bool) :
    Binary.word (inputBits encode sentinel value) =
      BlockDecoder.blocks encode value.1 ++ Binary.word (List.ofFn sentinel) ++ Binary.word value.2 := by
  simp [inputBits, BlockDecoder.blocks, Binary.word, List.map_flatMap, Function.comp_def]

/-- Standalone polynomial-time decoding, with raw preparation, simulation,
frame erasure, and native output all included. Only valid coded streams are
required: the mathematical input already specifies the live word and padding. -/
theorem polynomialTime (width : ℕ) (positive : 0 < width)
    (decode : (Fin width → Bool) → Option Letter) (encode : Letter → Fin width → Bool)
    (accepted : ∀ letter, decode (encode letter) = some letter)
    (sentinel : Fin width → Bool) (rejected : decode sentinel = none) :
    PolynomialTime (inputWord encode sentinel) id (fun value : Word × List Bool => value.1) := by
  classical
  let source := BlockDecoder.machine width decode
  let names := [false, true]
  let runOutput := sequence (Simulation.machine names source) (NativeTrackOutput.machine nativeRow) (0, ())
  let program := sequence (RawInput.machine empty mark) runOutput
    (.inl (Simulation.entry names (BlockDecoder.entry width)))
  let sourceBound : Polynomial ℕ := Polynomial.C (3 * width + 4) * Polynomial.X + Polynomial.C (2 * width + 4)
  let rowBound := Polynomial.X + 1 + 4 * sourceBound
  let simulationBound := sourceBound * (12 * rowBound + 79)
  let timeBound := 2 * (2 * (Polynomial.X + 1) + simulationBound + 4 * rowBound + 20) + Polynomial.X
  refine ⟨Sweep.Alphabet Row, inferInstance, inferInstance,
    SingleTape.Controller _, inferInstance, inferInstance, externalLetters,
    SingleTape.compile program, .inl (.inl (.inl 0)), timeBound, ?_, ?_⟩
  · intro letter
    change some _ ≠ none
    simp
  · intro value
    let bits := inputBits encode sentinel value
    let rows := RawInput.rows empty mark (bits.map (nativeRow ∘ Sum.inl))
    have rowsBound : rows.length ≤ bits.length + 1 := by
      simpa only [List.length_map] using RawInput.rows_length empty mark (bits.map (nativeRow ∘ Sum.inl))
    have nativeBound : value.1.length ≤ bits.length := by
      calc
        value.1.length = 1 * value.1.length := (one_mul _).symm
        _ ≤ width * value.1.length := Nat.mul_le_mul_right _ positive
        _ ≤ bits.length := by
          dsimp only [bits, inputBits]
          simp only [List.length_append, List.length_flatMap, List.length_ofFn]
          simp
          have multiplication := Nat.mul_comm width value.1.length
          omega
    have decoded := BlockDecoder.steps width decode encode accepted sentinel rejected value.1 (Binary.word value.2)
    rw [← binary_inputBits] at decoded
    obtain ⟨finalRows, simulationTicks, storage, simulationCost, finalRepresentation, simulated⟩ :=
      Simulation.steps names (by decide) (by intro name; cases name <;> simp [names]) source decoded (represented bits)
    have terminated := Simulation.terminal names source (BlockDecoder.exit width) finalRepresentation (by rfl)
    have finishedSimulation := simulated.trans terminated
    obtain ⟨extractTicks, extractCost, extracted⟩ := NativeTrackOutput.steps nativeRow value.1 finalRows (finalRepresentation true)
    have outputTrace := sequence_steps (Simulation.machine names source) (NativeTrackOutput.machine nativeRow) (0, ())
      finishedSimulation (by intro symbols; rfl) extracted
    have prepared := RawInput.steps empty mark (bits.map (nativeRow ∘ Sum.inl))
    have complete := sequence_steps (RawInput.machine empty mark) runOutput
      (.inl (Simulation.entry names (BlockDecoder.entry width))) prepared (by intro symbols; rfl) outputTrace
    have sourceCost : (3 * width + 4) * value.1.length + 2 * width + 4 ≤ sourceBound.eval bits.length := by
      simp only [sourceBound, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_left _ nativeBound) (2 * width)) 4
    have totalRows : rows.length + 4 * ((3 * width + 4) * value.1.length + 2 * width + 4) ≤ rowBound.eval bits.length := by
      simp only [rowBound, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_X]
      omega
    have finalRowsBound : finalRows.length ≤ rowBound.eval bits.length := by
      simp only [names, List.length_cons, List.length_nil] at storage
      exact storage.trans totalRows
    have simulatedBound : simulationTicks ≤ simulationBound.eval bits.length := by
      have cycleBound : Simulation.cycleCost names.length
          (rows.length + 2 * names.length * ((3 * width + 4) * value.1.length + 2 * width + 4)) ≤
          12 * rowBound.eval bits.length + 79 := by
        simp only [names, List.length_cons, List.length_nil, Simulation.cycleCost]
        omega
      refine simulationCost.trans ?_
      simp only [simulationBound, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_ofNat]
      exact Nat.mul_le_mul sourceCost cycleBound
    have totalCost : 2 * (2 * rows.length + 6 +
        (simulationTicks + (2 * finalRows.length + 4) + extractTicks + 1) + 1) ≤ timeBound.eval bits.length := by
      simp only [timeBound, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one,
        Polynomial.eval_X]
      omega
    constructor
    · refine ⟨2 * (2 * rows.length + 6 +
        (simulationTicks + (2 * finalRows.length + 4) + extractTicks + 1) + 1),
        .inl (.inr (.inr (7, ()))), ?_, ?_, ?_⟩
      · simpa only [inputWord, List.length_map] using totalCost
      · have translated := SingleTape.steps program complete
        convert translated using 1 <;>
          simp [SingleTape.configuration, inputWord, rows, bits, Sweep.tape, Turing.Tape.mk₁, Turing.Tape.mk₂,
            externalLetters, Function.comp_def, List.map_map]
      · have halted := SingleTape.halt program
          (.inr (.inr (7, ())), Sweep.tape [] (value.1.map (Sweep.row ∘ nativeRow))) (by rfl)
        convert halted using 1
        simp [SingleTape.configuration, Sweep.tape, Turing.Tape.mk₁, Turing.Tape.mk₂,
          externalLetters, Function.comp_def]
    · change value.1.length ≤ timeBound.eval (inputWord encode sentinel value).length
      simp only [inputWord, List.length_map]
      simp only [timeBound, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one,
        Polynomial.eval_X]
      dsimp only [bits] at nativeBound
      omega

end Polytime2.Complexity.BlockDecode
