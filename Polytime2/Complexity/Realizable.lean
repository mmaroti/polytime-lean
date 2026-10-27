import Polytime2.Complexity.Languages
import Polytime2.TM0.Computation
import Polytime2.Encoding.SizeSubstitution

/-! # From Polytime2 realizations to word complexity

Every realized computation is polynomial-time on its canonically serialized
admissible mathematical inputs. The proof uses the existing standalone TM0
export, including startup and extraction, and bounds every public size by its
unary header's contribution to the complete input word.

A total word reduction additionally needs a certified total parser/normalizer
and correctness on all words, including malformed representations. The bridge
does not assume that an admissible-input certificate handles arbitrary words.
-/

namespace Polytime2.Complexity.Internal

noncomputable def diagonal {Parameter : Type} (bound : MvPolynomial Parameter ℕ) : Polynomial ℕ :=
  MvPolynomial.eval₂Hom Polynomial.C (fun _ => Polynomial.X) bound

theorem diagonal_eval {Parameter : Type} (bound : MvPolynomial Parameter ℕ) (size : ℕ) :
    (diagonal bound).eval size = MvPolynomial.eval (fun _ => size) bound := by
  induction bound using MvPolynomial.induction_on with
  | C coefficient => simp [diagonal]
  | add first second firstEqual secondEqual => simpa [diagonal] using congrArg₂ (· + ·) firstEqual secondEqual
  | mul_X bound parameter equality => simpa [diagonal] using congrArg (· * size) equality

private theorem block_length_le_serialized (blocks : List (List Bool)) (block : List Bool)
    (member : block ∈ blocks) :
    block.length ≤ (DelimitedInput.serialize id blocks).length := by
  induction blocks with
  | nil => simp at member
  | cons first rest hypothesis =>
    have length : (DelimitedInput.serialize id (first :: rest)).length =
        first.length + 1 + (DelimitedInput.serialize id rest).length := by
      simp [DelimitedInput.serialize]
      omega
    rw [length]
    rcases List.mem_cons.mp member with equal | member
    · subst block; omega
    · have bounded := hypothesis member; omega

end Polytime2.Complexity.Internal

namespace Polytime2.Computation

open Complexity

universe carrierLevel
variable {Parameter InputName : Type} [Fintype Parameter] [Fintype InputName]

/-- Ordinary dependent pairs of sizes and admissible mathematical arguments. -/
abbrev AdmissibleInput (computation : Computation.{carrierLevel} Parameter InputName) :=
  Σ sizes : Parameter → ℕ, {arguments : computation.Arguments sizes // computation.precondition sizes arguments}

/-- Canonical public input word, including every unary size header. -/
noncomputable def inputWord (computation : Computation.{carrierLevel} Parameter InputName)
    (input : computation.AdmissibleInput) : Word := computation.serialize id input.1 input.2.val

/-- Mathematical results retain their size index, using the existing codec. -/
noncomputable def outputWord (computation : Computation.{carrierLevel} Parameter InputName)
    (output : Σ sizes, computation.outputDomain.Carrier sizes) : Word :=
  (EncodedDomain.ArrayEncoding.bits (computation.outputDomain.encode output.1 output.2)).map Sum.inl

/-- Evaluate the specified mathematical function and retain its output sizes. -/
def result (computation : Computation.{carrierLevel} Parameter InputName)
    (input : computation.AdmissibleInput) : Σ sizes, computation.outputDomain.Carrier sizes :=
  ⟨input.1, computation.compute input.1 input.2⟩

theorem size_le_inputWord_length (computation : Computation.{carrierLevel} Parameter InputName)
    (input : computation.AdmissibleInput) (parameter : Parameter) :
    input.1 parameter ≤ (computation.inputWord input).length := by
  classical
  have member : List.replicate (input.1 parameter) true ∈ computation.inputBlocks input.1 input.2.val :=
    List.mem_map.mpr ⟨Sum.inl parameter, by simp [inputRoles], rfl⟩
  simpa [inputWord, serialize] using Complexity.Internal.block_length_le_serialized
    (computation.inputBlocks input.1 input.2.val) (List.replicate (input.1 parameter) true) member

/-- Existing realizations yield actual finite TM0 certificates with polynomial
bounds in full serialized input length, on every admissible input. -/
theorem Realizable.polynomialTime {computation : Computation.{carrierLevel} Parameter InputName}
    (ready : computation.Realizable) :
    PolynomialTime computation.inputWord computation.outputWord computation.result := by
  obtain ⟨Symbol, finiteSymbols, inhabitedSymbols, letters, State, finiteStates, inhabitedStates,
    machine, bound, nonblank, execute⟩ := ready.tm0
  let _ : Inhabited Symbol := inhabitedSymbols
  let _ : Inhabited State := inhabitedStates
  let totalBound := Complexity.Internal.diagonal (bound + computation.outputDomain.widthPolynomial)
  refine ⟨Symbol, finiteSymbols, inhabitedSymbols, State, finiteStates, inhabitedStates,
    letters, machine, default, totalBound, nonblank, ?_⟩
  intro input
  obtain ⟨ticks, finalState, cost, trace, stopped⟩ := execute input.1 input.2.val input.2.property
  have monotone := SizeSubstitution.eval_mono (bound + computation.outputDomain.widthPolynomial)
    (computation.size_le_inputWord_length input)
  have total : MvPolynomial.eval input.1 bound + computation.outputDomain.width input.1 ≤
      totalBound.eval (computation.inputWord input).length := by
    simpa [totalBound, Complexity.Internal.diagonal_eval, EncodedDomain.width] using monotone
  constructor
  · refine ⟨ticks, finalState, by omega, ?_, ?_⟩
    · simpa [inputWord, outputWord, result, serialize, DelimitedInput.serialize,
        List.map_flatMap, List.map_map, Function.comp_def, Turing.TM0.init] using trace
    · simpa [outputWord, result, List.map_map, Function.comp_def] using stopped
  · simp [outputWord, result, EncodedDomain.ArrayEncoding.bits, EncodedDomain.width] at *
    omega

/-- A certified total parser/normalizer extends the admissible-input bridge to
an actual total word function. Malformed words must be handled by that parser
and the caller's all-word correctness proof. -/
theorem Realizable.wordFunction {computation : Computation.{carrierLevel} Parameter InputName}
    (ready : computation.Realizable) (parse : Word → computation.AdmissibleInput)
    (parserReady : PolynomialTime id computation.inputWord parse) :
    PolynomialTime id id (fun word => computation.outputWord (computation.result (parse word))) := by
  obtain ⟨Symbol, finiteSymbols, inhabitedSymbols, State, finiteStates, inhabitedStates,
    letters, machine, entry, bound, nonblank, execute⟩ := ready.polynomialTime.comp parserReady
  exact ⟨Symbol, finiteSymbols, inhabitedSymbols, State, finiteStates, inhabitedStates,
    letters, machine, entry, bound, nonblank, execute⟩

end Polytime2.Computation

namespace Polytime2.Complexity

/-- Turn a realized computation and a certified total parser into a polynomial
many-one reduction. Correctness must cover malformed words as well. -/
theorem ManyOneReducible.of_realizable
    {Parameter InputName : Type} [Fintype Parameter] [Fintype InputName]
    {computation : Computation Parameter InputName} (ready : computation.Realizable)
    (parse : Word → computation.AdmissibleInput)
    (parserReady : PolynomialTime id computation.inputWord parse)
    (source target : Language Letter)
    (correct : ∀ word, word ∈ source ↔ computation.outputWord (computation.result (parse word)) ∈ target) :
    ManyOneReducible source target :=
  ⟨_, ready.wordFunction parse parserReady, correct⟩

end Polytime2.Complexity
