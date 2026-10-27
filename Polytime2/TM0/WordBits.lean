import Polytime2.TM0.RawInput
import Polytime2.TM0.CallingConventionOutput
import Polytime2.Computation.Realizable
import Polytime2.Encoding.BinaryEncoding

/-! # Raw words as Boolean input tracks

Each raw input symbol supplies three Boolean tracks and one unary length
track. The raw-input adapter marks their common initial head. Output and
scratch tracks begin blank and can grow under the existing simulator. This
avoids presupposing a well-formed header on arbitrary word inputs.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.WordBits

open MultiTape CallingConvention EncodedDomain

variable {Scratch : Type}

abbrev TapeName (Scratch : Type) := Unit ⊕ (Fin 3 ⊕ (Unit ⊕ Scratch))

/-- Input symbols carry only immutable source data; simulated heads are marked
by the raw-input adapter, not by the external word alphabet. -/
def row (bits : Fin 3 → Bool) : Tracks.Row (Alphabet (TapeName Scratch)) :=
  ((fun name => match name with
    | .inl () => Binary.data true
    | .inr (.inl index) => Binary.data (bits index)
    | .inr (.inr _) => 0), fun _ => false)

def mark (source : Tracks.Row (Alphabet (TapeName Scratch))) : Tracks.Row (Alphabet (TapeName Scratch)) :=
  (source.1, fun _ => true)

def empty : Tracks.Row (Alphabet (TapeName Scratch)) := (fun _ => 0, fun _ => true)

def tapes {Letter : Type} (code : Letter → Fin 3 → Bool) : List Letter → Tapes (Alphabet (TapeName Scratch))
  | [] => fun _ => Turing.Tape.mk₁ []
  | first :: rest => fun name =>
      ⟨(row (code first)).1 name, Turing.ListBlank.mk [],
        Turing.ListBlank.mk (rest.map (fun letter => (row (code letter)).1 name))⟩

theorem represented {Letter : Type} (code : Letter → Fin 3 → Bool) (word : List Letter) :
    Tracks.Represents (RawInput.rows (empty (Scratch := Scratch)) mark (word.map (fun letter => row (code letter))))
      (tapes (Scratch := Scratch) code word) := by
  intro name
  cases word with
  | nil => exact ⟨[], empty, [], rfl, by simp, rfl, by simp, rfl⟩
  | cons first rest =>
    exact ⟨[], mark (row (code first)), rest.map (fun letter => row (code letter)),
      rfl, by simp, rfl, by
        intro entry member
        obtain ⟨letter, _, rfl⟩ := List.mem_map.mp member
        rfl, by
        simp only [tapes, mark, List.reverse_nil, List.map_nil, List.map_map]; rfl⟩

@[simp] private theorem mk_blanks (size : ℕ) :
    Turing.ListBlank.mk (List.replicate size (0 : Binary.Symbol)) = Turing.ListBlank.mk [] := by
  exact Quotient.sound (Or.inr ⟨size, by simp⟩)

theorem writable_blank {Letter : Type} (code : Letter → Fin 3 → Bool)
    (word : List Letter) (name : Unit ⊕ Scratch) :
    tapes code word (.inr (.inr name)) = Turing.Tape.mk₁ [] := by
  cases word with
  | nil => rfl
  | cons first rest =>
    simp [tapes, row, Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk']

theorem boolean_bits (sizes : Unit → ℕ) (value : Bool) :
    ArrayEncoding.bits ((booleans : EncodedDomain Unit).encode sizes value) = [value] := by
  cases value <;> simp only [booleans, fixed_encode_bits] <;> decide

theorem boolean_array_bits (sizes : Unit → ℕ) (values : Fin (sizes ()) → Bool) :
    ArrayEncoding.bits (((booleans : EncodedDomain Unit).array ()).encode sizes values) = List.ofFn values := by
  rw [array_encode_bits, ArrayEncoding.bits_encode]
  simp only [boolean_bits]
  simpa only [List.flatMap_def, List.map_ofFn, Function.comp_def] using List.flatMap_singleton' (List.ofFn values)

def arguments {Letter : Type} (code : Letter → Fin 3 → Bool) (word : List Letter) :
    Fin 3 → Fin word.length → Bool := fun bit index => code word[index] bit

theorem input_tape {Letter : Type} (code : Letter → Fin 3 → Bool) (word : List Letter) (bit : Fin 3) :
    tapes (Scratch := Scratch) code word (.inr (.inl bit)) =
      encoded ((booleans : EncodedDomain Unit).array ()) (fun _ => word.length) (arguments code word bit) := by
  rw [encoded, boolean_array_bits]
  have bits : List.ofFn (arguments code word bit) = word.map (fun letter => code letter bit) :=
    List.ofFn_getElem_eq_map word (fun letter => code letter bit)
  rw [bits]
  cases word with
  | nil => rfl
  | cons first rest =>
    simp [tapes, row, CallingConvention.tape, Binary.word, Turing.Tape.mk₁, Turing.Tape.mk₂,
      Turing.Tape.mk', List.map_map, Function.comp_def]

theorem size_tape {Letter : Type} (code : Letter → Fin 3 → Bool) (word : List Letter) :
    tapes (Scratch := Scratch) code word (.inl ()) = unary word.length := by
  cases word with
  | nil => rfl
  | cons first rest =>
    simp [tapes, row, CallingConvention.unary, CallingConvention.tape, Binary.word,
      Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk', List.replicate_succ]

/-- The three input arrays and length tape satisfy the ordinary calling
convention. Writable regions may have any polynomial width, including zero. -/
theorem entry {Letter : Type} (code : Letter → Fin 3 → Bool) (word : List Letter)
    (scratchDomains : Scratch → EncodedDomain Unit)
    (operation : (size : ℕ) → (Fin 3 → Fin size → Bool) → Bool) :
    let computation : Computation Unit (Fin 3) :=
      ⟨(fun _ => booleans.array ()), booleans, (fun _ _ => True), (fun sizes arguments => operation (sizes ()) arguments.val)⟩
    let inputs : Inputs (Computation.Realizable.Internal.domains computation scratchDomains)
        (Computation.Realizable.Internal.readOnly computation) (fun _ => word.length) :=
      fun name => match name with
      | ⟨.inl (), _⟩ => PUnit.unit
      | ⟨.inr (.inl bit), _⟩ => arguments code word bit
      | ⟨.inr (.inr _), impossible⟩ => False.elim (Bool.noConfusion impossible)
    Entry (Computation.Realizable.Internal.domains computation scratchDomains)
      (Computation.Realizable.Internal.readOnly computation) (fun _ => word.length) inputs (tapes code word) := by
  intro computation inputs
  constructor
  · intro name immutable
    rcases name with parameter | bit | output | scratch
    · cases parameter
      exact (size_tape code word).trans (encoded_unary () (fun _ => word.length)).symm
    · exact input_tape code word bit
    · cases immutable
    · cases immutable
  · intro name writable
    rcases name with parameter | bit | output | scratch
    · cases writable
    · cases writable
    · refine ⟨List.replicate (computation.outputDomain.width (fun _ => word.length)) 0,
        by simp only [List.length_replicate]; rfl, ?_⟩
      rw [writable_blank]
      simp [buffer, Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk']
    · refine ⟨List.replicate ((scratchDomains scratch).width (fun _ => word.length)) 0,
        by simp only [List.length_replicate]; rfl, ?_⟩
      rw [writable_blank]
      simp [buffer, Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk']

end Polytime2.WordBits
