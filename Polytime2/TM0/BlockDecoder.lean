import Polytime2.Primitives.FixedRead
import Polytime2.Machine.Wiring

/-! # Fixed-block decoding into a native output tape

A specialization-fixed finite decoder reads one binary block into the existing
fixed-width register. Accepted blocks emit one native symbol; a rejected block
ends the stream. The output head is restored before native-symbol extraction.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.BlockDecoder

open MultiTape CallingConvention

variable {Letter : Type}

/-- The input stays binary; the output stores actual native symbols. -/
def Alphabet : Bool → Type
  | false => Binary.Symbol
  | true => Option Letter

instance alphabetInhabited (name : Bool) : Inhabited (Alphabet (Letter := Letter) name) := by
  cases name <;> dsimp [Alphabet] <;> infer_instance

instance alphabetFintype [Fintype Letter] (name : Bool) : Fintype (Alphabet (Letter := Letter) name) := by
  cases name <;> dsimp [Alphabet] <;> infer_instance

/-- Reading, advancing past an accepted block, and rewinding the output. -/
abbrev State (width : ℕ) := StandardFixedRead.State width ⊕ (Fin (width + 1) ⊕ Fin 3)

def entry (width : ℕ) : State width := .inl ((false, Fin.last width), fun _ => false)
def exit (width : ℕ) : State width := .inr (.inr 2)

/-- Only the binary reader and input-head movement use the standard routines.
Native writes and the final rewind need no alternate binary encoding. -/
noncomputable def machine (width : ℕ) (decode : (Fin width → Bool) → Option Letter) :
    Machine (Alphabet (Letter := Letter)) (State width) := fun state symbols =>
  match state with
  | .inl reading =>
    match wire (oneTape false) (StandardFixedRead.machine width) reading symbols with
    | some (next, actions) => some (.inl next, actions)
    | none => match decode reading.2 with
      | none => some (.inr (.inr 0), stationary symbols)
      | some letter => some (.inr (.inl (Fin.last width)), fun name => match name with
        | false => (symbols false, none)
        | true => (some letter, some .right))
  | .inr (.inl advancing) =>
    match wire (oneTape false) (Move.machine width .right) advancing symbols with
    | some (next, actions) => some (.inr (.inl next), actions)
    | none => some (entry width, stationary symbols)
  | .inr (.inr phase) => match phase.val with
    | 0 => some (.inr (.inr 1), fun name => match name with
      | false => (symbols false, none)
      | true => (symbols true, some .left))
    | 1 => match symbols true with
      | none => some (exit width, fun name => match name with
        | false => (symbols false, none)
        | true => (none, some .right))
      | some _ => some (.inr (.inr 1), fun name => match name with
        | false => (symbols false, none)
        | true => (symbols true, some .left))
    | _ => none

/-- Ordinary two-sided tape words, with the left list in tape order. -/
def wordTape {Symbol : Type} [Inhabited Symbol] (left right : List Symbol) : Turing.Tape Symbol :=
  Turing.Tape.mk' (Turing.ListBlank.mk left) (Turing.ListBlank.mk right)

def tapes (input : Turing.Tape Binary.Symbol) (output : Turing.Tape (Option Letter)) :
    Tapes (Alphabet (Letter := Letter)) := fun name => match name with
  | false => input
  | true => output

/-- Reuse fixed scalar reading, retaining both the source word and the native
output tape exactly. One block costs `2 * width + 1` transitions. -/
theorem read_steps (width : ℕ) (decode : (Fin width → Bool) → Option Letter)
    (bits : Fin width → Bool) (left right : List Binary.Symbol) (output : Turing.Tape (Option Letter)) :
    Steps (machine width decode) (2 * width + 1)
      (entry width, tapes (wordTape left (Binary.word (List.ofFn bits) ++ right)) output)
      (.inl ((true, 0), bits), tapes (wordTape left (Binary.word (List.ofFn bits) ++ right)) output) := by
  have read := (StandardFixedRead.runsWithContext width (List.ofFn bits) List.length_ofFn
    (fun _ => false) left right).steps
  have memory : (fun index : Fin width => ((List.ofFn bits)[index.val]?).getD false) = bits := by
    funext index
    simp [index.isLt]
  rw [memory] at read
  have wired := wire_steps_of_eq (oneTape false) (StandardFixedRead.machine width) read
    (tapes (wordTape left (Binary.word (List.ofFn bits) ++ right)) output)
    (tapes (wordTape left (Binary.word (List.ofFn bits) ++ right)) output)
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
  exact wired.rename Sum.inl (target := machine width decode) (by
    intro state symbols next actions transition
    simp only [machine, transition])

/-- Advance over the accepted block, sharing the certified fixed movement. -/
theorem advance_steps (width : ℕ) (decode : (Fin width → Bool) → Option Letter)
    (bits : Fin width → Bool) (left right : List Binary.Symbol) (output : Turing.Tape (Option Letter)) :
    Steps (machine width decode) (width + 1)
      (.inr (.inl (Fin.last width)), tapes (wordTape left (Binary.word (List.ofFn bits) ++ right)) output)
      (entry width, tapes (wordTape ((Binary.word (List.ofFn bits)).reverse ++ left) right) output) := by
  have movement := Move.steps width .right
    (fun _ : Unit => wordTape left (Binary.word (List.ofFn bits) ++ right))
  have moved := Move.right_list (Binary.word (List.ofFn bits)) left right
  simp only [Binary.word, List.length_map, List.length_ofFn] at moved
  have wired := wire_steps_of_eq (oneTape false) (Move.machine width .right) movement
    (tapes (wordTape left (Binary.word (List.ofFn bits) ++ right)) output)
    (tapes (wordTape ((Binary.word (List.ofFn bits)).reverse ++ left) right) output)
    (by intros; rfl) (by intros; exact moved.symm) (by
      intro name outside
      cases name
      · exact False.elim (outside ⟨(), rfl⟩)
      · rfl)
  have advancing := wired.rename (fun state => Sum.inr (Sum.inl state)) (target := machine width decode) (by
    intro state symbols next actions transition
    simp only [machine, transition])
  have handover : step (machine width decode)
      (.inr (.inl 0), tapes (wordTape ((Binary.word (List.ofFn bits)).reverse ++ left) right) output) =
      some (entry width, tapes (wordTape ((Binary.word (List.ofFn bits)).reverse ++ left) right) output) := by
    simp [step, machine, wire, Move.machine, act_stationary]
  simpa only [Nat.add_comm width 1] using advancing.trans (.next handover (.zero _))

/-- An accepted block writes precisely one native symbol and advances to the
next block, leaving every input symbol unchanged. -/
theorem accepted_steps (width : ℕ) (decode : (Fin width → Bool) → Option Letter)
    (bits : Fin width → Bool) (letter : Letter) (decoded : decode bits = some letter)
    (left right : List Binary.Symbol) (outputLeft : List (Option Letter)) :
    Steps (machine width decode) (3 * width + 3)
      (entry width, tapes (wordTape left (Binary.word (List.ofFn bits) ++ right)) (wordTape outputLeft []))
      (entry width, tapes (wordTape ((Binary.word (List.ofFn bits)).reverse ++ left) right)
        (wordTape (some letter :: outputLeft) [])) := by
  have read := read_steps width decode bits left right (wordTape outputLeft [])
  have emitted : step (machine width decode)
      (.inl ((true, 0), bits), tapes (wordTape left (Binary.word (List.ofFn bits) ++ right)) (wordTape outputLeft [])) =
      some (.inr (.inl (Fin.last width)),
        tapes (wordTape left (Binary.word (List.ofFn bits) ++ right)) (wordTape (some letter :: outputLeft) [])) := by
    simp [step, machine, wire, StandardFixedRead.machine, decoded, MultiTape.read, tapes]
    funext name
    cases name
    · simp [act, tapes, Turing.Tape.write_self]
    · simp [act, tapes, wordTape, Turing.Tape.write_mk', Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
  have advanced := advance_steps width decode bits left right (wordTape (some letter :: outputLeft) [])
  convert read.trans (.next emitted advanced) using 1
  omega

/-- The first rejected block terminates the stream without interpreting any
following padding as a native symbol. -/
theorem rejected_steps (width : ℕ) (decode : (Fin width → Bool) → Option Letter)
    (bits : Fin width → Bool) (decoded : decode bits = none)
    (left right : List Binary.Symbol) (output : Turing.Tape (Option Letter)) :
    Steps (machine width decode) (2 * width + 2)
      (entry width, tapes (wordTape left (Binary.word (List.ofFn bits) ++ right)) output)
      (.inr (.inr 0), tapes (wordTape left (Binary.word (List.ofFn bits) ++ right)) output) := by
  have read := read_steps width decode bits left right output
  have stopped : step (machine width decode)
      (.inl ((true, 0), bits), tapes (wordTape left (Binary.word (List.ofFn bits) ++ right)) output) =
      some (.inr (.inr 0), tapes (wordTape left (Binary.word (List.ofFn bits) ++ right)) output) := by
    simp [step, machine, wire, StandardFixedRead.machine, decoded, act_stationary]
  exact read.trans (.next stopped (.zero _))

private theorem none_cons_empty :
    (Turing.ListBlank.mk ([] : List (Option Letter))).cons none = Turing.ListBlank.mk [] :=
  Turing.ListBlank.cons_head_tail (Turing.ListBlank.mk [])

private theorem rewind_scan_steps (width : ℕ) (decode : (Fin width → Bool) → Option Letter)
    (input : Turing.Tape Binary.Symbol) (left : List Letter) (current : Letter) (right : List (Option Letter)) :
    Steps (machine width decode) (left.length + 2)
      (.inr (.inr 1), tapes input (wordTape (left.map some) (some current :: right)))
      (exit width, tapes input (wordTape [] (left.reverse.map some ++ some current :: right))) := by
  induction left generalizing current right with
  | nil =>
    refine Steps.next (middle := (.inr (.inr 1), tapes input (wordTape [] (none :: some current :: right))))
      ?_ (.next ?_ (.zero _))
    · simp [step, machine, MultiTape.read, tapes, wordTape]
      funext name
      cases name <;> simp [act, tapes, Turing.Tape.write_mk', Turing.Tape.move_left_mk',
        ← Turing.ListBlank.cons_mk]
      rfl
    · simp [step, machine, MultiTape.read, tapes, wordTape, exit]
      funext name
      cases name <;> simp [act, tapes, Turing.Tape.write_mk', Turing.Tape.move_right_mk',
        ← Turing.ListBlank.cons_mk]
      exact congrArg (fun before : Turing.ListBlank (Option Letter) =>
        Turing.Tape.mk' before (Turing.ListBlank.mk (some current :: right))) (none_cons_empty (Letter := Letter))
  | cons letter left hypothesis =>
    have moved : step (machine width decode)
        (.inr (.inr 1), tapes input (wordTape ((letter :: left).map some) (some current :: right))) =
        some (.inr (.inr 1), tapes input (wordTape (left.map some) (some letter :: some current :: right))) := by
      simp [step, machine, MultiTape.read, tapes, wordTape]
      funext name
      cases name <;> simp [act, tapes, Turing.Tape.write_mk', Turing.Tape.move_left_mk',
        ← Turing.ListBlank.cons_mk]
    have rest := hypothesis letter (some current :: right)
    simpa only [List.length_cons, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc, List.singleton_append] using Steps.next moved rest

/-- Restore the native output head, including when no symbol was emitted. -/
theorem rewind_steps (width : ℕ) (decode : (Fin width → Bool) → Option Letter)
    (input : Turing.Tape Binary.Symbol) (letters : List Letter) :
    Steps (machine width decode) (letters.length + 2)
      (.inr (.inr 0), tapes input (wordTape (letters.map some) []))
      (exit width, tapes input (wordTape [] (letters.reverse.map some))) := by
  cases letters with
  | nil =>
    refine Steps.next (middle := (.inr (.inr 1), tapes input (wordTape [] []))) ?_ (.next ?_ (.zero _))
    · simp [step, machine, MultiTape.read, tapes, wordTape]
      funext name
      cases name <;> simp [act, tapes, Turing.Tape.write_mk', Turing.Tape.move_left_mk',
        -Turing.ListBlank.cons_mk]
      apply congrArg (Turing.Tape.mk' (Turing.ListBlank.mk ([] : List (Option Letter))))
      change ((Turing.ListBlank.mk ([] : List (Option Letter))).cons none).cons none = Turing.ListBlank.mk []
      exact (congrArg (fun source : Turing.ListBlank (Option Letter) => source.cons none)
        (none_cons_empty (Letter := Letter))).trans (none_cons_empty (Letter := Letter))
    · have instruction : machine width decode (.inr (.inr 1)) (read (tapes input (wordTape [] []))) =
          some (exit width, fun name => match name with
            | false => (input.head, none) | true => (none, some .right)) := rfl
      simp only [step, instruction, Option.map_some, Option.some.injEq, Prod.mk.injEq, true_and]
      funext name
      cases name <;> simp [act, tapes, -Turing.ListBlank.cons_mk]
      exact congrArg (fun before : Turing.ListBlank (Option Letter) =>
        Turing.Tape.mk' before (Turing.ListBlank.mk [])) (none_cons_empty (Letter := Letter))
  | cons letter letters =>
    have moved : step (machine width decode)
        (.inr (.inr 0), tapes input (wordTape ((letter :: letters).map some) [])) =
        some (.inr (.inr 1), tapes input (wordTape (letters.map some) [some letter])) := by
      simp [step, machine, MultiTape.read, tapes, wordTape]
      funext name
      cases name <;> simp [act, tapes, Turing.Tape.write_mk', Turing.Tape.move_left_mk',
        ← Turing.ListBlank.cons_mk]
      exact congrArg (fun after : Turing.ListBlank (Option Letter) =>
        Turing.Tape.mk' (Turing.ListBlank.mk (letters.map some)) (after.cons (some letter)))
        (none_cons_empty (Letter := Letter))
    have rest := rewind_scan_steps width decode input letters letter []
    simpa only [List.length_cons, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      List.append_nil] using Steps.next moved rest

/-- Canonical binary blocks in their original source order. -/
def blocks {width : ℕ} (encode : Letter → Fin width → Bool) (letters : List Letter) : List Binary.Symbol :=
  letters.flatMap (fun letter => Binary.word (List.ofFn (encode letter)))

@[simp] theorem blocks_length {width : ℕ} (encode : Letter → Fin width → Bool) (letters : List Letter) :
    (blocks encode letters).length = width * letters.length := by
  simp [blocks, Binary.word, Nat.mul_comm]

/-- Decode a finite accepted prefix, preserving arbitrary following symbols. -/
theorem prefix_steps (width : ℕ) (decode : (Fin width → Bool) → Option Letter)
    (encode : Letter → Fin width → Bool) (accepted : ∀ letter, decode (encode letter) = some letter)
    (letters : List Letter) (left right : List Binary.Symbol) (outputLeft : List (Option Letter)) :
    Steps (machine width decode) ((3 * width + 3) * letters.length)
      (entry width, tapes (wordTape left (blocks encode letters ++ right)) (wordTape outputLeft []))
      (entry width, tapes (wordTape ((blocks encode letters).reverse ++ left) right)
        (wordTape ((letters.reverse.map some) ++ outputLeft) [])) := by
  induction letters generalizing left outputLeft with
  | nil =>
    simpa only [blocks, List.flatMap_nil, List.reverse_nil, List.nil_append, List.map_nil,
      List.length_nil, Nat.mul_zero] using
        (Steps.zero (machine := machine width decode) (entry width, tapes (wordTape left right) (wordTape outputLeft [])))
  | cons letter letters hypothesis =>
    have first := accepted_steps width decode (encode letter) letter (accepted letter)
      left (blocks encode letters ++ right) outputLeft
    have rest := hypothesis ((Binary.word (List.ofFn (encode letter))).reverse ++ left) (some letter :: outputLeft)
    simpa only [blocks, List.flatMap_cons, List.append_assoc, List.reverse_append, List.reverse_cons,
      List.map_append, List.map_cons, List.map_nil, List.singleton_append, List.length_cons, Nat.mul_succ,
      Nat.add_comm ((3 * width + 3) * letters.length) (3 * width + 3)] using first.trans rest

/-- A rejected sentinel ends decoding before padding. The final native word
is exact, its head is restored, and all source blocks remain unchanged.
The transition count includes reading, advancing, and restoring the output. -/
theorem steps (width : ℕ) (decode : (Fin width → Bool) → Option Letter)
    (encode : Letter → Fin width → Bool) (accepted : ∀ letter, decode (encode letter) = some letter)
    (sentinel : Fin width → Bool) (rejected : decode sentinel = none)
    (letters : List Letter) (padding : List Binary.Symbol) :
    Steps (machine width decode) ((3 * width + 4) * letters.length + 2 * width + 4)
      (entry width, tapes (wordTape [] (blocks encode letters ++ Binary.word (List.ofFn sentinel) ++ padding))
        (wordTape [] []))
      (exit width, tapes (wordTape (blocks encode letters).reverse (Binary.word (List.ofFn sentinel) ++ padding))
        (wordTape [] (letters.map some))) := by
  have decodedPrefix := prefix_steps width decode encode accepted letters []
    (Binary.word (List.ofFn sentinel) ++ padding) []
  simp only [List.append_nil] at decodedPrefix
  have stop := rejected_steps width decode sentinel rejected (blocks encode letters).reverse padding
    (wordTape (letters.reverse.map some) [])
  have returned := rewind_steps width decode
    (wordTape (blocks encode letters).reverse (Binary.word (List.ofFn sentinel) ++ padding)) letters.reverse
  simp only [List.reverse_reverse, List.length_reverse] at returned
  have complete := decodedPrefix.trans (stop.trans returned)
  convert complete using 1
  · ring
  · simp only [List.append_assoc]

/-- Positive block width bounds every emitted symbol by a source symbol.
Consequently the exact decoder trace has a linear bound in its complete input,
including the sentinel and arbitrary trailing capacity padding. -/
theorem time_bound (width : ℕ) (positive : 0 < width) (encode : Letter → Fin width → Bool)
    (sentinel : Fin width → Bool) (letters : List Letter) (padding : List Binary.Symbol) :
    (3 * width + 4) * letters.length + 2 * width + 4 ≤
      (3 * width + 4) * (blocks encode letters ++ Binary.word (List.ofFn sentinel) ++ padding).length + 2 * width + 4 := by
  have prefixBound : letters.length ≤ (blocks encode letters ++ Binary.word (List.ofFn sentinel) ++ padding).length := by
    calc
      letters.length = 1 * letters.length := (one_mul _).symm
      _ ≤ width * letters.length := Nat.mul_le_mul_right _ positive
      _ ≤ _ := by simp only [List.length_append, blocks_length]; omega
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_left _ prefixBound) (2 * width)) 4

@[simp] theorem halt (width : ℕ) (decode : (Fin width → Bool) → Option Letter)
    (symbols : Symbols (Alphabet (Letter := Letter))) : machine width decode (exit width) symbols = none := rfl

end Polytime2.BlockDecoder
