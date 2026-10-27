import Polytime2.TM0.Sweep

/-! # Preparing a marked interval from arbitrary raw input rows

Raw input has no framing markers. This adapter marks its first row, supplies
one row for empty input, writes left and right boundaries in adjacent blanks,
and restores the head to the first row. It reuses the sweep prefix and rewind
rules. The controller and row transformations are fixed independently of the
input length; the row count is never stored in the finite controller.
-/

namespace Polytime2.RawInput

open MultiTape

universe rowLevel
variable {Row : Type rowLevel}

@[simp] private theorem alphabet_default : (default : Sweep.Alphabet Row) = none := rfl

/-- Empty input still has one row for the initial simulated heads. -/
def rows (empty : Row) (mark : Row → Row) : List Row → List Row
  | [] => [empty]
  | first :: rest => mark first :: rest

theorem rows_length (empty : Row) (mark : Row → Row) (payload : List Row) :
    (rows empty mark payload).length ≤ payload.length + 1 := by
  cases payload <;> simp [rows]

private def markHead (empty : Row) (mark : Row → Row) : Sweep.Alphabet Row → Sweep.Alphabet Row
  | some (.inr value) => Sweep.row (mark value)
  | _ => Sweep.row empty

/-- Mark the head row and install the left boundary in two transitions. -/
def markStart (empty : Row) (mark : Row → Row) :
    Machine (fun _ : Unit => Sweep.Alphabet Row) (Fin 3)
  | state, symbols => match state.val with
    | 0 => some (1, fun _ => (markHead empty mark (symbols ()), some .left))
    | 1 => some (2, fun _ => (Sweep.leftMarker, some .right))
    | _ => none

theorem markStart_steps (empty : Row) (mark : Row → Row) (payload : List Row) :
    Steps (markStart empty mark) 2
      (0, Sweep.tape [] (payload.map Sweep.row))
      (2, Sweep.tape [Sweep.leftMarker] ((rows empty mark payload).map Sweep.row)) := by
  have first : step (markStart empty mark) (0, Sweep.tape [] (payload.map Sweep.row)) =
      some (1, Sweep.tape [] (none :: (rows empty mark payload).map Sweep.row)) := by
    cases payload with
    | nil =>
      simp [step, markStart, MultiTape.read, Sweep.tape, rows, markHead]
      funext name; cases name
      simp [act, Sweep.tape, Turing.Tape.write_mk', Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk]
    | cons head tail =>
      simp [step, markStart, MultiTape.read, Sweep.tape, rows, markHead, Sweep.row]
      funext name; cases name
      simp [act, Sweep.tape, Turing.Tape.write_mk', Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk]
  have second : step (markStart empty mark)
      (1, Sweep.tape [] (none :: (rows empty mark payload).map Sweep.row)) =
      some (2, Sweep.tape [Sweep.leftMarker] ((rows empty mark payload).map Sweep.row)) := by
    simp [step, markStart]
    funext name; cases name
    simp [act, Sweep.tape, Turing.Tape.write_mk', Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
  exact .next first (.next second (.zero _))

private def visit (_ : Unit) (row : Row) : Unit × Row := ((), row)

private theorem run_visit (payload : List Row) : Sweep.run visit () payload = ((), payload) := by
  induction payload with
  | nil => rfl
  | cons first rest hypothesis => simp [Sweep.run, visit, hypothesis]

/-- A sweep whose forward pass closes the raw interval at the first blank. -/
def close : Machine (fun _ : Unit => Sweep.Alphabet Row) (Sweep.Controller Unit) :=
  fun state symbols => match Sweep.machine visit state symbols with
  | some command => some command
  | none => match state, symbols () with
    | .inl (false, ()), none => some (.inl (true, ()), fun _ => (Sweep.rightMarker, none))
    | _, _ => none

private theorem close_transfer {ticks : ℕ} {initial final : Configuration (fun _ : Unit => Sweep.Alphabet Row)
    (Sweep.Controller Unit)} (trace : Steps (Sweep.machine visit) ticks initial final) :
    Steps close ticks initial final := by
  simpa only [id_eq] using trace.rename id (target := close)
    (by intro state symbols next actions transition; simp [close, transition])

/-- Discover the raw interval's right end and restore its head. -/
theorem close_steps (payload : List Row) :
    Steps close (2 * payload.length + 3)
      (.inl (false, ()), Sweep.tape [Sweep.leftMarker] (payload.map Sweep.row))
      (.inr (), Sweep.tape [Sweep.leftMarker] (payload.map Sweep.row ++ [Sweep.rightMarker])) := by
  have scanned := close_transfer (Sweep.forward visit () payload [Sweep.leftMarker] [])
  simp only [run_visit, List.append_nil] at scanned
  have turn : step close
      (.inl (false, ()), Sweep.tape (payload.reverse.map Sweep.row ++ [Sweep.leftMarker]) []) =
      some (.inl (true, ()), Sweep.tape (payload.reverse.map Sweep.row ++ [Sweep.leftMarker]) [Sweep.rightMarker]) := by
    simp [step, close, Sweep.machine, MultiTape.read, Sweep.tape]
    funext name; cases name
    simp [act, Sweep.tape, Turing.Tape.write_mk', Turing.ListBlank.cons_mk]
  have returned := close_transfer (Sweep.rewind visit () payload.reverse Sweep.rightMarker (by rfl) [] [])
  have complete := scanned.trans (.next turn returned)
  simpa [List.map_reverse, Nat.two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using complete

/-- Complete raw-row preparation with one controller handover. -/
def machine (empty : Row) (mark : Row → Row) :=
  MultiTape.sequence (markStart empty mark) close (.inl (false, ()))

theorem steps (empty : Row) (mark : Row → Row) (payload : List Row) :
    Steps (machine empty mark) (2 * (rows empty mark payload).length + 6)
      (.inl 0, Sweep.tape [] (payload.map Sweep.row))
      (.inr (.inr ()), Sweep.tape [Sweep.leftMarker]
        ((rows empty mark payload).map Sweep.row ++ [Sweep.rightMarker])) := by
  have complete := sequence_steps (markStart empty mark) close (.inl (false, ()))
    (markStart_steps empty mark payload) (by intro symbols; rfl) (close_steps (rows empty mark payload))
  have arithmetic : 2 + (2 * (rows empty mark payload).length + 3) + 1 =
      2 * (rows empty mark payload).length + 6 := by omega
  simpa only [machine, arithmetic] using complete

theorem halt (empty : Row) (mark : Row → Row) (symbols) :
    machine empty mark (.inr (.inr ())) symbols = none := rfl

end Polytime2.RawInput
