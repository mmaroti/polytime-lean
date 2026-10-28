import Mathlib.Data.List.Basic
import Mathlib.Logic.Function.Basic
import Lean.Elab.Tactic.Omega

/-! # Boolean circuits with shared wires

A gate is a Boolean constant or a NAND of two numbered wires. A program is
an ordered list of gates; starting with `inputs` input wires, gate `index`
defines wire `inputs + index`. `WellFormed` requires every operand to refer
to an input or an earlier gate. A circuit pairs a program with an output
wire. No machine representation or complexity certificate is assumed here.

NAND and constants suffice for the bounded-machine simulation and give the
following Tseitin conversion a fixed gate basis. Sharing is explicit: reading
a wire does not copy the circuit producing it.
-/

namespace Polytime2.Circuit

/-- A constant, or two inputs to a NAND gate. -/
abbrev Gate := Bool ⊕ (ℕ × ℕ)

/-- Gate semantics on an assignment to numbered wires. -/
def Gate.eval (gate : Gate) (values : ℕ → Bool) : Bool :=
  match gate with
  | .inl value => value
  | .inr (left, right) => !(values left && values right)

/-- All operands precede the wire being defined. -/
def Gate.Valid (available : ℕ) (gate : Gate) : Prop :=
  match gate with
  | .inl _ => True
  | .inr (left, right) => left < available ∧ right < available

theorem Gate.Valid.mono {gate : Gate} {source target : ℕ}
    (valid : gate.Valid source) (bounded : source ≤ target) : gate.Valid target := by
  cases gate with
  | inl value => trivial
  | inr pair => exact ⟨Nat.lt_of_lt_of_le valid.1 bounded, Nat.lt_of_lt_of_le valid.2 bounded⟩

/-- Evaluate successive gates, assigning one fresh wire per gate. -/
def run (start : ℕ) (gates : List Gate) (values : ℕ → Bool) : ℕ → Bool :=
  match gates with
  | [] => values
  | gate :: rest => run (start + 1) rest
      (Function.update values start (gate.eval values))

/-- A program is acyclic when each gate reads only earlier wires. -/
def WellFormed (start : ℕ) (gates : List Gate) : Prop :=
  match gates with
  | [] => True
  | gate :: rest => gate.Valid start ∧ WellFormed (start + 1) rest

/-- Every reference in an acyclic program is below its total wire count. -/
theorem WellFormed.gates_valid {start : ℕ} {gates : List Gate} (valid : WellFormed start gates) :
    ∀ gate ∈ gates, gate.Valid (start + gates.length) := by
  induction gates generalizing start with
  | nil => simp
  | cons head rest induction =>
    intro gate member
    rcases List.mem_cons.mp member with equal | member
    · subst gate
      exact valid.1.mono (by simp)
    · exact (induction valid.2 gate member).mono (by simp; omega)

/-- Circuit data consists of a gate list and a selected output wire. -/
abbrev Network := List Gate × ℕ

/-- All gates are acyclic and the output wire exists. Inputs themselves may
be outputs, so a circuit with no gates is permitted. -/
def Valid (inputs : ℕ) (circuit : Network) : Prop :=
  WellFormed inputs circuit.1 ∧ circuit.2 < inputs + circuit.1.length

/-- Input assignments have their ordinary finite mathematical carrier.
Values outside the input range start false; valid circuits cannot read them
until a gate has defined them. -/
def evaluate (inputs : ℕ) (circuit : Network) (assignment : Fin inputs → Bool) : Bool :=
  run inputs circuit.1 (fun wire => if bound : wire < inputs then assignment ⟨wire, bound⟩
    else false) circuit.2

/-- An accepting assignment sets the selected output wire to true. -/
def Satisfiable (inputs : ℕ) (circuit : Network) : Prop :=
  ∃ assignment : Fin inputs → Bool, evaluate inputs circuit assignment = true

theorem run_append (first second : List Gate) (start : ℕ) (values : ℕ → Bool) :
    run start (first ++ second) values =
      run (start + first.length) second (run start first values) := by
  induction first generalizing start values with
  | nil => simp [run]
  | cons gate rest induction =>
    simpa [run, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      induction (start + 1) (Function.update values start (gate.eval values))

theorem wellFormed_append (first second : List Gate) (start : ℕ) :
    WellFormed start (first ++ second) ↔
      WellFormed start first ∧ WellFormed (start + first.length) second := by
  induction first generalizing start with
  | nil => simp [WellFormed]
  | cons gate rest induction =>
    simp [WellFormed, induction, and_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Gate execution never changes inputs or previously computed wires. -/
theorem run_preserves (gates : List Gate) (start : ℕ) (values : ℕ → Bool)
    (wire : ℕ) (earlier : wire < start) : run start gates values wire = values wire := by
  induction gates generalizing start values with
  | nil => rfl
  | cons gate rest induction =>
    rw [run, induction (start + 1) _ (by omega)]
    exact Function.update_of_ne (by omega) _ _

end Polytime2.Circuit
