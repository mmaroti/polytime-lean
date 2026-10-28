import Polytime2.Circuit.Compile

/-! # Circuits for fixed finite Boolean transition tables

Shannon expansion represents any Boolean function of finitely many bits using
NAND and constants. The gate bound is exponential only in the table's arity;
the machine simulation uses this for a fixed local transition table, not for
the whole input-dependent configuration. Uniform polynomial-time circuit
construction is not asserted by this mathematical representation theorem.
-/

namespace Polytime2.Circuit.Expression

/-- Select the true or false branch, using four NAND operations when the
selector is a wire. The branch expressions each occur once. -/
def select (selector yes no : Expression) : Expression :=
  .nand (.nand selector yes) (.nand (.nand selector selector) no)

theorem select_eval (selector yes no : Expression) (values : ℕ → Bool) :
    (select selector yes no).eval values =
      if selector.eval values then yes.eval values else no.eval values := by
  simp only [select, eval]
  cases selector.eval values <;> cases yes.eval values <;> cases no.eval values <;>
    rfl

theorem select_valid {selector yes no : Expression} {available : ℕ}
    (selectorValid : selector.Valid available) (yesValid : yes.Valid available)
    (noValid : no.Valid available) : (select selector yes no).Valid available :=
  ⟨⟨selectorValid, yesValid⟩, ⟨⟨selectorValid, selectorValid⟩, noValid⟩⟩

/-- The first argument is read from `offset`; recursive branches read the
remaining consecutive wires. Empty tables are constants. -/
def truthTable : (arity : ℕ) → ℕ → ((Fin arity → Bool) → Bool) → Expression
  | 0, _, table => .constant (table Fin.elim0)
  | arity + 1, offset, table =>
    select (.wire offset)
      (truthTable arity (offset + 1) (fun tail => table (Fin.cases true tail)))
      (truthTable arity (offset + 1) (fun tail => table (Fin.cases false tail)))

theorem truthTable_valid (arity offset available : ℕ)
    (table : (Fin arity → Bool) → Bool) (fits : offset + arity ≤ available) :
    (truthTable arity offset table).Valid available := by
  induction arity generalizing offset with
  | zero => trivial
  | succ arity induction =>
    apply select_valid
    · change offset < available
      omega
    · exact induction (offset + 1) _ (by omega)
    · exact induction (offset + 1) _ (by omega)

theorem truthTable_eval (arity offset : ℕ) (table : (Fin arity → Bool) → Bool)
    (values : ℕ → Bool) :
    (truthTable arity offset table).eval values =
      table (fun index => values (offset + index.val)) := by
  induction arity generalizing offset with
  | zero =>
    change table Fin.elim0 = _
    congr 1
    funext index
    exact Fin.elim0 index
  | succ arity induction =>
    simp only [truthTable, select_eval, eval, induction]
    have assignment (head : Bool) (equal : values offset = head) :
        Fin.cases head (fun index : Fin arity => values (offset + 1 + index.val)) =
          (fun index : Fin (arity + 1) => values (offset + index.val)) := by
      funext index
      refine Fin.cases ?_ (fun tail => ?_) index
      · simpa using equal.symm
      · simp [Nat.add_comm, Nat.add_left_comm]
    cases equal : values offset <;> simp [assignment _ equal]

/-- Each Shannon node adds four gates; constants contribute one. The arity
will be specialization-fixed in the machine simulation. -/
theorem truthTable_gateCount (arity offset : ℕ) (table : (Fin arity → Bool) → Bool) :
    (truthTable arity offset table).gateCount + 4 = 5 * 2 ^ arity := by
  induction arity generalizing offset with
  | zero => rfl
  | succ arity induction =>
    have yes := induction (offset + 1) (fun tail => table (Fin.cases true tail))
    have no := induction (offset + 1) (fun tail => table (Fin.cases false tail))
    simp only [truthTable, select, gateCount, Nat.pow_succ]
    omega

end Polytime2.Circuit.Expression
