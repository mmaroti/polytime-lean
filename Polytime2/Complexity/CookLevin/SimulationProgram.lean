import Polytime2.Complexity.CookLevin.CellProgram
import Polytime2.Arrays.Tabulate

/-! # Uniform tabulation of machine simulation gates

Fixed records collect the output bits of a cell. Polynomial array tabulations
collect cells and time steps. All coordinates come from the existing array
rules, including the empty array when the time allowance is zero.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity.CookLevin

open Turing Circuit EncodedDomain Polytime2.Computation

variable {Symbol State : Type} [Inhabited Symbol] [Inhabited State]
variable [Fintype Symbol] [Fintype State]

private noncomputable def cellPrograms (machine : TM0.Machine Symbol State) : Computation Unit Bool where
  inputDomains := blockBaseInputs
  outputDomain := record (cellWidth Symbol State)
    (fun _ => record (cellBlockSize Symbol State) (fun _ => gateDomain (layoutWires Symbol State)))
  precondition _ _ := True
  compute sizes arguments bit := (cellProgram machine bit).compute sizes arguments

private theorem cellPrograms_realizable (machine : TM0.Machine Symbol State) :
    (cellPrograms machine).Realizable := by
  apply Realizable.recordOutputs
  intro bit
  exact cellProgram_realizable machine bit

private noncomputable def layerPrograms (machine : TM0.Machine Symbol State) : Computation Unit Unit :=
  arrayTabulate (fun _ => arrayPosition (MvPolynomial.X ())) (cellPrograms machine).outputDomain layoutPositions
    (fun sizes arguments cell => (cellPrograms machine).compute sizes
      ⟨(fun name => match name with | false => arguments () | true => cell), trivial⟩)

private theorem layerPrograms_realizable (machine : TM0.Machine Symbol State) :
    (layerPrograms machine).Realizable := by
  unfold layerPrograms
  apply arrayTabulate_realizable
  let inputs : Unit ⊕ Unit → EncodedDomain Unit :=
    Sum.elim (fun _ => arrayPosition (MvPolynomial.X ())) (fun _ => arrayPosition layoutPositions)
  have prepared := (cellPrograms_realizable machine).onArguments inputs (fun _ _ => True)
    (fun name => match name with | false => Sum.inl () | true => Sum.inr ())
    (by intro name; cases name <;> rfl) (by intros; trivial)
  apply prepared.withSpecification (fun _ _ => True) _ (by intros; trivial)
  intro sizes arguments allowed
  apply congrArg ((cellPrograms machine).compute sizes)
  apply Subtype.ext
  funext name
  cases name <;> rfl

/-- Construct the simulation gates, indexed by time, cell, bit, and template
slot, using the canonical nested array and record codecs. -/
noncomputable def simulationProgram (machine : TM0.Machine Symbol State) : Computation Unit Empty :=
  arrayTabulate (fun empty => nomatch empty) (layerPrograms machine).outputDomain (MvPolynomial.X ())
    (fun sizes _ time => (layerPrograms machine).compute sizes ⟨(fun _ => time), trivial⟩)

theorem simulationProgram_realizable (machine : TM0.Machine Symbol State) :
    (simulationProgram machine).Realizable := by
  unfold simulationProgram
  apply arrayTabulate_realizable
  let inputs : Empty ⊕ Unit → EncodedDomain Unit :=
    Sum.elim (fun empty => nomatch empty) (fun _ => arrayPosition (MvPolynomial.X ()))
  have prepared := (layerPrograms_realizable machine).onArguments inputs (fun _ _ => True)
    (fun _ => Sum.inr ()) (by intros; rfl) (by intros; trivial)
  exact prepared.withSpecification (fun _ _ => True) _ (by intros; trivial) (by intros; rfl)

/-- Every tabulated block is the certified local constructor at exactly its
mathematical time, cell, and bit coordinates. -/
theorem simulationProgram_block (machine : TM0.Machine Symbol State) (sizes : Unit → ℕ)
    (arguments : (simulationProgram machine).Arguments sizes)
    (time : Fin (MvPolynomial.eval sizes (MvPolynomial.X ())))
    (cell : Fin (MvPolynomial.eval sizes layoutPositions)) (bit : Fin (cellWidth Symbol State)) :
    (simulationProgram machine).compute sizes ⟨arguments, trivial⟩ time cell bit =
      (cellProgram machine bit).compute sizes
        ⟨(fun name => match name with | false => time | true => cell), trivial⟩ := rfl

end Polytime2.Complexity.CookLevin
