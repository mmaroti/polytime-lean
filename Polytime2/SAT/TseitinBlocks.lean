import Polytime2.SAT.TseitinGate
import Polytime2.Circuit.WireArithmetic
import Polytime2.Arrays.Tabulate
import Polytime2.Arrays.Operations
import Polytime2.Arrays.FlattenRecords

/-! # Uniform tabulation of Tseitin gate blocks

The mathematical sizes are the circuit input count and gate count. Each gate
is read from the canonical array, and its output is the next numbered wire.
No acyclicity check is required for emission; semantic equivalence separately
requires the mathematical circuit validity hypothesis.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.SAT

open EncodedDomain Polytime2.Computation Circuit
open Polytime2.Computation.Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

/-- Emit one three-clause record for every gate, in execution order. -/
noncomputable def tseitinBlocks (inputs count : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  arrayTabulate (fun _ => (gateDomain (inputs + count)).arrayOfLength count)
    (record 3 (fun _ => clauseDomain (inputs + count))) count
    (fun sizes arguments position => boundedGateClauses
      ((gateOutputWire inputs count).compute sizes ⟨(fun _ => position), trivial⟩) (arguments () position))

theorem tseitinBlocks_realizable (inputs count : MvPolynomial Parameter ℕ) : (tseitinBlocks inputs count).Realizable := by
  apply arrayTabulate_realizable
  let context : Unit ⊕ Unit → EncodedDomain Parameter :=
    Sum.elim (fun _ => (gateDomain (inputs + count)).arrayOfLength count) (fun _ => arrayPosition count)
  have lookup := (arrayLookupWithIndex_realizable (gateDomain (inputs + count)) (arrayPosition count)
    (fun _ position => position.val) (arrayPosition_value count) count).onArguments context (fun _ _ => True)
      (fun name => if name then .inl () else .inr ()) (by intro name; cases name <;> rfl) (by
        intro sizes arguments
        exact (arguments.val (.inr ())).isLt)
  have gateReady := lookup.withSpecification (fun _ _ => True)
    (fun _ arguments => arguments.val (.inl ()) (arguments.val (.inr ()))) (by intros; trivial) (by intros; rfl)
  have output := (gateOutputWire_realizable inputs count).onArguments context (fun _ _ => True)
    (fun _ => .inr ()) (by intros; rfl) (by intros; trivial)
  have emitted := (gateClauseBlock_realizable (inputs + count)).onResults context (fun _ _ => True)
    (fun name sizes arguments => match name with
      | false => arguments.val (.inl ()) (arguments.val (.inr ()))
      | true => (gateOutputWire inputs count).compute sizes ⟨(fun _ => arguments.val (.inr ())), trivial⟩)
    (by intros; trivial) (by
      intro name
      cases name
      · exact gateReady
      · exact output)
  exact emitted.withSpecification (fun _ _ => True) _ (by intros; trivial)
    (by intros; simp only [gateClauseBlock, specification_compute, onResults])

/-- Flatten gate blocks to the canonical array of all three-literal clauses. -/
noncomputable def tseitinGateProgram (inputs count : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  (tseitinBlocks inputs count).followedBy
    (arrayFlattenRecords (clauseDomain (inputs + count)) 3 count) rfl (by intros; trivial)

theorem tseitinGateProgram_realizable (inputs count : MvPolynomial Parameter ℕ) :
    (tseitinGateProgram inputs count).Realizable :=
  (tseitinBlocks_realizable inputs count).followedBy
    (arrayFlattenRecords_realizable (clauseDomain (inputs + count)) 3 count) rfl (by intros; trivial)

/-- The entire clause array is exactly the mathematical gate formula. -/
theorem tseitinGateProgram_value (inputs count : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (tseitinGateProgram inputs count).Arguments sizes // True}) :
    List.ofFn (fun index => clauseValue ((tseitinGateProgram inputs count).compute sizes arguments index)) =
      programFormula (MvPolynomial.eval sizes inputs) (List.ofFn (fun index => gateValue (arguments.val () index))) := by
  simp only [tseitinGateProgram, followedBy]
  rw [List.ofFn_comp' _ clauseValue, arrayFlattenRecords_list]
  simp only [List.map_flatten, List.map_ofFn, Function.comp_def, tseitinBlocks, arrayTabulate]
  rw [programFormula_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext position
  have correct := boundedGateClauses_value
    ((gateOutputWire inputs count).compute sizes ⟨(fun _ => position), trivial⟩) (arguments.val () position)
  exact congrArg List.ofFn correct

end Polytime2.SAT
