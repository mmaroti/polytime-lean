import Polytime2.CSP.Checker
import Polytime2.Arrays.ZipWith
import Polytime2.Arrays.AllTrue
import Polytime2.Primitives.FiniteOperations
import Polytime2.Computation.Constant

/-! # Realization of recursive fixed-relation checking

The recursive routine checks one relation using finite predicate sections,
named array zip, and conjunction. The variable count is the only runtime size;
arity and carrier are fixed before specialization. All machine composition is
delegated to existing mathematical computation rules.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.CSP.Internal

open _root_.Polytime2.Computation EncodedDomain

variable (Carrier : Type) [Fintype Carrier]

private noncomputable def valueCodec : EncodedDomain Empty := fixed (Fintype.equivFin Carrier)

private noncomputable def predicateCodec (arity : ℕ) : EncodedDomain Empty := by
  classical
  exact fixed (Fintype.equivFin ((Fin arity → Carrier) → Bool))

private noncomputable def relationInputs (arity : ℕ) : Option Bool → EncodedDomain Unit
  | none => (predicateCodec Carrier arity).constant
  | some false => assignmentDomain Carrier
  | some true => scopeDomain arity

private noncomputable def relationComputation (arity : ℕ) : Computation Unit (Option Bool) where
  inputDomains := relationInputs Carrier arity
  outputDomain := booleans
  precondition _ _ := True
  compute sizes arguments := relationCheckValue Carrier (sizes ()) arity
    (arguments.val none) (arguments.val (some false)) (arguments.val (some true))

private theorem nullaryTable_realizable :
    (unaryMap (scopeDomain 0) (booleans : EncodedDomain Unit) (fun _ _ => True)
      (fun _ table => table.val Fin.elim0)).Realizable := by
  have prepared := (copy_realizable (booleans : EncodedDomain Unit)).reinterpretInputs
    (fun _ : Unit => scopeDomain 0) (fun _ _ table => table Fin.elim0)
    (by intros; rfl) (by intros; rfl) (fun _ _ => True) (by intros; trivial)
  exact prepared

private theorem splitTable_realizable (arity : ℕ) :
    (unaryMap (scopeDomain (arity + 1)) ((scopeDomain arity).array ()) (fun _ _ => True)
      (fun sizes table => scopeSplit (sizes ()) arity table.val)).Realizable := by
  exact (copy_realizable ((scopeDomain arity).array ())).reinterpretInputs
    (fun _ : Unit => scopeDomain (arity + 1))
    (fun _ sizes table => scopeSplit (sizes ()) arity table)
    (by intros; rfl) (by intro name sizes table; exact scopeDomain_succ_bits arity sizes table)
    (fun _ _ => True) (by intros; trivial)

private theorem relationComputation_realizable (arity : ℕ) :
    (relationComputation Carrier arity).Realizable := by
  classical
  induction arity with
  | zero =>
    let inputs := relationInputs Carrier 0
    have predicate := (finitePredicate_realizable (predicateCodec Carrier 0)
      (fun relation => relation Fin.elim0)).onArguments inputs (fun _ _ => True)
      (fun _ => none) (by intros; rfl) (by intros; trivial)
    have enabled := nullaryTable_realizable.onArguments inputs (fun _ _ => True) (fun _ => some true)
      (by intros; rfl) (by intros; trivial)
    have complete := (booleanOperation_realizable (fun flags : Bool → Bool => !flags true || flags false)).onResults
      inputs (fun _ _ => True) (fun flag _ arguments => if flag then arguments.val (some true) Fin.elim0
        else arguments.val none Fin.elim0) (by intros; trivial)
      (by intro flag; cases flag; exact predicate; exact enabled)
    exact complete.withSpecification (fun _ _ => True) (relationComputation Carrier 0).compute
      (by intros; trivial) (by intros; rfl)
  | succ arity hypothesis =>
    let context : Bool → EncodedDomain Unit := fun choice =>
      if choice then assignmentDomain Carrier else (predicateCodec Carrier (arity + 1)).constant
    let operation sizes (arguments : ∀ name, (context name).Carrier sizes)
        (value : Carrier) (table : (Fin arity → Fin (sizes ())) → Bool) :=
      relationCheckValue Carrier (sizes ()) arity
        (fun rest => arguments false (Fin.cons value rest)) (arguments true) table
    let step := arrayZipWithStep context (valueCodec Carrier).constant (scopeDomain arity) booleans operation
    have sectionReady := (finiteTable_realizable (predicateCodec Carrier (arity + 1))
      (valueCodec Carrier) (predicateCodec Carrier arity)
      (fun predicate value rest => predicate (Fin.cons value rest))).withConstantSizes (Parameter := Unit)
    have sectionOnStep := sectionReady.onArguments step.inputDomains (fun _ _ => True)
      (fun name => if name then .inr false else .inl false)
      (by intro name; cases name <;> rfl) (by intros; trivial)
    let results (name : Option Bool) (sizes : Unit → ℕ)
        (arguments : {arguments : step.Arguments sizes // True}) :
        ((relationComputation Carrier arity).inputDomains name).Carrier sizes := by
      cases name with
      | none => exact fun rest => arguments.val (.inl false) (Fin.cons (arguments.val (.inr false)) rest)
      | some choice =>
        cases choice
        · exact arguments.val (.inl true)
        · exact arguments.val (.inr true)
    have stepReady : step.Realizable := by
      have assembled := hypothesis.onResults step.inputDomains (fun _ _ => True) results
        (by intros; trivial) (by
          intro name
          cases name with
          | none => exact sectionOnStep
          | some choice =>
            cases choice
            · exact Realizable.argument step.inputDomains (.inl true) (fun _ _ => True)
            · exact Realizable.argument step.inputDomains (.inr true) (fun _ _ => True))
      exact assembled.withSpecification step.precondition step.compute (by intros; trivial) (by intros; rfl)
    have zipped := arrayZipWithAtParameter_realizable context (valueCodec Carrier).constant
      (scopeDomain arity) booleans () operation stepReady
    have all := zipped.followedBy (arrayAllTrueAtParameter_realizable ()) rfl (by intros; trivial)
    let inputs := relationInputs Carrier (arity + 1)
    let producers (name : Bool ⊕ Bool) (sizes : Unit → ℕ)
        (arguments : {arguments : (∀ name, (inputs name).Carrier sizes) // True}) :
        ((arrayZipWithAtParameter context (valueCodec Carrier).constant (scopeDomain arity) booleans () operation).inputDomains name).Carrier sizes := by
      rcases name with name | name
      · cases name
        · exact arguments.val none
        · exact arguments.val (some false)
      · cases name
        · exact arguments.val (some false)
        · exact scopeSplit (sizes ()) arity (arguments.val (some true))
    have complete := all.onResults inputs (fun _ _ => True) producers (by intros; trivial) (by
      intro name
      rcases name with name | name
      · cases name
        · exact Realizable.argument inputs none (fun _ _ => True)
        · exact Realizable.argument inputs (some false) (fun _ _ => True)
      · cases name
        · exact Realizable.argument inputs (some false) (fun _ _ => True)
        · exact (splitTable_realizable arity).onArguments inputs (fun _ _ => True)
            (fun _ => some true) (by intros; rfl) (by intros; trivial))
    apply complete.withSpecification (fun _ _ => True) (relationComputation Carrier (arity + 1)).compute
      (by intros; trivial)
    intro sizes arguments valid
    apply Bool.eq_iff_iff.mpr
    change (arrayAllTrueAtParameter ()).compute sizes
      ⟨(fun _ first => relationCheckValue Carrier (sizes ()) arity
        (fun rest => arguments none (Fin.cons (arguments (some false) first) rest))
        (arguments (some false)) (fun rest => arguments (some true) (Fin.cons first rest))), trivial⟩ = true ↔ _
    rw [arrayAllTrueAtParameter_correct]
    simp [relationComputation, relationCheckValue, List.all_eq_true]

end Polytime2.CSP.Internal

namespace Polytime2.CSP

open FirstOrder FirstOrder.Language EncodedDomain _root_.Polytime2.Computation

variable (L : Language.{0, 0}) [L.IsRelational] [Fintype (RelationSymbol L)]
variable (Carrier : Type) [Fintype Carrier] [L.Structure Carrier]

/-- Check all fixed template relations using their certified fixed-arity
checkers. All Boolean-table extraction and assignment traversal is composed
through the public computation rules. -/
theorem assignmentChecker_realizable : (assignmentChecker L Carrier).Realizable := by
  classical
  let inputs := checkerInputs L Carrier
  let results (symbol : RelationSymbol L) (sizes : Unit → ℕ)
      (arguments : {arguments : (∀ name, (inputs name).Carrier sizes) // True}) : Bool :=
    Internal.relationCheckValue Carrier (sizes ()) symbol.1
      (fun tuple => decide (Structure.RelMap symbol.2 tuple))
      (arguments.val true) ((instanceTablesEquiv L (sizes ())) (arguments.val false) symbol)
  have each (symbol : RelationSymbol L) :
      (Computation.mk inputs booleans (fun _ _ => True) (results symbol)).Realizable := by
    let relation : (Fin symbol.1 → Carrier) → Bool := fun tuple => decide (Structure.RelMap symbol.2 tuple)
    have constant := (finiteOperation_realizable (fun empty : Empty => empty.elim)
      (Internal.predicateCodec Carrier symbol.1) (fun _ => relation)).withConstantSizes (Parameter := Unit)
    have constantOnInputs := constant.onResults inputs (fun _ _ => True) (fun empty => empty.elim)
      (by intros; trivial) (fun empty => empty.elim)
    have project := (Realizable.argument (fun index : RelationSymbol L => scopeDomain index.1)
      symbol (fun _ _ => True)).withRecordArgument
    have projected := project.reinterpretInputs (fun _ : Unit => instanceDomain L)
      (fun _ sizes input => instanceTablesEquiv L (sizes ()) input)
      (by intros; rfl) (by intros; rfl) (fun _ _ => True) (by intros; trivial)
    have tableOnInputs := projected.onArguments inputs (fun _ _ => True) (fun _ => false)
      (by intros; rfl) (by intros; trivial)
    let producers (name : Option Bool) (sizes : Unit → ℕ)
        (arguments : {arguments : (∀ name, (inputs name).Carrier sizes) // True}) :
        ((Internal.relationComputation Carrier symbol.1).inputDomains name).Carrier sizes := by
      cases name with
      | none => exact relation
      | some choice =>
        cases choice
        · exact arguments.val true
        · exact instanceTablesEquiv L (sizes ()) (arguments.val false) symbol
    have assembled := (Internal.relationComputation_realizable Carrier symbol.1).onResults
      inputs (fun _ _ => True) producers (by intros; trivial) (by
        intro name
        cases name with
        | none => exact constantOnInputs
        | some choice =>
          cases choice
          · exact Realizable.argument inputs true (fun _ _ => True)
          · exact tableOnInputs)
    exact assembled.withSpecification (fun _ _ => True) (results symbol)
      (by intros; trivial) (by intros; rfl)
  have combined := (booleanOperation_realizable (Parameter := Unit)
    (fun flags : RelationSymbol L → Bool => decide (∀ symbol, flags symbol = true))).onResults
      inputs (fun _ _ => True) results (by intros; trivial) each
  apply combined.decision (fun sizes arguments => Preserves L Carrier (sizes ()) (arguments false) (arguments true))
  intro sizes arguments valid
  change decide (∀ symbol, results symbol sizes ⟨arguments, trivial⟩ = true) = true ↔ _
  rw [decide_eq_true_eq]
  simp only [results, Internal.relationCheckValue_correct]
  change (∀ symbol : RelationSymbol L, ∀ tuple,
    decide ((arguments false).RelMap symbol.2 tuple) = true →
      decide (@Structure.RelMap L Carrier _ symbol.1 symbol.2 ((arguments true) ∘ tuple)) = true) ↔ _
  simp only [decide_eq_true_eq]
  rfl

end Polytime2.CSP
