import Polytime2.CSP.InstanceProgram
import Polytime2.CSP.RelationMaterialize

/-! # Certified insertion of a finite family of relational facts

Each fixed relation symbol has its own array of optional scopes. Materialize
its dense table and assemble the canonical instance. Fact order, duplicates,
and absent entries have no mathematical effect on the resulting relations.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.CSP

open EncodedDomain Polytime2.Computation

variable (L : FirstOrder.Language.{0, 0}) [L.IsRelational] [Fintype (RelationSymbol L)]
variable {Parameter : Type} [Fintype Parameter]

/-- The ordinary dependent family of optional relation-scope arrays. -/
noncomputable def instanceFactsDomain (vertices : MvPolynomial Parameter ℕ)
    (facts : RelationSymbol L → MvPolynomial Parameter ℕ) : EncodedDomain Parameter :=
  namedRecord (fun symbol => (relationFactDomain vertices symbol.1).arrayOfLength (facts symbol))

/-- Insert precisely the asserted facts into the canonical dense instance. -/
noncomputable def materializeInstance (vertices : MvPolynomial Parameter ℕ)
    (facts : RelationSymbol L → MvPolynomial Parameter ℕ) : Computation Parameter Unit := by
  classical
  exact instanceTabulate L (fun _ : Unit => instanceFactsDomain L vertices facts) vertices
    (fun _ arguments symbol tuple => decide (∃ index, arguments () symbol index = some tuple))

theorem materializeInstance_realizable (vertices : MvPolynomial Parameter ℕ)
    (facts : RelationSymbol L → MvPolynomial Parameter ℕ) :
    (materializeInstance L vertices facts).Realizable := by
  classical
  apply instanceTabulate_of_tables_realizable
  intro symbol
  have projected := namedRecordProjection_realizable
    (fun index : RelationSymbol L => (relationFactDomain vertices index.1).arrayOfLength (facts index)) symbol
  have inserted := projected.followedBy (materializeRelation_realizable vertices (facts symbol) symbol.1)
    rfl (by intros; trivial)
  exact inserted.withSpecification (fun _ _ => True) _ (by intros; trivial) (by intros; rfl)

/-- The output structure asserts a relation exactly when some input entry is
that scope. No validity condition on the fact family is needed. -/
theorem materializeInstance_correct (vertices : MvPolynomial Parameter ℕ)
    (facts : RelationSymbol L → MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (input : (instanceFactsDomain L vertices facts).Carrier sizes)
    {arity : ℕ} (symbol : L.Relations arity)
    (tuple : Fin arity → Fin (MvPolynomial.eval sizes vertices)) :
    ((materializeInstance L vertices facts).compute sizes ⟨fun _ => input, trivial⟩).RelMap symbol tuple ↔
      ∃ index, input ⟨arity, symbol⟩ index = some tuple := by
  classical
  change decide (∃ index, input ⟨arity, symbol⟩ index = some tuple) = true ↔ _
  simp only [decide_eq_true_eq]

end Polytime2.CSP
