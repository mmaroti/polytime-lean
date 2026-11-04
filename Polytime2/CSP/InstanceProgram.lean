import Polytime2.CSP.ScopeProgram
import Polytime2.Computation.Dependent

/-! # Dense relational instances from certified scope queries

Specialization-fixed relation symbols select their scope query. All fields
reuse the canonical scope and named-record codecs; assembly introduces no
alternate table ordering, extra tags, or padding.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.CSP

open EncodedDomain Polytime2.Computation

variable (L : FirstOrder.Language.{0, 0}) [L.IsRelational] [Fintype (RelationSymbol L)]
variable {Parameter Context : Type} [Fintype Parameter] [Fintype Context]

/-- Read one specialization-fixed relation from a canonical dense instance. -/
noncomputable def instanceRelation (vertices : MvPolynomial Parameter ℕ)
    (symbol : RelationSymbol L) : Computation Parameter Unit :=
  unaryMap ((instanceDomain L).substitute (fun _ => vertices))
    ((scopeDomain symbol.1).substitute (fun _ => vertices))
    (fun _ _ => True)
    (fun sizes input => instanceTablesEquiv L (MvPolynomial.eval sizes vertices) input.val symbol)

theorem instanceRelation_realizable (vertices : MvPolynomial Parameter ℕ)
    (symbol : RelationSymbol L) : (instanceRelation L vertices symbol).Realizable := by
  let fields := fun index : RelationSymbol L => (scopeDomain index.1).substitute (fun _ => vertices)
  have project := (Realizable.argument fields symbol (fun _ _ => True)).withRecordArgument
  have converted := project.reinterpretInputs
    (fun _ : Unit => (instanceDomain L).substitute (fun _ => vertices))
    (fun _ sizes input => instanceTablesEquiv L (MvPolynomial.eval sizes vertices) input)
    (by
      intro name sizes
      have lengths := congrArg List.length
        (instanceDomain_substitute_bits L vertices sizes (fun _ _ => false))
      simpa only [ArrayEncoding.bits, List.length_ofFn, EncodedDomain.width,
        withRecordArgument, fields] using lengths)
    (by
      intro name sizes input
      simpa only [Equiv.symm_apply_apply, withRecordArgument, fields] using
        instanceDomain_substitute_bits L vertices sizes
          (instanceTablesEquiv L (MvPolynomial.eval sizes vertices) input))
    (fun _ _ => True) (by intros; trivial)
  exact converted.withSpecification (fun _ _ => True) (instanceRelation L vertices symbol).compute
    (by intros; trivial) (by intros; rfl)

/-- Build the actual mathematical structure whose relations are the supplied
Boolean queries, at the requested mathematical variable count. -/
noncomputable def instanceTabulate (context : Context → EncodedDomain Parameter)
    (vertices : MvPolynomial Parameter ℕ)
    (query : ∀ sizes, (∀ name, (context name).Carrier sizes) →
      (symbol : RelationSymbol L) → (Fin symbol.1 → Fin (MvPolynomial.eval sizes vertices)) → Bool) :
    Computation Parameter Context where
  inputDomains := context
  outputDomain := (instanceDomain L).substitute (fun _ => vertices)
  precondition _ _ := True
  compute sizes arguments := (instanceTablesEquiv L (MvPolynomial.eval sizes vertices)).symm
    (query sizes arguments.val)

theorem instanceTabulate_of_tables_realizable (context : Context → EncodedDomain Parameter)
    (vertices : MvPolynomial Parameter ℕ)
    (query : ∀ sizes, (∀ name, (context name).Carrier sizes) →
      (symbol : RelationSymbol L) → (Fin symbol.1 → Fin (MvPolynomial.eval sizes vertices)) → Bool)
    (ready : ∀ symbol : RelationSymbol L,
      (scopeTabulate context vertices symbol.1 (fun sizes arguments => query sizes arguments symbol)).Realizable) :
    (instanceTabulate L context vertices query).Realizable := by
  let fields := fun symbol : RelationSymbol L => (scopeDomain symbol.1).substitute (fun _ => vertices)
  let results (symbol : RelationSymbol L) sizes
      (arguments : {arguments : ∀ name, (context name).Carrier sizes // True}) := query sizes arguments.val symbol
  have fieldReady (symbol : RelationSymbol L) :
      (Computation.mk context (fields symbol) (fun _ _ => True) (results symbol)).Realizable :=
    ready symbol
  have packed := Realizable.namedRecordOutputs context fields (fun _ _ => True) results fieldReady
  have converted := packed.reinterpretOutput ((instanceDomain L).substitute (fun _ => vertices))
    (fun sizes tables => (instanceTablesEquiv L (MvPolynomial.eval sizes vertices)).symm tables)
    (by
      intro sizes
      have lengths := congrArg List.length (instanceDomain_substitute_bits L vertices sizes (fun _ _ => false))
      simpa only [ArrayEncoding.bits, List.length_ofFn, EncodedDomain.width] using lengths)
    (instanceDomain_substitute_bits L vertices)
  exact converted.withSpecification (fun _ _ => True) (instanceTabulate L context vertices query).compute
    (by intros; trivial) (by intros; rfl)

theorem instanceTabulate_realizable (context : Context → EncodedDomain Parameter)
    (vertices : MvPolynomial Parameter ℕ)
    (query : ∀ sizes, (∀ name, (context name).Carrier sizes) →
      (symbol : RelationSymbol L) → (Fin symbol.1 → Fin (MvPolynomial.eval sizes vertices)) → Bool)
    (ready : ∀ symbol : RelationSymbol L,
      (scopeQuery context vertices symbol.1 (fun sizes arguments => query sizes arguments symbol)).Realizable) :
    (instanceTabulate L context vertices query).Realizable :=
  instanceTabulate_of_tables_realizable L context vertices query
    (fun symbol => scopeTabulate_realizable context vertices symbol.1 _ (ready symbol))

end Polytime2.CSP
