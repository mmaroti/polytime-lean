import Polytime2.CSP.InstanceWordCheck
import Polytime2.CSP.PrepareCount
import Polytime2.Computation.RetainBoolean

/-! # Checking an instance/witness word pair at its prepared count

The input consists of two exact stored fields. The variable count is read
from the instance header; the checker runs at that actual count with a bound
provided by the host capacity. No variable count is supplied by the caller.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.CSP

open EncodedDomain Polytime2.Computation Complexity

variable (L : FirstOrder.Language.{0, 0}) [L.IsRelational] [Fintype (RelationSymbol L)]
variable (Carrier : Type) [Fintype Carrier] [L.Structure Carrier]

private noncomputable def wordField : EncodedDomain Unit :=
  boundedArray letterDomain (MvPolynomial.X ())

private noncomputable def wordPair : EncodedDomain Unit := wordField.prod wordField

private noncomputable def pairedChecker : Computation Bool Unit :=
  (instanceWordChecker L Carrier).onResults
    (fun _ => wordPair.renameParameters (fun _ : Unit => false)) (fun _ _ => True)
    (fun choice _ arguments => match choice with | false => (arguments.val ()).1 | true => (arguments.val ()).2)
    (by intros; trivial)

private theorem pairedChecker_realizable : (pairedChecker L Carrier).Realizable := by
  apply (instanceWordChecker_realizable L Carrier).onResults
    (fun _ => wordPair.renameParameters (fun _ : Unit => false)) (fun _ _ => True)
    (fun choice _ arguments => match choice with | false => (arguments.val ()).1 | true => (arguments.val ()).2)
    (by intros; trivial)
  intro choice
  cases choice
  · exact (pairProjection_realizable wordField wordField false).renameParameters (fun _ : Unit => false)
  · exact (pairProjection_realizable wordField wordField true).renameParameters (fun _ : Unit => false)

private def sizeNames : Bool → Unit ⊕ Unit
  | false => .inl ()
  | true => .inr ()

private noncomputable def checkerCallee : Computation (Unit ⊕ Unit) Unit :=
  ((pairedChecker L Carrier).renameParameters sizeNames).reinterpretInputs
    (fun _ => wordPair.renameParameters Sum.inl) (fun _ _ value => value)
    (fun _ _ => True) (by intros; trivial) |>.reinterpretOutput booleans (fun _ value => value)

private theorem checkerCallee_realizable : (checkerCallee L Carrier).Realizable := by
  have prepared := ((pairedChecker_realizable L Carrier).renameParameters sizeNames).reinterpretInputs
    (fun _ : Unit => wordPair.renameParameters Sum.inl) (fun _ _ value => value)
    (by
      intro name sizes
      change (wordPair.renameParameters Sum.inl).width sizes =
        ((wordPair.renameParameters (fun _ : Unit => false)).renameParameters sizeNames).width sizes
      simp only [renameParameters_comp]; rfl)
    (by
      intro name sizes value
      exact (renameParameters_comp_bits wordPair (fun _ : Unit => false) sizeNames sizes value).symm)
    (fun _ _ => True) (by intros; trivial)
  apply prepared.reinterpretOutput booleans (fun _ value => value)
  · intro sizes
    change (booleans : EncodedDomain (Unit ⊕ Unit)).width sizes =
      ((booleans : EncodedDomain Bool).renameParameters sizeNames).width sizes
    simp only [booleans, fixed_renameParameters]
  · intro sizes value
    change ArrayEncoding.bits (booleans.encode sizes value) =
      ArrayEncoding.bits (((booleans : EncodedDomain Bool).renameParameters sizeNames).encode sizes value)
    simp only [renameParameters_bits, booleans, fixed_encode_bits]

private theorem checkerCallee_correct (sizes : (Unit ⊕ Unit) → ℕ)
    (pair : (wordPair.renameParameters Sum.inl).Carrier sizes) :
    (checkerCallee L Carrier).compute sizes ⟨(fun _ => pair), trivial⟩ =
      (readPairHeader (List.ofFn pair.1.2)).elim false
        (fun parsed => tableWordVerifier L Carrier (sizes (.inr ())) parsed.2 (List.ofFn pair.2.2)) :=
  instanceWordChecker_correct L Carrier (sizes ∘ sizeNames)
    (fun choice => match choice with | false => pair.1 | true => pair.2)

/-- Check the two stored words using the variable count prepared from the
instance field. Header and code failures return false. -/
noncomputable def pairWordChecker : Computation Unit Unit :=
  (prepareFieldCount.followedBy
    ((checkerCallee L Carrier).atComputedUnarySizes (extendedSizeBounds (fun _ : Unit => MvPolynomial.X ())))
    rfl (by intros; trivial)).followedBy
      (retainComputedBoolean (extendedSizeBounds (fun _ : Unit => MvPolynomial.X ()))) rfl (by intros; trivial)

theorem pairWordChecker_realizable : (pairWordChecker L Carrier).Realizable :=
  (prepareFieldCount_realizable.followedBy
    ((checkerCallee_realizable L Carrier).atComputedUnarySizes
      (extendedSizeBounds (fun _ : Unit => MvPolynomial.X ())))
    rfl (by intros; trivial)).followedBy
      (retainComputedBoolean_realizable (extendedSizeBounds (fun _ : Unit => MvPolynomial.X ()))) rfl (by intros; trivial)

/-- The prepared count agrees with every valid header, so the complete stored
word-pair check has exactly the mathematical verifier's answer. -/
theorem pairWordChecker_correct (sizes : Unit → ℕ)
    (pair : (wordPair).Carrier sizes) :
    (pairWordChecker L Carrier).compute sizes ⟨(fun _ => pair), trivial⟩ =
      wordVerifier L Carrier (encodePair (List.ofFn pair.1.2, List.ofFn pair.2.2)) := by
  let frame := prepareFieldCount.compute sizes ⟨(fun _ => pair), trivial⟩
  let bounds := extendedSizeBounds (fun _ : Unit => (MvPolynomial.X () : MvPolynomial Unit ℕ))
  let actual := computedSizeAssignment bounds sizes frame.1
  have checked := checkerCallee_correct L Carrier actual frame.2
  change (checkerCallee L Carrier).compute actual ⟨(fun _ => frame.2), trivial⟩ = _
  rw [checked]
  change (readPairHeader (List.ofFn pair.1.2)).elim false
    (fun parsed => tableWordVerifier L Carrier (actual (.inr ())) parsed.2 (List.ofFn pair.2.2)) = _
  simp only [wordVerifier, decodePair_encodePair]
  cases header : readPairHeader (List.ofFn pair.1.2) with
  | none => rfl
  | some parsed =>
    rcases parsed with ⟨count, tables⟩
    have sameCount : actual (.inr ()) = count := prepareFieldCount_parsed sizes pair count tables header
    simp only [Option.elim_some]
    rw [sameCount]

end Polytime2.CSP
