import Polytime2.Encoding.EncodedArray
import Polytime2.Encoding.BinaryEncoding
import Mathlib.Combinatorics.SimpleGraph.Basic

/-! # Dense canonical encodings of ordinary finite simple graphs

The mathematical carrier is Mathlib's `SimpleGraph`. Storage is its Boolean
adjacency matrix. Decoding rejects loops and asymmetric matrices.
-/

namespace Polytime2.EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Exactly the Boolean matrices representing simple undirected graphs. -/
def IsSimpleAdjacency {size : ℕ} (table : Fin size → Fin size → Bool) : Prop :=
  (∀ vertex, table vertex vertex = false) ∧ ∀ first second, table first second = table second first

/-- Interpret an admissible adjacency matrix as an ordinary simple graph. -/
def graphOfAdjacency {size : ℕ} (table : {table : Fin size → Fin size → Bool // IsSimpleAdjacency table}) :
    SimpleGraph (Fin size) where
  Adj first second := table.val first second = true
  symm := ⟨by intro first second adjacent; rw [← table.property.2 first second]; exact adjacent⟩
  loopless := ⟨by intro vertex adjacent; simp only [table.property.1 vertex, Bool.false_eq_true] at adjacent⟩

/-- A simple graph and its exact adjacency matrix determine one another. -/
noncomputable def simpleGraphEquiv (size : ℕ) :
    SimpleGraph (Fin size) ≃ {table : Fin size → Fin size → Bool // IsSimpleAdjacency table} := by
  classical
  exact {
    toFun := fun graph => ⟨fun first second => decide (graph.Adj first second), by
      constructor
      · intro vertex; simp
      · intro first second; simp only [graph.adj_comm]⟩
    invFun := graphOfAdjacency
    left_inv := by intro graph; ext first second; simp [graphOfAdjacency]
    right_inv := by
      intro table
      apply Subtype.ext
      funext first second
      cases value : table.val first second <;> simp [graphOfAdjacency, value] }

/-- Dense canonical graph storage, with its admissibility internal to decoding. -/
noncomputable def simpleGraphs (vertices : MvPolynomial Parameter ℕ) : EncodedDomain Parameter := by
  classical
  exact (((booleans.arrayOfLength vertices).arrayOfLength vertices).restrict
    (fun _ table => IsSimpleAdjacency table)).reindex
      (fun sizes => SimpleGraph (Fin (MvPolynomial.eval sizes vertices)))
      (fun sizes => simpleGraphEquiv (MvPolynomial.eval sizes vertices))

/-- Dense canonical storage uses exactly one bit per ordered vertex pair. -/
theorem simpleGraphs_width (vertices : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ) :
    (simpleGraphs vertices).width sizes = (MvPolynomial.eval sizes vertices) ^ 2 := by
  change ((booleans.arrayOfLength vertices).arrayOfLength vertices).width sizes = _
  simp [pow_two, booleans, width, fixed, ofCodec, show Nat.clog 2 2 = 1 by decide]

end Polytime2.EncodedDomain
