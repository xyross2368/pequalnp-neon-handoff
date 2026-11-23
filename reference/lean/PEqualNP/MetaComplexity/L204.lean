import Mathlib
import PEqualNP.MetaComplexity.Helpers.EdgeFnFinal

/-- The class form of the lower bound for the edge function with extra OR-variables, against
circuits over AND, OR and NOT with every gate counted. -/
theorem PEqualNP.MetaComplexity.L204 : ∀ (n k s : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)), (∀ (v : Fin n) (c : G.Walk v v), c.IsCycle → 7 ≤ c.length) → (∀ u v : Fin n, u ≠ v → 3 ≤ (G.neighborSet u).ncard → 3 ≤ (G.neighborSet v).ncard → ∀ p : G.Walk u v, 7 ≤ p.length) → (∀ i j : Fin n, G.Adj i j → i ∉ A) → (A.Nonempty ∨ ∃ i j : Fin n, G.Adj i j) → (∀ T : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → k ≤ T.card) → PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => @decide ((∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) (Classical.propDecidable _)) s → A.card + G.edgeSet.ncard + k ≤ s + 1 :=
  PEqualNP.MetaComplexity.EdgeFn.stmtLB_final
