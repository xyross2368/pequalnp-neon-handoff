import PEqualNP.Defs.MetaComplexityMinimal
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite
import PEqualNP.MetaComplexity.Helpers.ForestBound

/-- For a forest `G` on `n` vertices with at least one edge and vertex cover number at least
`k`, every fan-in two circuit for "some edge has both ends true" has at least `|E| + k - 1`
gates. -/
theorem PEqualNP.MetaComplexity.L104 : ∀ (n k s : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G.IsAcyclic → (∃ i j : Fin n, G.Adj i j) → (∀ T : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → k ≤ T.card) → PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) s → G.edgeFinset.card + k ≤ s + 1 :=
  PEqualNP.MetaComplexity.Helpers.Forest.forest_bound
