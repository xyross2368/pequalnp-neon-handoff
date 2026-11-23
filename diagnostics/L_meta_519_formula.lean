import PEqualNP.Outside.L_meta_531

namespace Meta519Formula

open PEqualNP.MetaComplexity

def PositiveLeaves {n : ℕ} (φ : DMFormula n) : Prop :=
  DMFormula.rec (motive := fun _ => Prop) (fun _ b => b = true)
    (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) φ

def binaryGates {n : ℕ} : DMFormula n → ℕ
  | .lit _ _ => 0
  | .and left right => binaryGates left + binaryGates right + 1
  | .or left right => binaryGates left + binaryGates right + 1

theorem leaves_eq_gates_add_one {n : ℕ} (φ : DMFormula n) :
    φ.leaves = binaryGates φ + 1 := by
  induction φ with
  | lit i b => rfl
  | and left right hl hr => simp only [DMFormula.leaves, binaryGates, hl, hr]; omega
  | or left right hl hr => simp only [DMFormula.leaves, binaryGates, hl, hr]; omega

private theorem triangleFree {n : ℕ} {G : SimpleGraph (Fin n)}
    (hgirth : ∀ v : Fin n, ∀ c : G.Walk v v, c.IsCycle → 7 ≤ c.length) :
    ∀ a b c : Fin n, ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c a) := by
  intro a b c h
  obtain ⟨hab, hbc, hca⟩ := h
  let w : G.Walk a a := .cons hab (.cons hbc (.cons hca .nil))
  have hcycle : w.IsCycle := by
    apply SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    refine ⟨?_, by simp [w]⟩
    simp [w, SimpleGraph.Walk.isPath_def, hbc.ne, hab.ne.symm, hca.ne]
  have hlong := hgirth a w hcycle
  simp [w] at hlong

private theorem squareFree {n : ℕ} {G : SimpleGraph (Fin n)}
    (hgirth : ∀ v : Fin n, ∀ c : G.Walk v v, c.IsCycle → 7 ≤ c.length) :
    ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) := by
  intro a b c d hac hbd h
  obtain ⟨hab, hbc, hcd, hda⟩ := h
  let w : G.Walk a a := .cons hab (.cons hbc (.cons hcd (.cons hda .nil)))
  have hcycle : w.IsCycle := by
    apply SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    refine ⟨?_, by simp [w]⟩
    simp [w, SimpleGraph.Walk.isPath_def, hbc.ne, hab.ne.symm, hcd.ne, hda.ne, hac.symm, hbd]
  have hlong := hgirth a w hcycle
  simp [w] at hlong

/-- The edge-plus-cover lower bound for monotone binary formulas on a graph of girth at least 7. -/
theorem monotoneFormulaGateLowerBound {n k : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj]
    (hgirth : ∀ v : Fin n, ∀ c : G.Walk v v, c.IsCycle → 7 ≤ c.length)
    (hcover : ∀ T : Finset (Fin n), (∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T) → k ≤ T.card)
    (φ : DMFormula n) (hpositive : PositiveLeaves φ)
    (heval : ∀ x : Fin n → Bool, φ.eval x =
      decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) :
    G.edgeSet.ncard + k ≤ binaryGates φ + 1 := by
  obtain ⟨T, hT, hbound⟩ :=
    PEqualNP.Outside.L_meta_531 n G (triangleFree hgirth) (squareFree hgirth) φ hpositive heval
  have hedge : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  rw [hedge, ← leaves_eq_gates_add_one]
  exact (Nat.add_le_add_left (hcover T hT) _).trans hbound

end Meta519Formula
