import Mathlib.Data.Fintype.Basic

/-!
# De Morgan formulas and leaf size

A de Morgan formula on `n` inputs is a binary tree whose inner nodes are AND or OR and whose
leaves are literals: an input or the negation of an input. Negations sit only at the leaves and
cost nothing; there are no constants, so every formula has at least one leaf. The leaf size is
the number of leaves, counting every occurrence of a literal. This is the usual formula size
measure over the de Morgan basis.

It differs from the circuit size of `Defs/MetaComplexity.lean` in two ways: nothing is shared
(a subformula used twice is written twice), and negations are free.

* `DMFormula n`: the formulas. `DMFormula.eval φ x`: the value at the input `x`.
* `DMFormula.leaves φ`: the number of leaves.
* `HasLeafSize n f s`: some formula with at most `s` leaves computes `f`.
-/

namespace PEqualNP.MetaComplexity

/-- A de Morgan formula on `n` inputs: a literal `lit i b` (the input `i` when `b` is true, its
negation when `b` is false), or the AND or the OR of two formulas. -/
inductive DMFormula (n : ℕ) : Type
  | lit : Fin n → Bool → DMFormula n
  | and : DMFormula n → DMFormula n → DMFormula n
  | or : DMFormula n → DMFormula n → DMFormula n

/-- The value of a formula at the input `x`. -/
def DMFormula.eval {n : ℕ} : DMFormula n → (Fin n → Bool) → Bool
  | DMFormula.lit i b, x => if b then x i else !x i
  | DMFormula.and φ ψ, x => φ.eval x && ψ.eval x
  | DMFormula.or φ ψ, x => φ.eval x || ψ.eval x

/-- The number of leaves of a formula, every occurrence of a literal counted. -/
def DMFormula.leaves {n : ℕ} : DMFormula n → ℕ
  | DMFormula.lit _ _ => 1
  | DMFormula.and φ ψ => φ.leaves + ψ.leaves
  | DMFormula.or φ ψ => φ.leaves + ψ.leaves

/-- `f` is computed by a de Morgan formula with at most `s` leaves. -/
def HasLeafSize (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ φ : DMFormula n, φ.leaves ≤ s ∧ ∀ x : Fin n → Bool, φ.eval x = f x

end PEqualNP.MetaComplexity
