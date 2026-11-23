import PEqualNP.MetaComplexity.Helpers.Readers

namespace NeonRound2Audit

open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers.Readers

theorem essentialInputSavesOne {n s : ℕ} {f : (Fin (n + 1) → Bool) → Bool}
    (i : Fin (n + 1)) (b : Bool) (hd : Dep f i)
    (hc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x i b) ≠ f (Function.update y i b))
    (hf : HasCircuitSize (n + 1) f s) : Drop f i b 1 s := by
  obtain ⟨gs, o, least, hs⟩ := exists_least (n + 1) f s (dep_nc hd) hf
  obtain ⟨p, hp⟩ := least.dep_read i hd hc
  have saved := least.save i b (hc b) {p} (by
    intro j hj
    have e : j = p := Finset.mem_singleton.mp hj
    subst j
    exact rc_input b hp)
  rw [Finset.card_singleton] at saved
  exact saved.mono (Nat.le_refl 1) hs

end NeonRound2Audit
