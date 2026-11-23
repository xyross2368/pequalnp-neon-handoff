import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card

namespace Meta519Restriction

abbrev IsCover {n : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n)) : Prop :=
  ∀ a b, G.Adj a b → a ∈ T ∨ b ∈ T

/-- A zero restriction at v removes its incident edges. The cover number drops by one precisely
when some minimum cover of the original graph contains v. -/
theorem coverDropIff {n k k' : ℕ} {G H : SimpleGraph (Fin n)} (v : Fin n)
    (hdelete : ∀ a b, H.Adj a b ↔ G.Adj a b ∧ a ≠ v ∧ b ≠ v)
    (Gminimum : ∀ T, IsCover G T → k ≤ T.card)
    (Hminimum : ∀ T, IsCover H T → k' ≤ T.card)
    (Hattains : ∃ U, IsCover H U ∧ U.card = k') :
    k' + 1 = k ↔ ∃ T, IsCover G T ∧ T.card = k ∧ v ∈ T := by
  obtain ⟨U, hU, hUc⟩ := Hattains
  have added : IsCover G (insert v U) := by
    intro a b hab
    by_cases ha : a = v
    · simp [ha]
    by_cases hb : b = v
    · simp [hb]
    exact (hU a b ((hdelete a b).mpr ⟨hab, ha, hb⟩)).imp
      (fun hm => Finset.mem_insert_of_mem hm) (fun hm => Finset.mem_insert_of_mem hm)
  have hupper : k ≤ k' + 1 :=
    (Gminimum _ added).trans (by simpa [hUc] using Finset.card_insert_le v U)
  constructor
  · intro hdrop
    have hv : v ∉ U := by
      intro hv
      have bound := Gminimum U (by simpa [Finset.insert_eq_of_mem hv] using added)
      omega
    refine ⟨insert v U, added, ?_, Finset.mem_insert_self _ _⟩
    rw [Finset.card_insert_of_notMem hv, hUc, hdrop]
  · rintro ⟨T, hT, hTc, hv⟩
    have erased : IsCover H (T.erase v) := by
      intro a b hab
      obtain ⟨hab', ha, hb⟩ := (hdelete a b).mp hab
      exact (hT a b hab').imp (fun hm => Finset.mem_erase.mpr ⟨ha, hm⟩)
        (fun hm => Finset.mem_erase.mpr ⟨hb, hm⟩)
    have hbound := Hminimum _ erased
    rw [Finset.card_erase_of_mem hv, hTc] at hbound
    have hpos : 0 < k := hTc ▸ Finset.card_pos.mpr ⟨v, hv⟩
    omega

end Meta519Restriction
