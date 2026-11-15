import LatticeProb.Prob.GlobalEntryClock

/-! # Global entry and hitting times after a cutoff -/

set_option autoImplicit false

open Set MeasureTheory Classical

namespace LatticeProb

/-- If all hit times lie after a cutoff, the global entry clock agrees with the
hitting time after that cutoff, including when the path never hits the set. -/
theorem globalEntryClock_eq_hittingAfter_of_lower_bound {Ω E : Type*}
    (f : Ω → ℝ → E) (U : Set E) (ω : Ω) (a : ℝ)
    (ha : ∀ t, f ω t ∈ U → a ≤ t) :
    entryClockOfEReal (globalOpenEntry f U ω) =
      hittingAfter (fun t ω => f ω t) U a ω := by
  let S : Set ℝ := {t | f ω t ∈ U}
  have hb : BddBelow S := ⟨a, fun t ht => ha t ht⟩
  by_cases hn : S.Nonempty
  · obtain ⟨u, hu⟩ := hn
    have hbot := globalOpenEntry_ne_bot_of_lower_bound f U ω a ha
    have htop : globalOpenEntry f U ω ≠ ⊤ := by
      have hle : globalOpenEntry f U ω ≤ (u : EReal) := sInf_le ⟨u, hu, rfl⟩
      exact ne_top_of_le_ne_top (EReal.coe_ne_top u) hle
    obtain ⟨c, hc, hcclock⟩ := (entryClockOfEReal_spec hbot).resolve_left
      (fun h => htop h.1)
    have hc_lower : ∀ t ∈ S, c ≤ t := by
      intro t ht
      have h : (c : EReal) ≤ (t : EReal) := by
        rw [← hc]
        exact sInf_le ⟨t, ht, rfl⟩
      exact EReal.coe_le_coe_iff.mp h
    have hcs : c = sInf S := by
      apply le_antisymm (le_csInf ⟨u, hu⟩ hc_lower)
      have h : ((sInf S : ℝ) : EReal) ≤ globalOpenEntry f U ω := by
        apply le_sInf
        rintro x ⟨t, ht, rfl⟩
        exact EReal.coe_le_coe_iff.mpr (csInf_le hb ht)
      rw [hc] at h
      exact EReal.coe_le_coe_iff.mp h
    have hs : {t : ℝ | a ≤ t ∧ f ω t ∈ U} = S := by
      ext t
      exact ⟨fun h => h.2, fun h => ⟨ha t h, h⟩⟩
    have hex : ∃ t, a ≤ t ∧ f ω t ∈ U := ⟨u, ha u hu, hu⟩
    rw [hcclock, hittingAfter, ite_eq_left hex, hs, ← hcs]
  · have hempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    have hg : globalOpenEntry f U ω = ⊤ := by
      change sInf ((fun t : ℝ => (t : EReal)) '' S) = ⊤
      simp only [hempty, image_empty, sInf_empty]
    rw [hg, entryClockOfEReal_top]
    symm
    apply hittingAfter_eq_top_iff.mpr
    intro t _ ht
    exact hn ⟨t, ht⟩

end LatticeProb
