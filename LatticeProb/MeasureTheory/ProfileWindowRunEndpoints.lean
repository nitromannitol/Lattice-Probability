import LatticeProb.MeasureTheory.BoundedAEProfileRun

/-! # Endpoints of almost-everywhere constant profile runs -/

set_option autoImplicit false

open Set MeasureTheory Filter

namespace LatticeProb

open scoped Classical in
/-- The bounds obtained from rational constant windows recover an absorbing run. -/
theorem profile_window_bounds_eq_run_endpoints
    (f : ℝ → ℝ) (a u b l r c : ℝ)
    (hal : a ≤ l) (hlu : l < u) (hur : u < r) (hrb : r ≤ b)
    (hrun : ∀ᵐ t ∂(volume.restrict (Ioo l r)), f t = c)
    (habsorb : ∀ p q : ℝ, Ioo p q ⊆ Ioo a b →
      (Ioo l r ∩ Ioo p q).Nonempty → ∀ d : ℝ,
      (∀ᵐ t ∂(volume.restrict (Ioo p q)), f t = d) →
      Ioo p q ⊆ Ioo l r) :
    (⨅ pq : ℚ × ℚ,
      if a ≤ (pq.1 : ℝ) ∧ (pq.1 : ℝ) < u ∧ u < (pq.2 : ℝ) ∧ (pq.2 : ℝ) ≤ b ∧
        ∃ d : ℝ, ∀ᵐ t ∂(volume.restrict (Ioo (pq.1 : ℝ) (pq.2 : ℝ))), f t = d
      then (pq.1 : ℝ) else b) = l ∧
    (⨆ pq : ℚ × ℚ,
      if a ≤ (pq.1 : ℝ) ∧ (pq.1 : ℝ) < u ∧ u < (pq.2 : ℝ) ∧ (pq.2 : ℝ) ≤ b ∧
        ∃ d : ℝ, ∀ᵐ t ∂(volume.restrict (Ioo (pq.1 : ℝ) (pq.2 : ℝ))), f t = d
      then (pq.2 : ℝ) else a) = r := by
  classical
  let W : ℚ × ℚ → Prop := fun pq =>
    a ≤ (pq.1 : ℝ) ∧ (pq.1 : ℝ) < u ∧ u < (pq.2 : ℝ) ∧ (pq.2 : ℝ) ≤ b ∧
      ∃ d : ℝ, ∀ᵐ t ∂(volume.restrict (Ioo (pq.1 : ℝ) (pq.2 : ℝ))), f t = d
  let L : ℚ × ℚ → ℝ := fun pq => if W pq then (pq.1 : ℝ) else b
  let R : ℚ × ℚ → ℝ := fun pq => if W pq then (pq.2 : ℝ) else a
  change (⨅ pq, L pq) = l ∧ (⨆ pq, R pq) = r
  have hqual (p q : ℚ) (hp : l < (p : ℝ)) (hpu : (p : ℝ) < u)
      (huq : u < (q : ℝ)) (hq : (q : ℝ) < r) : W (p, q) := by
    have hsub : Ioo (p : ℝ) (q : ℝ) ⊆ Ioo l r :=
      Ioo_subset_Ioo hp.le hq.le
    exact ⟨hal.trans hp.le, hpu, huq, hq.le.trans hrb, c,
      ae_restrict_of_ae_restrict_of_subset hsub hrun⟩
  have hbounds (pq : ℚ × ℚ) : l ≤ L pq ∧ R pq ≤ r := by
    by_cases hw : W pq
    · have hw' := hw
      obtain ⟨ha, hp, hq, hb, d, hd⟩ := hw'
      have hsub : Ioo (pq.1 : ℝ) (pq.2 : ℝ) ⊆ Ioo a b :=
        Ioo_subset_Ioo ha hb
      have hinter : (Ioo l r ∩ Ioo (pq.1 : ℝ) (pq.2 : ℝ)).Nonempty :=
        ⟨u, ⟨⟨hlu, hur⟩, ⟨hp, hq⟩⟩⟩
      have h := (Ioo_subset_Ioo_iff (hp.trans hq)).mp (habsorb _ _ hsub hinter d hd)
      simpa only [L, R, hw, ↓reduceIte] using h
    · simp only [L, R, hw, ↓reduceIte]
      exact ⟨le_of_lt (hlu.trans (hur.trans_le hrb)),
        (hal.trans (le_of_lt (hlu.trans hur)))⟩
  have hL : BddBelow (range L) := ⟨l, by rintro _ ⟨pq, rfl⟩; exact (hbounds pq).1⟩
  have hR : BddAbove (range R) := ⟨r, by rintro _ ⟨pq, rfl⟩; exact (hbounds pq).2⟩
  constructor
  · apply le_antisymm
    · by_contra h
      have hlt : l < ⨅ pq, L pq := lt_of_not_ge h
      obtain ⟨p, hlp, hp⟩ := exists_rat_btwn (lt_min hlu hlt)
      obtain ⟨q, huq, hqr⟩ := exists_rat_btwn hur
      have hw := hqual p q hlp (lt_of_lt_of_le hp (min_le_left _ _)) huq hqr
      have hle := ciInf_le hL (p, q)
      simp only [L, hw, ↓reduceIte] at hle
      exact (not_lt_of_ge hle) (lt_of_lt_of_le hp (min_le_right _ _))
    · exact le_ciInf fun pq => (hbounds pq).1
  · apply le_antisymm
    · exact ciSup_le fun pq => (hbounds pq).2
    · by_contra h
      have hlt : (⨆ pq, R pq) < r := lt_of_not_ge h
      obtain ⟨p, hlp, hpu⟩ := exists_rat_btwn hlu
      obtain ⟨q, hq, hqr⟩ := exists_rat_btwn (max_lt hur hlt)
      have hw := hqual p q hlp hpu (lt_of_le_of_lt (le_max_left _ _) hq) hqr
      have hle := le_ciSup hR (p, q)
      simp only [R, hw, ↓reduceIte] at hle
      exact (not_lt_of_ge hle) (lt_of_le_of_lt (le_max_right _ _) hq)

end LatticeProb
