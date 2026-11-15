import LatticeProb.Analysis.CompactMinimaGridWindow

/-! # Fine-grid windows with touching intervals -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- Strict compact minimum comparison gives interior grid windows even when
the middle interval is a singleton. -/
theorem exists_grid_window_of_interval_minima_le {f : ℝ → ℝ} {a b c d : ℝ}
    (hf : Continuous f) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hgap : max (sInf (f '' Icc a b)) (sInf (f '' Icc c d)) <
      sInf (f '' Icc b c)) :
    ∃ δ > 0, ∀ ε, 0 < ε → ε < δ → ∃ i j : ℤ,
      i + 1 < j ∧
      a < ε * ((i : ℝ) - 1) ∧ ε * i < b ∧
      c < ε * ((j : ℝ) - 1) ∧ ε * j < d ∧
      max (sInf (f '' Icc (ε * ((i : ℝ) - 1)) (ε * i)))
        (sInf (f '' Icc (ε * ((j : ℝ) - 1)) (ε * j))) <
        sInf (f '' Icc (ε * i) (ε * ((j : ℝ) - 1))) := by
  obtain ⟨r, hl, hr, hm⟩ := exists_level_between_interval_minima hf hab hcd hgap
  obtain ⟨s, hs, t, ht, hfs, hft, hexc⟩ :=
    exists_separated_excursion_contacts hf hbc hl hr hm
  let b' := (s + b) / 2
  let c' := (c + t) / 2
  have hsb : s < b' := by dsimp [b']; linarith [hs.2]
  have hbb : b' < b := by dsimp [b']; linarith [hs.2]
  have hcc : c < c' := by dsimp [c']; linarith [ht.1]
  have hct : c' < t := by dsimp [c']; linarith [ht.1]
  have hsep : b' < c' := hbb.trans_le hbc |>.trans hcc
  let δ := min (min (s - a) (b' - s)) (min (t - c') (d - t))
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (lt_min (sub_pos.mpr hs.1) (sub_pos.mpr hsb))
      (lt_min (sub_pos.mpr hct) (sub_pos.mpr ht.2))
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεd
  have h₁ : ε < s - a := hεd.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have h₂ : ε < b' - s := hεd.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have h₃ : ε < t - c' := hεd.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have h₄ : ε < d - t := hεd.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨i, j, hij, hai, his, hsi, hib, hcj, hjt, htj, hjd, hij'⟩ :=
    exists_excursion_grid_cells hsep hε h₁ h₂ h₃ h₄
  have hli : sInf (f '' Icc (ε * ((i : ℝ) - 1)) (ε * i)) ≤ r := by
    rw [← hfs]
    exact csInf_le (isCompact_Icc.bddBelow_image hf.continuousOn)
      ⟨s, ⟨his, hsi.le⟩, rfl⟩
  have hrj : sInf (f '' Icc (ε * ((j : ℝ) - 1)) (ε * j)) ≤ r := by
    rw [← hft]
    exact csInf_le (isCompact_Icc.bddBelow_image hf.continuousOn)
      ⟨t, ⟨hjt.le, htj⟩, rfl⟩
  have hmij : r < sInf (f '' Icc (ε * i) (ε * ((j : ℝ) - 1))) := by
    apply (isCompact_Icc.lt_sInf_iff_of_continuous
      (nonempty_Icc.mpr hij'.le) hf.continuousOn r).2
    intro z hz
    exact hexc z ⟨hsi.trans_le hz.1, hz.2.trans_lt hjt⟩
  exact ⟨i, j, hij, hai, hib.trans hbb, hcc.trans hcj, hjd, (max_le hli hrj).trans_lt hmij⟩

/-- The same comparison holds at every sufficiently fine reciprocal mesh. -/
theorem exists_reciprocal_grid_window_of_interval_minima_le {f : ℝ → ℝ} {a b c d : ℝ}
    (hf : Continuous f) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hgap : max (sInf (f '' Icc a b)) (sInf (f '' Icc c d)) <
      sInf (f '' Icc b c)) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → ∃ i j : ℤ,
      let ε : ℝ := 1 / n
      i + 1 < j ∧
      a < ε * ((i : ℝ) - 1) ∧ ε * i < b ∧
      c < ε * ((j : ℝ) - 1) ∧ ε * j < d ∧
      max (sInf (f '' Icc (ε * ((i : ℝ) - 1)) (ε * i)))
        (sInf (f '' Icc (ε * ((j : ℝ) - 1)) (ε * j))) <
        sInf (f '' Icc (ε * i) (ε * ((j : ℝ) - 1))) := by
  obtain ⟨δ, hδ, hgrid⟩ := exists_grid_window_of_interval_minima_le hf hab hbc hcd hgap
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
  refine ⟨k + 1, Nat.zero_lt_succ k, ?_⟩
  intro n hn
  have hnpos : 0 < n := (Nat.zero_lt_succ k).trans_le hn
  have hle : 1 / (n : ℝ) ≤ 1 / ((k : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hn)
  exact hgrid (1 / n) (by positivity) (hle.trans_lt hk)

end LatticeProb
