import LatticeProb.Analysis.StrictExcursionGridWindow

/-! # Fine-grid windows from compact interval minima -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- A strict comparison of the two outer minima with the middle minimum
provides a level separating outer witnesses from the whole middle interval. -/
theorem exists_level_between_interval_minima {f : ℝ → ℝ} {a b c d : ℝ}
    (hf : Continuous f) (hab : a ≤ b) (hcd : c ≤ d)
    (hgap : max (sInf (f '' Icc a b)) (sInf (f '' Icc c d)) <
      sInf (f '' Icc b c)) :
    ∃ r : ℝ, (∃ x ∈ Icc a b, f x < r) ∧
      (∃ y ∈ Icc c d, f y < r) ∧ ∀ z ∈ Icc b c, r < f z := by
  obtain ⟨r, hrlo, hrhi⟩ := exists_between hgap
  have hl : sInf (f '' Icc a b) < r := (le_max_left _ _).trans_lt hrlo
  have hr : sInf (f '' Icc c d) < r := (le_max_right _ _).trans_lt hrlo
  obtain ⟨_, ⟨x, hx, rfl⟩, hfx⟩ :=
    exists_lt_of_csInf_lt ((nonempty_Icc.mpr hab).image f) hl
  obtain ⟨_, ⟨y, hy, rfl⟩, hfy⟩ :=
    exists_lt_of_csInf_lt ((nonempty_Icc.mpr hcd).image f) hr
  refine ⟨r, ⟨x, hx, hfx⟩, ⟨y, hy, hfy⟩, ?_⟩
  intro z hz
  exact hrhi.trans_le (csInf_le (isCompact_Icc.bddBelow_image hf.continuousOn)
    ⟨z, hz, rfl⟩)

/-- A strict comparison of compact interval minima persists on suitable
interior grid cells at every sufficiently small positive mesh. -/
theorem exists_grid_window_of_interval_minima {f : ℝ → ℝ} {a b c d : ℝ}
    (hf : Continuous f) (hab : a ≤ b) (hbc : b < c) (hcd : c ≤ d)
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
  obtain ⟨δ, hδ, hgrid⟩ := exists_strict_excursion_grid_window hf hbc hl hr hm
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεd
  obtain ⟨i, j, hij, hai, hib, hcj, hjd, hli, hrj, hmij⟩ := hgrid ε hε hεd
  exact ⟨i, j, hij, hai, hib, hcj, hjd, (max_le hli hrj).trans_lt hmij⟩

/-- The same comparison is realized for every sufficiently fine reciprocal mesh. -/
theorem exists_reciprocal_grid_window_of_interval_minima {f : ℝ → ℝ} {a b c d : ℝ}
    (hf : Continuous f) (hab : a ≤ b) (hbc : b < c) (hcd : c ≤ d)
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
  obtain ⟨r, hl, hr, hm⟩ := exists_level_between_interval_minima hf hab hcd hgap
  obtain ⟨N, hN, hgrid⟩ := exists_strict_excursion_reciprocal_grid_window hf hbc hl hr hm
  refine ⟨N, hN, ?_⟩
  intro n hn
  obtain ⟨i, j, hij, hai, hib, hcj, hjd, hli, hrj, hmij⟩ := hgrid n hn
  exact ⟨i, j, hij, hai, hib, hcj, hjd, (max_le hli hrj).trans_lt hmij⟩

end LatticeProb
