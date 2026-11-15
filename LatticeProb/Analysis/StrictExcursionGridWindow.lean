import LatticeProb.Analysis.ExcursionGridCells
import LatticeProb.Analysis.SeparatedExcursionContacts

/-! # Strict excursion windows on fine grids -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- A strict level excursion through separated intervals yields, at every
sufficiently fine positive mesh, two interior grid cells whose minima are below
the minimum on the interval between them. -/
theorem exists_strict_excursion_grid_window {f : ℝ → ℝ} {a b c d r : ℝ}
    (hf : Continuous f) (hbc : b < c)
    (hleft : ∃ x ∈ Icc a b, f x < r) (hright : ∃ y ∈ Icc c d, f y < r)
    (hmiddle : ∀ z ∈ Icc b c, r < f z) :
    ∃ δ > 0, ∀ ε, 0 < ε → ε < δ → ∃ i j : ℤ,
      i + 1 < j ∧
      a < ε * ((i : ℝ) - 1) ∧ ε * i < b ∧
      c < ε * ((j : ℝ) - 1) ∧ ε * j < d ∧
      sInf (f '' Icc (ε * ((i : ℝ) - 1)) (ε * i)) ≤ r ∧
      sInf (f '' Icc (ε * ((j : ℝ) - 1)) (ε * j)) ≤ r ∧
      r < sInf (f '' Icc (ε * i) (ε * ((j : ℝ) - 1))) := by
  obtain ⟨s, hs, t, ht, hfs, hft, hexc⟩ :=
    exists_separated_excursion_contacts hf hbc.le hleft hright hmiddle
  let δ := min (min (s - a) (b - s)) (min (t - c) (d - t))
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (lt_min (sub_pos.mpr hs.1) (sub_pos.mpr hs.2))
      (lt_min (sub_pos.mpr ht.1) (sub_pos.mpr ht.2))
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεd
  have h₁ : ε < s - a := hεd.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have h₂ : ε < b - s := hεd.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have h₃ : ε < t - c := hεd.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have h₄ : ε < d - t := hεd.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨i, j, hij, hai, his, hsi, hib, hcj, hjt, htj, hjd, hij'⟩ :=
    exists_excursion_grid_cells hbc hε h₁ h₂ h₃ h₄
  have hl : sInf (f '' Icc (ε * ((i : ℝ) - 1)) (ε * i)) ≤ r := by
    rw [← hfs]
    exact csInf_le (isCompact_Icc.bddBelow_image hf.continuousOn)
      ⟨s, ⟨his, hsi.le⟩, rfl⟩
  have hr : sInf (f '' Icc (ε * ((j : ℝ) - 1)) (ε * j)) ≤ r := by
    rw [← hft]
    exact csInf_le (isCompact_Icc.bddBelow_image hf.continuousOn)
      ⟨t, ⟨hjt.le, htj⟩, rfl⟩
  have hm : r < sInf (f '' Icc (ε * i) (ε * ((j : ℝ) - 1))) := by
    apply (isCompact_Icc.lt_sInf_iff_of_continuous
      (nonempty_Icc.mpr hij'.le) hf.continuousOn r).2
    intro z hz
    exact hexc z ⟨hsi.trans_le hz.1, hz.2.trans_lt hjt⟩
  exact ⟨i, j, hij, hai, hib, hcj, hjd, hl, hr, hm⟩


/-- The strict excursion grid windows can be chosen simultaneously at every
sufficiently fine reciprocal mesh. -/
theorem exists_strict_excursion_reciprocal_grid_window {f : ℝ → ℝ} {a b c d r : ℝ}
    (hf : Continuous f) (hbc : b < c)
    (hleft : ∃ x ∈ Icc a b, f x < r) (hright : ∃ y ∈ Icc c d, f y < r)
    (hmiddle : ∀ z ∈ Icc b c, r < f z) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → ∃ i j : ℤ,
      let ε : ℝ := 1 / n
      i + 1 < j ∧
      a < ε * ((i : ℝ) - 1) ∧ ε * i < b ∧
      c < ε * ((j : ℝ) - 1) ∧ ε * j < d ∧
      sInf (f '' Icc (ε * ((i : ℝ) - 1)) (ε * i)) ≤ r ∧
      sInf (f '' Icc (ε * ((j : ℝ) - 1)) (ε * j)) ≤ r ∧
      r < sInf (f '' Icc (ε * i) (ε * ((j : ℝ) - 1))) := by
  obtain ⟨δ, hδ, hgrid⟩ := exists_strict_excursion_grid_window hf hbc hleft hright hmiddle
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
  refine ⟨k + 1, Nat.zero_lt_succ k, ?_⟩
  intro n hn
  have hnpos : 0 < n := (Nat.zero_lt_succ k).trans_le hn
  have hle : 1 / (n : ℝ) ≤ 1 / ((k : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hn)
  exact hgrid (1 / n) (by positivity) (hle.trans_lt hk)

end LatticeProb
