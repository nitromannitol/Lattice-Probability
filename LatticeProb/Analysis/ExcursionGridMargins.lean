import Mathlib

/-!
# Margins for approximating ordered excursions

A countable family of positive horizons suffices for ordered excursion
endpoints. For each such choice, the grid constraints hold for every
sufficiently small mesh.
-/

set_option autoImplicit false

open Filter
open scoped Topology

namespace LatticeProb

/-- A reciprocal horizon can be chosen strictly below both excursion lengths,
with a positive mesh threshold preserving the endpoint and separation margins. -/
theorem exists_reciprocal_horizon_grid_margin
    {a b s d : ℝ} (ha : 0 < a) (hab : a < b) (hbs : b < s)
    (hsep : d < s - a) :
    ∃ k : ℕ, ∃ δ : ℝ, 0 < δ ∧
      a + 1 / (k + 1 : ℝ) ≤ s ∧
      ∀ ε : ℝ, ε < δ →
        ε < a ∧ d + ε < s - a ∧ b + 1 / (k + 1 : ℝ) + ε < s := by
  have hl : 0 < min (s - a) (s - b) / 2 := by
    apply div_pos (lt_min (by linarith) (by linarith)) (by norm_num)
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hl
  have hka : 1 / (k + 1 : ℝ) < (s - a) / 2 :=
    hk.trans_le (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
  have hkb : 1 / (k + 1 : ℝ) < (s - b) / 2 :=
    hk.trans_le (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
  have hkpos : 0 < 1 / (k + 1 : ℝ) := by positivity
  let δ := min a (min (s - a - d) (s - b - 1 / (k + 1 : ℝ)))
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min ha (lt_min (by linarith) (by linarith))
  refine ⟨k, δ, hδ, by linarith, ?_⟩
  intro ε hε
  have hεa : ε < a := hε.trans_le (min_le_left _ _)
  have hεsep : ε < s - a - d :=
    hε.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεback : ε < s - b - 1 / (k + 1 : ℝ) :=
    hε.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  exact ⟨hεa, by linarith, by linarith⟩

/-- For any mesh sequence tending to zero, one reciprocal horizon works for
all sufficiently fine meshes. -/
theorem exists_reciprocal_horizon_eventually_grid_margin
    {a b s d : ℝ} (ha : 0 < a) (hab : a < b) (hbs : b < s)
    (hsep : d < s - a) {mesh : ℕ → ℝ} (hmesh : Tendsto mesh atTop (𝓝 0)) :
    ∃ k : ℕ, a + 1 / (k + 1 : ℝ) ≤ s ∧
      ∀ᶠ n in atTop, mesh n < a ∧ d + mesh n < s - a ∧
        b + 1 / (k + 1 : ℝ) + mesh n < s := by
  obtain ⟨k, δ, hδ, hk, hbound⟩ :=
    exists_reciprocal_horizon_grid_margin ha hab hbs hsep
  refine ⟨k, hk, ?_⟩
  filter_upwards [hmesh.eventually (eventually_lt_nhds hδ)] with n hn
  exact hbound (mesh n) hn

end LatticeProb
