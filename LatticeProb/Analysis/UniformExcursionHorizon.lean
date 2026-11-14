import Mathlib

/-!
# Uniform horizons for ordered excursions

A positive lower bound for each relevant time gap gives one horizon and one
mesh threshold, uniformly over all endpoints with those gaps.
-/

set_option autoImplicit false

open Filter
open scoped Topology

namespace LatticeProb

/-- Separation and a lower bound on the omitted endpoint gap provide a common
positive horizon, with a uniform margin for all sufficiently small meshes. -/
theorem exists_uniform_excursion_horizon {d q : ℝ} (hd : 0 < d) (hq : 0 < q) :
    ∃ H : ℝ, 0 < H ∧ ∀ a b s : ℝ, d < s - a → q < s - b →
      a + H < s ∧ ∀ ε : ℝ, ε < H → b + H + ε < s := by
  let H := min d q / 2
  have hH : 0 < H := div_pos (lt_min hd hq) (by norm_num)
  have hHd : H ≤ d / 2 := div_le_div_of_nonneg_right (min_le_left d q) (by norm_num)
  have hHq : H ≤ q / 2 := div_le_div_of_nonneg_right (min_le_right d q) (by norm_num)
  refine ⟨H, hH, ?_⟩
  intro a b s hsa hsb
  constructor
  · linarith
  · intro ε hε
    linarith

/-- A vanishing mesh eventually satisfies the common horizon bounds for every
pair of endpoints in the same separated, positive-gap class. -/
theorem exists_uniform_excursion_horizon_eventually
    {d q : ℝ} (hd : 0 < d) (hq : 0 < q) {mesh : ℕ → ℝ}
    (hmesh : Tendsto mesh atTop (𝓝 0)) :
    ∃ H : ℝ, 0 < H ∧ ∀ᶠ n in atTop, ∀ a b s : ℝ,
      d < s - a → q < s - b → a + H < s ∧ b + H + mesh n < s := by
  obtain ⟨H, hH, hbound⟩ := exists_uniform_excursion_horizon hd hq
  refine ⟨H, hH, ?_⟩
  filter_upwards [hmesh.eventually (eventually_lt_nhds hH)] with n hn
  intro a b s ha hb
  obtain ⟨hforward, hbackward⟩ := hbound a b s ha hb
  exact ⟨hforward, hbackward (mesh n) hn⟩

end LatticeProb
