/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatLocalChainGeometry at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistFiniteChain
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistCollar

 

set_option autoImplicit false
noncomputable section

open Set Topology Metric
open LQGMetric LQGMetric.DG

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_heat_local_chain_geometry
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U)
    {z w : ℂ} (hz : z ∈ U) (hw : w ∈ U) :
    ∃ (ρ : ℝ) (N : ℕ) (p : ℕ → ℂ),
      0 < ρ ∧ 4 * ρ ≤ (1 / 2 : ℝ) ∧
      p 0 = z ∧ p (N + 1) = w ∧
      (∀ j, j ≤ N + 1 → ball (p j) (4 * ρ) ⊆ U) ∧
      (∀ j, j ≤ N → dist (p j) (p (j + 1)) < 2 * ρ) := by
  obtain ⟨q, hq⟩ := t15_exists_isDGPath hU hUc hz hw
  let K : Set ℂ := q '' Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image_of_continuousOn hq.continuousOn
  have hKU : K ⊆ U := by
    rintro x ⟨t, ht, rfl⟩
    exact hq.mapsTo ht
  obtain ⟨k, hk⟩ := pt_dist_eventual_crossing_ball_subset hK.isBounded hU
    (by simpa only [hK.isClosed.closure_eq] using hKU)
  let k₀ := max 4 k
  let ρ : ℝ := ((2 : ℝ)⁻¹) ^ k₀
  have hk₀ : 4 ≤ k₀ := le_max_left _ _
  have hkk₀ : k ≤ k₀ := le_max_right _ _
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρsmall : 4 * ρ ≤ (1 / 2 : ℝ) := by
    have hb : ρ ≤ ((2 : ℝ)⁻¹) ^ 4 := by
      dsimp [ρ]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hk₀
    norm_num at hb ⊢
    linarith
  obtain ⟨N, p, hp0, hpN, hpK, hpstep⟩ :=
    pt_dist_finite_chain_of_path hq (show 0 < 2 * ρ by positivity)
  refine ⟨ρ, N, p, hρ, hρsmall, hp0, hpN, ?_, hpstep⟩
  intro j hj x hx
  have hpj : p j ∈ K := hpK j hj
  have hsub := hk k₀ hkk₀ (p j) hpj (p j) (by simp)
  apply hsub
  have hle : 4 * ρ ≤ 17 * ρ := by nlinarith [hρ.le]
  exact lt_of_lt_of_le hx hle

end SupercriticalLQGUniqueness.B2.DG20Pt
