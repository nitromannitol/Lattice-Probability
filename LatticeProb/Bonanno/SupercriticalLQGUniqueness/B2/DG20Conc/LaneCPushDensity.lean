/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPushDensity at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPushBounds

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.LFPP

def laneCPushSequence (n : ℕ) : ℝ := (1 / 1000) * ((n + 1 : ℝ)⁻¹)

theorem laneC_push_sequence_pos (n : ℕ) : 0 < laneCPushSequence n := by
  unfold laneCPushSequence
  positivity

theorem laneC_push_sequence_le (n : ℕ) : laneCPushSequence n ≤ 1 / 1000 := by
  unfold laneCPushSequence
  have h : (1 : ℝ) ≤ n + 1 := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hi : (n + 1 : ℝ)⁻¹ ≤ 1 := by
    simpa using (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) h)
  nlinarith

theorem laneC_push_sequence_tendsto :
    Tendsto laneCPushSequence atTop (nhds 0) := by
  unfold laneCPushSequence
  simpa using (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (1 / 1000 : ℝ))

theorem laneC_inwardPush_deriv_comp {d : ℝ} {γ : ℝ → ℂ} {t : ℝ}
    (hγ : DifferentiableAt ℝ γ t) :
    deriv (laneCInwardPush d ∘ γ) t =
      (fderiv ℝ (laneCInwardPush d) (γ t)) (deriv γ t) := by
  exact ((laneC_inwardPush_contDiff d).differentiable (by norm_num) (γ t)).hasFDerivAt
    |>.comp_hasDerivAt t hγ.hasDerivAt |>.deriv

theorem laneC_push_density_bound {ξ : ℝ} {f : ℂ → ℝ}
    {γ : ℝ → ℂ} {d B M t : ℝ}
    (_hd : d ∈ Icc (0 : ℝ) (1 / 1000))
    (hγz : γ t ∈ laneCOuterCluster)
    (hγ : DifferentiableAt ℝ γ t)
    (hB : ∀ z ∈ laneCOuterCluster,
      Real.exp (ξ * f (laneCInwardPush d z)) ≤ B)
    (hM : ∀ z ∈ laneCOuterCluster,
      ‖fderiv ℝ (laneCInwardPush d) z‖ ≤ M)
    (hB0 : 0 ≤ B) (hM0 : 0 ≤ M) :
    lenDens ξ f (laneCInwardPush d ∘ γ) t ≤
      ENNReal.ofReal (B * M) * ENNReal.ofReal ‖deriv γ t‖ := by
  have hnorm : ‖deriv (laneCInwardPush d ∘ γ) t‖ ≤ M * ‖deriv γ t‖ := by
    rw [laneC_inwardPush_deriv_comp hγ]
    exact ((fderiv ℝ (laneCInwardPush d) (γ t)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hM _ hγz) (norm_nonneg _))
  have hexp := hB _ hγz
  unfold lenDens
  rw [← ENNReal.ofReal_mul (mul_nonneg hB0 hM0)]
  exact ENNReal.ofReal_le_ofReal (by
    change Real.exp (ξ * f (laneCInwardPush d (γ t))) *
      ‖deriv (laneCInwardPush d ∘ γ) t‖ ≤ (B * M) * ‖deriv γ t‖
    calc
      _ ≤ B * ‖deriv (laneCInwardPush d ∘ γ) t‖ :=
        mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
      _ ≤ B * (M * ‖deriv γ t‖) := mul_le_mul_of_nonneg_left hnorm hB0
      _ = (B * M) * ‖deriv γ t‖ := by ring)

end SupercriticalLQGUniqueness.B2.DG20Conc
