import Mathlib
import LatticeProb.Analysis.RieszKernelHolder
import LatticeProb.Analysis.SegmentAveragePotential

/-!
# Morrey's oscillation estimate on balls

Let `E` be a finite-dimensional real inner product space of dimension `d` with an additive Haar
measure `μ`, and let `d < p < ∞`. If `f : E → F` is `C¹` on a ball `B = B(a, r)`, then
`‖f z - f z'‖ ≤ C r^{1 - d/p} ‖D f‖_{L^p(B)}` for all `z, z' ∈ B`, with a constant `C` that
depends only on `E`, `μ` and `p`.

The proof averages the triangle inequality `‖f z - f z'‖ ≤ ‖f z - f y‖ + ‖f y - f z'‖` over
`y ∈ B`. Each average is bounded by the Riesz potential of `‖D f‖` (`segmentAverage_potential`),
and the Riesz potential by Hölder's inequality (`rieszKernel_holder`). The factor `(2 r)^d` of the
potential bound cancels against `μ(B) = r^d μ(B(0, 1))`.

## Main results

* `LatticeProb.PegdenSmart.morrey_oscillation`: the oscillation estimate.
-/

open MeasureTheory Metric Set
open scoped ENNReal NNReal

namespace LatticeProb.PegdenSmart

/-- Morrey's oscillation estimate on balls, for `d < p < ∞`: the constant depends on `E`, `μ`
and `p` only. -/
theorem morrey_oscillation (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (p : ℝ≥0∞) :
    (Module.finrank ℝ E : ℝ≥0∞) < p → p ≠ ⊤ →
    ∃ C : ℝ≥0, ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
      (f : E → F) (a : E) (r : ℝ), 0 < r → ContDiffOn ℝ 1 f (ball a r) →
      ∀ z ∈ ball a r, ∀ z' ∈ ball a r,
        ‖f z - f z'‖ₑ ≤ (C : ℝ≥0∞) * ENNReal.ofReal r ^ (1 - (Module.finrank ℝ E : ℝ) / p.toReal) *
          eLpNorm (fderiv ℝ f) p (μ.restrict (ball a r)) := by
  intro hdp hp
  have hpd : (Module.finrank ℝ E : ℝ) < p.toReal := by
    simpa using ENNReal.toReal_strict_mono hp hdp
  have hp0 : p ≠ 0 := (zero_le.trans_lt hdp).ne'
  obtain ⟨C₁, hC₁⟩ := rieszKernel_holder E μ p.toReal hpd
  set d : ℕ := Module.finrank ℝ E with hd_def
  set m : ℝ≥0∞ := μ (ball (0 : E) 1) with hm_def
  have hm0 : m ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
  have hmtop : m ≠ ⊤ := measure_ball_lt_top.ne
  set K : ℝ≥0∞ := 2 * ENNReal.ofReal ((2 : ℝ) ^ d / d) * C₁ / m with hK_def
  have hKtop : K ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top)
      ENNReal.coe_ne_top) hm0
  refine ⟨K.toNNReal, ?_⟩
  intro F _ _ _ f a r hr hf z hz z' hz'
  rw [ENNReal.coe_toNNReal hKtop]
  set R : ℝ≥0∞ := ENNReal.ofReal r ^ (1 - (d : ℝ) / p.toReal) with hR_def
  set N : ℝ≥0∞ := eLpNorm (fderiv ℝ f) p (μ.restrict (ball a r)) with hN_def
  set A : ℝ≥0∞ := ENNReal.ofReal ((2 * r) ^ d / (d : ℝ)) with hA_def
  have hN : N = (∫⁻ w in ball a r, ‖fderiv ℝ f w‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal) :=
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp
      ((hf.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl).aestronglyMeasurable
        measurableSet_ball)
  have hpot : ∀ x ∈ ball a r, ∫⁻ y in ball a r, ‖f x - f y‖ₑ ∂μ ≤ A * (C₁ * R * N) := by
    intro x hx
    refine (segmentAverage_potential μ f a x r hr hf hx).trans ?_
    gcongr
    set g : E → ℝ≥0∞ := (ball a r).indicator fun w => ‖fderiv ℝ f w‖ₑ with hg_def
    have hg : Measurable g := measurable_indicator_enorm_fderiv hf
    have e1 : ∫⁻ w in ball a r, ‖fderiv ℝ f w‖ₑ * ‖w - x‖ₑ ^ (1 - (d : ℝ)) ∂μ =
        ∫⁻ w in ball a r, ‖w - x‖ₑ ^ (1 - (d : ℝ)) * g w ∂μ := by
      refine setLIntegral_congr_fun measurableSet_ball fun w hw => ?_
      simp [g, hw, mul_comm]
    have e2 : ∫⁻ w in ball a r, g w ^ p.toReal ∂μ =
        ∫⁻ w in ball a r, ‖fderiv ℝ f w‖ₑ ^ p.toReal ∂μ := by
      refine setLIntegral_congr_fun measurableSet_ball fun w hw => ?_
      simp [g, hw]
    rw [e1, hN, ← e2]
    exact hC₁ a x r hr hx g hg
  have hmeas : AEMeasurable (fun y => ‖f z - f y‖ₑ) (μ.restrict (ball a r)) :=
    (continuousOn_const.sub hf.continuousOn).enorm.aemeasurable measurableSet_ball
  have key : μ (ball a r) * ‖f z - f z'‖ₑ ≤ 2 * (A * (C₁ * R * N)) := by
    calc μ (ball a r) * ‖f z - f z'‖ₑ = ∫⁻ _ in ball a r, ‖f z - f z'‖ₑ ∂μ := by
          rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ y in ball a r, (‖f z - f y‖ₑ + ‖f z' - f y‖ₑ) ∂μ := by
          refine lintegral_mono fun y => ?_
          rw [enorm_sub_rev (f z') (f y), ← edist_eq_enorm_sub, ← edist_eq_enorm_sub,
            ← edist_eq_enorm_sub]
          exact edist_triangle _ _ _
      _ = ∫⁻ y in ball a r, ‖f z - f y‖ₑ ∂μ + ∫⁻ y in ball a r, ‖f z' - f y‖ₑ ∂μ :=
          lintegral_add_left' hmeas _
      _ ≤ A * (C₁ * R * N) + A * (C₁ * R * N) := add_le_add (hpot z hz) (hpot z' hz')
      _ = 2 * (A * (C₁ * R * N)) := (two_mul _).symm
  have hA : A = ENNReal.ofReal ((2 : ℝ) ^ d / d) * ENNReal.ofReal (r ^ d) := by
    rw [hA_def, ← ENNReal.ofReal_mul (by positivity), mul_pow]
    ring_nf
  have hfin : μ (ball a r) * (K * R * N) = 2 * (A * (C₁ * R * N)) := by
    rw [Measure.addHaar_ball_of_pos μ a hr, hA, hK_def, div_eq_mul_inv]
    calc ENNReal.ofReal (r ^ d) * m * (2 * ENNReal.ofReal ((2 : ℝ) ^ d / d) * C₁ * m⁻¹ * R * N)
        = (m * m⁻¹) *
            (2 * (ENNReal.ofReal ((2 : ℝ) ^ d / d) * ENNReal.ofReal (r ^ d) * (C₁ * R * N))) := by
          ring
      _ = _ := by rw [ENNReal.mul_inv_cancel hm0 hmtop, one_mul]
  rw [← hfin] at key
  exact (ENNReal.mul_le_mul_iff_right (measure_ball_pos μ a hr).ne' measure_ball_lt_top.ne).mp key

end LatticeProb.PegdenSmart
