/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.L3_4N5 at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4N4
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgBridge
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgCont
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg
import Mathlib.Topology.TietzeExtension
import Mathlib.Analysis.Complex.Harmonic.MeanValue

/-!
# `𝔥^r(0) = h_r(0)`, deterministic part: mollified circle averages of a harmonic distribution

If a distribution `T` equals a harmonic function `g` on `B_1(0)`, then for `0 ≤ ρ < 1` the
mollified circle averages `mollAvg T n 0 ρ = ⟨T, circBump n 0 ρ⟩` converge to `g(0)`: for large
`n` they equal those of a continuous extension `g̃` of `g|_{B̄_R(0)}` (Tietze, `R = (1+ρ)/2`),
which converge to the circle average of `g̃` (`CircleAvg.tendsto_mollAvg_ofCont`), equal to
`g(0)` by the mean value property (mathlib `HarmonicOnNhd.circleAverage_eq`).

* `circBump_eq_zero_of_norm` — `circBump n 0 ρ` vanishes for `|y| ≥ ρ + 2^{-n}`.
* `tendsto_mollAvg_of_harmonic`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Finset Metric InnerProductSpace Topology
open scoped ENNReal

namespace LQGMetric.LM

open Blueprint GM CircleAvg

lemma circBump_eq_zero_of_norm {n : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ) {y : ℂ}
    (hy : ρ + (2 : ℝ)⁻¹ ^ n ≤ ‖y‖) : circBump n 0 ρ y = 0 := by
  rw [circBump_apply]
  have h0 : EqOn (fun x => bumpTest n x y) (fun _ => (0 : ℝ)) (sphere (0 : ℂ) |ρ|) := by
    intro x hx
    have hx' : ‖x‖ = ρ := by simpa [abs_of_nonneg hρ] using hx
    show bumpTest n x y = 0
    rw [bumpTest_apply, ContDiffBump.normed_def, (bumpAt n x).zero_of_le_dist, zero_div]
    show (2 : ℝ)⁻¹ ^ n ≤ dist y x
    have := norm_sub_norm_le y x
    rw [dist_eq_norm]; linarith
  rw [Real.circleAverage_congr_sphere h0]
  simp [Real.circleAverage]

lemma tsupport_circBump_subset_ball {n : ℕ} {ρ R : ℝ} (hρ : 0 ≤ ρ) (hR : ρ + (2 : ℝ)⁻¹ ^ n < R) :
    tsupport (circBump n 0 ρ : ℂ → ℝ) ⊆ ball (0 : ℂ) R := by
  refine (closure_minimal (fun y hy => ?_) isClosed_closedBall).trans
    (closedBall_subset_ball hR)
  by_contra hy'
  rw [mem_closedBall, dist_zero_right, not_le] at hy'
  exact hy (circBump_eq_zero_of_norm hρ hy'.le)

/-- **Mollified circle averages of a harmonic distribution** converge to its value at the
centre. -/
theorem tendsto_mollAvg_of_harmonic {T : DistC} {g : ℂ → ℝ}
    (hg : HarmonicOnNhd g (ball (0 : ℂ) 1))
    (hrep : ∀ φ : TestOn (ballO 0 1), restrictTo (ballO 0 1) T φ = ∫ x, g x * φ x)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Tendsto (fun n => mollAvg T n 0 ρ) atTop (𝓝 (g 0)) := by
  set R := (1 + ρ) / 2 with hRdef
  have hR1 : R < 1 := by rw [hRdef]; linarith
  have hρR : ρ < R := by rw [hRdef]; linarith
  have hBR : closedBall (0 : ℂ) R ⊆ ball (0 : ℂ) 1 := closedBall_subset_ball hR1
  have hcont : ContinuousOn g (closedBall (0 : ℂ) R) := fun x hx =>
    (hg x (hBR hx)).1.continuousAt.continuousWithinAt
  obtain ⟨gt, hgt⟩ := ContinuousMap.exists_restrict_eq (isClosed_closedBall (x := (0 : ℂ)) (ε := R))
    ⟨fun x => g x, continuousOn_iff_continuous_domRestrict.1 hcont⟩
  have hgtEq : ∀ x ∈ closedBall (0 : ℂ) R, gt x = g x := fun x hx => by
    have := congrArg (fun F : C(closedBall (0 : ℂ) R, ℝ) => F ⟨x, hx⟩) hgt
    exact this
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (sub_pos.2 hρR) (by norm_num : (2 : ℝ)⁻¹ < 1)
  have hev : ∀ᶠ n in atTop, mollAvg (ofCont gt) n 0 ρ = mollAvg T n 0 ρ := by
    filter_upwards [eventually_ge_atTop N] with n hn
    have hpow : (2 : ℝ)⁻¹ ^ n ≤ (2 : ℝ)⁻¹ ^ N := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
    have hts : tsupport (circBump n 0 ρ : ℂ → ℝ) ⊆ ball (0 : ℂ) 1 :=
      (tsupport_circBump_subset_ball hρ0 (by linarith : ρ + (2 : ℝ)⁻¹ ^ n < R)).trans
        (ball_subset_ball hR1.le)
    rw [mollAvg_eq, mollAvg_eq, ofCont_apply, ← restrictTo_testOn1 T _ hts, hrep]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    show circBump n 0 ρ y * gt y = g y * circBump n 0 ρ y
    by_cases hy : ‖y‖ ≤ R
    · rw [hgtEq y (by simpa using hy), mul_comm]
    · rw [circBump_eq_zero_of_norm hρ0 (by rw [not_le] at hy; linarith)]; simp
  have hlim := tendsto_mollAvg_ofCont gt ρ 0
  have hca : Real.circleAverage gt 0 ρ = g 0 := by
    have hsph : EqOn gt g (sphere (0 : ℂ) |ρ|) := fun x hx => hgtEq x (by
      rw [mem_closedBall, dist_zero_right]
      have : ‖x‖ = |ρ| := by simpa using hx
      rw [this, abs_of_nonneg hρ0]; exact hρR.le)
    rw [Real.circleAverage_congr_sphere hsph]
    refine InnerProductSpace.HarmonicOnNhd.circleAverage_eq (hg.mono ?_)
    rw [abs_of_nonneg hρ0]; exact closedBall_subset_ball hρ1
  rw [hca] at hlim
  exact hlim.congr' hev

end LQGMetric.LM
