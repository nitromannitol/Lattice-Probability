/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: BouRabeeGwynne/BrownianStoppedLimit.lean.
-/

import LatticeProb.Prob.BrownianPathSpace
import LatticeProb.Prob.BrownianStoppedSum
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Bounded stopped harmonic expectation, obtained from actual dyadic sums

The upper stopping approximations converge pathwise. Compact support supplies
the domination, and the summed C² remainder tends to zero. This proves the
stopped expectation identity rather than assuming a harmonic martingale.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace LatticeProb

/-- A stopping time with values in `ℝ≥0` is measurable as a map `BrownianPath d → ℝ≥0`. -/
lemma measurable_nnreal_brownian_stopping {d : ℕ} {σ : BrownianPath d → ℝ≥0}
    (hσ : IsStoppingTime (brownianNaturalFiltration d) (fun ω ↦ (σ ω : ℝ≥0∞))) :
    Measurable σ := by
  have hcoe : Measurable (fun ω ↦ (σ ω : ℝ≥0∞)) := hσ.measurable'
  simpa only [Function.comp_def, ENNReal.toNNReal_coe] using
    ENNReal.measurable_toNNReal.comp hcoe

/-- If `σ` is measurable, then evaluating a Brownian path at the random time `σ ω` is
measurable. -/
lemma measurable_brownian_random_evaluation {d : ℕ} {σ : BrownianPath d → ℝ≥0}
    (hσ : Measurable σ) : Measurable (fun ω : BrownianPath d ↦ ω (σ ω)) := by
  have heval : Measurable (fun p : BrownianPath d × ℝ≥0 ↦ p.1 p.2) :=
    (by fun_prop : Continuous (fun p : BrownianPath d × ℝ≥0 ↦ p.1 p.2)).measurable
  exact heval.comp (measurable_id.prodMk hσ)

/-- The dyadic grid length `⌈N * 2ⁿ⌉ / 2ⁿ` of the upper dyadic approximation of `N` is at most
`N + 1`, uniformly in the level `n`. -/
lemma dyadic_grid_length_le (N : ℝ≥0) (n : ℕ) :
    (⌈N * (2 : ℝ≥0) ^ n⌉₊ : ℝ≥0) * (1 / (2 : ℝ≥0) ^ n) ≤ N + 1 := by
  have hq : 0 < (2 : ℝ≥0) ^ n := by positivity
  have hqone : (1 : ℝ≥0) ≤ (2 : ℝ≥0) ^ n := one_le_pow₀ (by norm_num)
  calc
    _ = (⌈N * (2 : ℝ≥0) ^ n⌉₊ : ℝ≥0) / (2 : ℝ≥0) ^ n := by rw [mul_one_div]
    _ ≤ (N * (2 : ℝ≥0) ^ n + 1) / (2 : ℝ≥0) ^ n :=
      div_le_div_of_nonneg_right (Nat.ceil_lt_add_one (by positivity)).le hq.le
    _ = N + 1 / (2 : ℝ≥0) ^ n := by
      rw [add_div, mul_div_cancel_right₀ _ (ne_of_gt hq)]
    _ ≤ N + 1 := add_le_add_right ((div_le_one hq).mpr hqone) N

/-- A bounded genuine stopping time, before which the translated path stays
in the harmonic region, preserves the expectation of a compact C² function. -/
theorem standardBrownianLaw_bounded_stopped_harmonic_difference {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) (hsupp : HasCompactSupport f)
    {U : Set (Euc d)} (hh : IsHarmonicOn f U)
    {σ : BrownianPath d → ℝ≥0}
    (hσ : IsStoppingTime (brownianNaturalFiltration d) (fun ω ↦ (σ ω : ℝ≥0∞)))
    (N : ℝ≥0) (hN : ∀ ω, σ ω ≤ N) (z : Euc d)
    (hstay : ∀ ω t, t < σ ω → z + ω t ∈ U) :
    (∫ ω, f (z + ω (σ ω)) - f (z + ω 0) ∂μ) = 0 := by
  letI : IsProbabilityMeasure μ := hμ.1
  let a : ℕ → ℝ := fun n ↦ ∫ ω,
    f (z + ω (dyadicStoppingTime σ n ω)) - f (z + ω 0) ∂μ
  let I : ℝ := ∫ ω, f (z + ω (σ ω)) - f (z + ω 0) ∂μ
  obtain ⟨M, hM⟩ := hsupp.exists_bound_of_continuous hf.continuous
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (0 : Euc d))
  have hmeas (n : ℕ) : AEStronglyMeasurable (fun ω : BrownianPath d ↦
      f (z + ω (dyadicStoppingTime σ n ω)) - f (z + ω 0)) μ := by
    have hm := measurable_brownian_random_evaluation (measurable_nnreal_brownian_stopping
      (isStoppingTime_dyadicStoppingTime _ hσ n))
    exact ((hf.continuous.measurable.comp (measurable_const.add hm)).sub
      (hf.continuous.measurable.comp (measurable_const.add
        (continuous_eval_const (0 : ℝ≥0)).measurable))).aestronglyMeasurable
  have hbound (n : ℕ) : ∀ᵐ ω ∂μ,
      ‖f (z + ω (dyadicStoppingTime σ n ω)) - f (z + ω 0)‖ ≤ 2 * M := by
    filter_upwards [] with ω
    exact (norm_sub_le _ _).trans
      (by linarith [hM (z + ω (dyadicStoppingTime σ n ω)), hM (z + ω 0)])
  have hlim : Tendsto a atTop (𝓝 I) := by
    apply tendsto_integral_of_dominated_convergence (fun _ ↦ 2 * M) hmeas (integrable_const _)
      hbound
    filter_upwards [] with ω
    exact (((hf.continuous.comp (continuous_const.add ω.continuous)).tendsto (σ ω)).comp
      (tendsto_dyadicStoppingTime σ ω)).sub tendsto_const_nhds
  have hs : Tendsto (fun n : ℕ ↦ ((1 / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)) atTop (𝓝 0) := by
    simpa [one_div, Function.comp_def] using (tendsto_inv_atTop_zero.comp
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)))
  have hI (ε : ℝ) (hε : 0 < ε) : |I| ≤ ε * (d : ℝ) * ((N : ℝ) + 1) := by
    obtain ⟨C, hC, hsum⟩ :=
      standardBrownianLaw_dyadic_stopped_harmonic_bound hμ hf hsupp hh hε
    have hboundn (n : ℕ) : |a n| ≤ ε * (d : ℝ) * ((N : ℝ) + 1) +
        C * ((N : ℝ) + 1) * ((1 / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) := by
      have hb := (hsum σ hσ N hN z hstay n).2
      have hlength : (⌈N * (2 : ℝ≥0) ^ n⌉₊ : ℝ) *
          ((1 / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) ≤ (N : ℝ) + 1 := by
        exact_mod_cast dyadic_grid_length_le N n
      have hs0 : 0 ≤ ((1 / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
      apply hb.trans
      calc
        _ = (ε * (d : ℝ)) * ((⌈N * (2 : ℝ≥0) ^ n⌉₊ : ℝ) *
              ((1 / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)) +
            (C * ((1 / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)) *
              ((⌈N * (2 : ℝ≥0) ^ n⌉₊ : ℝ) * ((1 / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)) := by
          ring
        _ ≤ (ε * (d : ℝ)) * ((N : ℝ) + 1) +
            (C * ((1 / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)) * ((N : ℝ) + 1) :=
          add_le_add (mul_le_mul_of_nonneg_left hlength (by positivity))
            (mul_le_mul_of_nonneg_left hlength (mul_nonneg hC hs0))
        _ = _ := by ring
    have hrhs : Tendsto (fun n : ℕ ↦ ε * (d : ℝ) * ((N : ℝ) + 1) +
        C * ((N : ℝ) + 1) * ((1 / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)) atTop
        (𝓝 (ε * (d : ℝ) * ((N : ℝ) + 1))) := by
      simpa only [mul_zero, add_zero] using tendsto_const_nhds.add (tendsto_const_nhds.mul hs)
    exact le_of_tendsto_of_tendsto' (continuous_abs.tendsto I |>.comp hlim) hrhs hboundn
  have hzero : |I| = 0 := by
    apply le_antisymm _ (abs_nonneg I)
    by_contra hpos
    have hpos : 0 < |I| := lt_of_not_ge hpos
    let K : ℝ := (d : ℝ) * ((N : ℝ) + 1)
    have hK : 0 ≤ K := by dsimp [K]; positivity
    let ε : ℝ := |I| / (2 * (K + 1))
    have hε : 0 < ε := by dsimp [ε]; positivity
    have heq : ε * (K + 1) = |I| / 2 := by dsimp [ε]; field_simp
    have hb := hI ε hε
    change |I| ≤ ε * (d : ℝ) * ((N : ℝ) + 1) at hb
    have hb' : |I| ≤ ε * K := by dsimp [K]; nlinarith [hb]
    nlinarith
  exact abs_eq_zero.mp hzero

namespace BrownianStoppedLimitExample

/-- Concrete mesh check of `dyadic_grid_length_le`: at `N = 1 / 2` and level `n = 2`, the mesh is
`1 / 4`, the dyadic grid length is `1 / 2`, and the bound is `N + 1 = 3 / 2`. -/
theorem dyadic_grid_length_le_concrete :
    (⌈(1 / 2 : ℝ≥0) * (2 : ℝ≥0) ^ 2⌉₊ : ℝ≥0) * (1 / (2 : ℝ≥0) ^ 2) ≤
      1 / 2 + 1 :=
  dyadic_grid_length_le (1 / 2) 2

/-- The bounded stopped harmonic difference for the constant stopping time `c`. The law `μ` and
the harmonic function `f` on `U` are binders, and the stopping time is `fun _ ↦ c`. -/
theorem standardBrownianLaw_bounded_stopped_harmonic_difference_const {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) (hsupp : HasCompactSupport f)
    {U : Set (Euc d)} (hh : IsHarmonicOn f U) (c : ℝ≥0) (z : Euc d)
    (hstay : ∀ (ω : BrownianPath d) (t : ℝ≥0), t < c → z + ω t ∈ U) :
    (∫ ω, f (z + ω c) - f (z + ω 0) ∂μ) = 0 :=
  standardBrownianLaw_bounded_stopped_harmonic_difference hμ hf hsupp hh
    (isStoppingTime_const (brownianNaturalFiltration d) c) c (fun _ ↦ le_rfl) z hstay

/-- The bounded stopped harmonic difference for the exit time of an open set `U` from the shifted
path `t ↦ z + ω t`, truncated at `N`. The path hypothesis of the main theorem holds for every
path, and `U` is an arbitrary open set on which `f` is harmonic. -/
theorem standardBrownianLaw_truncated_exit_stopped_harmonic_difference {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) (hsupp : HasCompactSupport f)
    {U : Set (Euc d)} (hU : IsOpen U) (hh : IsHarmonicOn f U) (N : ℝ≥0) (z : Euc d) :
    (∫ ω, f (z + ω (ENNReal.toNNReal (min (continuousExitTime U z ω) N))) - f (z + ω 0) ∂μ) =
      0 := by
  have hfin (ω : BrownianPath d) : min (continuousExitTime U z ω) (N : ℝ≥0∞) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _)
  have hcoe : (fun ω ↦ ((ENNReal.toNNReal (min (continuousExitTime U z ω) N) : ℝ≥0) :
      ℝ≥0∞)) = fun ω ↦ min (continuousExitTime U z ω) (N : ℝ≥0∞) :=
    funext fun ω ↦ ENNReal.coe_toNNReal (hfin ω)
  have hσ : IsStoppingTime (brownianNaturalFiltration d)
      (fun ω ↦ ((ENNReal.toNNReal (min (continuousExitTime U z ω) N) : ℝ≥0) : ℝ≥0∞)) := by
    rw [hcoe]
    exact (isStoppingTime_continuousExitTime hU z).min_const N
  refine standardBrownianLaw_bounded_stopped_harmonic_difference hμ hf hsupp hh hσ N ?_ z ?_
  · intro ω
    rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal (hfin ω)]
    exact min_le_right _ _
  · intro ω t ht
    have h1 : (t : ℝ≥0∞) < min (continuousExitTime U z ω) N := by
      have h2 := ENNReal.coe_lt_coe.mpr ht
      rwa [ENNReal.coe_toNNReal (hfin ω)] at h2
    exact mem_of_lt_continuousExitTime (lt_of_lt_of_le h1 (min_le_left _ _))

end BrownianStoppedLimitExample

end LatticeProb
