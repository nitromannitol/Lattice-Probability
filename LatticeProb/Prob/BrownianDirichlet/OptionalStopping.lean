import LatticeProb.Prob.BrownianDirichlet.Discounted
import LatticeProb.Prob.BrownianStoppedLimit

/-!
# Bounded stopping for discounted Brownian compensation

The past-event identity telescopes on upper dyadic grids. Pathwise continuity and
compact-support bounds then give the identity at every bounded stopping time.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

noncomputable section

namespace LatticeProb

/-- The discounted observable is continuous in time along every continuous path. -/
lemma continuous_discountedObservable {d : ℕ} {f : Euc d → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (σ μd : ℝ) (x : Euc d) (ω : BrownianPath d) :
    Continuous (fun t ↦ discountedObservable f σ μd x t ω) := by
  obtain ⟨hD, _⟩ := continuous_compactSupport_discountedForcing hf hc σ μd
  have hg : Continuous (fun s : ℝ ↦ Real.exp (-μd * s) *
      discountedForcing f σ μd (x + σ • ω s.toNNReal)) := by
    apply Continuous.mul
    · fun_prop
    · exact hD.comp (by fun_prop)
  exact (by fun_prop : Continuous (fun t : ℝ≥0 ↦
    Real.exp (-μd * (t : ℝ)) * f (x + σ • ω t))).add
    ((intervalIntegral.continuous_primitive (fun a b ↦ hg.intervalIntegrable a b) 0).comp
      NNReal.continuous_coe)

/-- On every upper dyadic grid the stopped compensated increment has zero integral. -/
lemma integral_discounted_dyadic_difference {d : ℕ} {μ : Measure (BrownianPath d)}
    (hμ : IsStandardBrownianLaw μ) {f : Euc d → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) {σ μd : ℝ}
    (hσ : 0 < σ) (hμd : 0 < μd) (x : Euc d) {ζ : BrownianPath d → ℝ≥0}
    (hζ : IsStoppingTime (brownianNaturalFiltration d) (fun ω ↦ (ζ ω : ℝ≥0∞)))
    (N : ℝ≥0) (hN : ∀ ω, ζ ω ≤ N) (n : ℕ) :
    Integrable (fun ω ↦ discountedObservable f σ μd x (dyadicStoppingTime ζ n ω) ω -
      discountedObservable f σ μd x 0 ω) μ ∧
    (∫ ω, discountedObservable f σ μd x (dyadicStoppingTime ζ n ω) ω -
      discountedObservable f σ μd x 0 ω ∂μ) = 0 := by
  classical
  let D : ℕ → BrownianPath d → ℝ := fun j ↦
    {ω | (j : ℝ≥0) / (2 : ℝ≥0) ^ n < ζ ω}.indicator (fun ω ↦
      discountedObservable f σ μd x ((j + 1 : ℕ) / (2 : ℝ≥0) ^ n) ω -
        discountedObservable f σ μd x ((j : ℝ≥0) / (2 : ℝ≥0) ^ n) ω)
  have hD (j : ℕ) : Integrable (D j) μ ∧ (∫ ω, D j ω ∂μ) = 0 := by
    let s : ℝ≥0 := (j : ℝ≥0) / (2 : ℝ≥0) ^ n
    let t : ℝ≥0 := ((j + 1 : ℕ) / (2 : ℝ≥0) ^ n)
    have hst : s ≤ t := by
      exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ j) (by positivity)
    have hH := measurableSet_before_nnreal_stopping hζ s
    have hHa := (brownianNaturalFiltration d).le s _ hH
    have hi := integrable_discountedObservable hμ hf hc hμd σ x t
    have hj := integrable_discountedObservable hμ hf hc hμd σ x s
    refine ⟨(hi.sub hj).indicator hHa, ?_⟩
    change (∫ ω, {ω | s < ζ ω}.indicator (fun ω ↦
      discountedObservable f σ μd x t ω - discountedObservable f σ μd x s ω) ω ∂μ) = 0
    rw [integral_indicator hHa, integral_sub hi.integrableOn hj.integrableOn,
      setIntegral_discounted_past hμ hf hc hσ hμd x hst hH, sub_self]
  have heq : (fun ω ↦ discountedObservable f σ μd x (dyadicStoppingTime ζ n ω) ω -
      discountedObservable f σ μd x 0 ω) =
      fun ω ↦ ∑ j ∈ Finset.range ⌈N * (2 : ℝ≥0) ^ n⌉₊, D j ω := by
    funext ω
    simpa only [D, indicator_apply, mem_setOf_eq] using
      dyadic_stopped_difference_eq_sum (fun ω t ↦ discountedObservable f σ μd x t ω)
        ζ hN n ω
  rw [heq]
  refine ⟨integrable_finsetSum _ (fun j _ ↦ (hD j).1), ?_⟩
  rw [integral_finsetSum _ (fun j _ ↦ (hD j).1)]
  have hz (j : ℕ) : (∫ ω, D j ω ∂μ) = 0 := (hD j).2
  simp only [hz, Finset.sum_const_zero]

/-- Discounted compensation preserves expectation at every bounded stopping time. -/
theorem integral_discounted_stopped {d : ℕ} {μ : Measure (BrownianPath d)}
    (hμ : IsStandardBrownianLaw μ) {f : Euc d → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) {σ μd : ℝ}
    (hσ : 0 < σ) (hμd : 0 < μd) (x : Euc d) {ζ : BrownianPath d → ℝ≥0}
    (hζ : IsStoppingTime (brownianNaturalFiltration d) (fun ω ↦ (ζ ω : ℝ≥0∞)))
    (N : ℝ≥0) (hN : ∀ ω, ζ ω ≤ N) :
    (∫ ω, discountedObservable f σ μd x (ζ ω) ω ∂μ) = f x := by
  letI : IsProbabilityMeasure μ := hμ.1
  obtain ⟨K, hK⟩ := hc.exists_bound_of_continuous hf.continuous
  obtain ⟨hD, hDc⟩ := continuous_compactSupport_discountedForcing hf hc σ μd
  obtain ⟨L, hL⟩ := hDc.exists_bound_of_continuous hD
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL (0 : Euc d))
  have hgrid (n : ℕ) (ω : BrownianPath d) : dyadicStoppingTime ζ n ω ≤ N + 1 := by
    apply le_trans _ (dyadic_grid_length_le N n)
    rw [dyadicStoppingTime, mul_one_div]
    exact div_le_div_of_nonneg_right
      (Nat.cast_le.mpr (Nat.ceil_mono
        (mul_le_mul_of_nonneg_right (hN ω) (by positivity)))) (by positivity)
  have hi (n : ℕ) := integral_discounted_dyadic_difference hμ hf hc hσ hμd x hζ N hN n
  have hbound (n : ℕ) : ∀ᵐ ω ∂μ,
      ‖discountedObservable f σ μd x (dyadicStoppingTime ζ n ω) ω -
        discountedObservable f σ μd x 0 ω‖ ≤ 2 * K + ((N : ℝ) + 1) * L := by
    filter_upwards [] with ω
    have hb := abs_discountedObservable_le hμd hK hL x (dyadicStoppingTime ζ n ω) ω
    have hz := abs_discountedObservable_le hμd hK hL x 0 ω
    have ht : (dyadicStoppingTime ζ n ω : ℝ) ≤ (N : ℝ) + 1 := by
      exact_mod_cast hgrid n ω
    have hm := mul_le_mul_of_nonneg_right ht hL0
    have hn := norm_sub_le (discountedObservable f σ μd x
      (dyadicStoppingTime ζ n ω) ω) (discountedObservable f σ μd x 0 ω)
    simp only [Real.norm_eq_abs, NNReal.coe_zero, zero_mul, add_zero] at hn hz ⊢
    linarith
  have hconv : ∀ᵐ ω ∂μ, Tendsto (fun n ↦
      discountedObservable f σ μd x (dyadicStoppingTime ζ n ω) ω -
        discountedObservable f σ μd x 0 ω) atTop
      (𝓝 (discountedObservable f σ μd x (ζ ω) ω -
        discountedObservable f σ μd x 0 ω)) :=
    Filter.Eventually.of_forall (fun ω ↦
      (((continuous_discountedObservable hf hc σ μd x ω).tendsto (ζ ω)).comp
        (tendsto_dyadicStoppingTime ζ ω)).sub tendsto_const_nhds)
  have hlim := tendsto_integral_of_dominated_convergence
    (fun _ ↦ 2 * K + ((N : ℝ) + 1) * L)
    (fun n ↦ (hi n).1.aestronglyMeasurable) (integrable_const _) hbound hconv
  have hzero : (∫ ω, discountedObservable f σ μd x (ζ ω) ω -
      discountedObservable f σ μd x 0 ω ∂μ) = 0 := by
    have hz (n : ℕ) : (∫ ω, discountedObservable f σ μd x
        (dyadicStoppingTime ζ n ω) ω - discountedObservable f σ μd x 0 ω ∂μ) = 0 :=
      (hi n).2
    exact tendsto_nhds_unique hlim (by simpa only [hz] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0)))
  have hdiff : Integrable (fun ω ↦ discountedObservable f σ μd x (ζ ω) ω -
      discountedObservable f σ μd x 0 ω) μ := by
    apply (integrable_const (2 * K + ((N : ℝ) + 1) * L)).mono'
      (aestronglyMeasurable_of_tendsto_ae _
        (fun n ↦ (hi n).1.aestronglyMeasurable) hconv)
    filter_upwards [hconv, ae_all_iff.mpr hbound] with ω hω hb
    exact le_of_tendsto hω.norm (Filter.Eventually.of_forall hb)
  have hstop : Integrable (fun ω ↦ discountedObservable f σ μd x (ζ ω) ω) μ := by
    exact (hdiff.add (integrable_discountedObservable hμ hf hc hμd σ x 0)).congr
      (Filter.Eventually.of_forall (fun ω ↦ sub_add_cancel _ _))
  rw [integral_sub hstop (integrable_discountedObservable hμ hf hc hμd σ x 0),
    integral_discounted hμ hf hc hσ] at hzero
  exact sub_eq_zero.mp hzero

/-- A nonzero smooth bump and an existing Brownian law realize bounded stopping at unit time. -/
theorem exists_brownian_bump_discounted_stopped :
    let b : ContDiffBump (0 : Euc 1) := ⟨1, 2, one_pos, one_lt_two⟩
    ∃ μ : Measure (BrownianPath 1), IsStandardBrownianLaw μ ∧ b (0 : Euc 1) = 1 ∧
      (∫ ω, discountedObservable (⇑b) 1 1 (0 : Euc 1)
        ((fun _ : BrownianPath 1 ↦ 1) ω) ω ∂μ) = 1 := by
  intro b
  obtain ⟨μ, hμ⟩ := BrownianPathCoordsExample.exists_isStandardBrownianLaw_one
  have hb : b (0 : Euc 1) = 1 := b.one_of_mem_closedBall (by simp [b])
  refine ⟨μ, hμ, hb, ?_⟩
  exact (integral_discounted_stopped hμ b.contDiff b.hasCompactSupport
    zero_lt_one zero_lt_one (0 : Euc 1)
    (isStoppingTime_const (brownianNaturalFiltration 1) 1) 1 (fun _ ↦ le_rfl)).trans hb

end LatticeProb
