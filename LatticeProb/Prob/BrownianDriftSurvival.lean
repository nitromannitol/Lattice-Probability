/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib
import LatticeProb.Prob.BrownianExpMartingale
import LatticeProb.Prob.GamblersRuinOvershoot

/-!
# Brownian motion with positive drift: the survival probability

For a pre-Brownian motion `B` with continuous paths, `c > 0` and `δ > 0`, the probability that
`B t + c t` stays above `-δ` for all `t ≥ 0` equals `1 - exp (-2 c δ)`.

The estimate from below is the maximal inequality for the exponential martingale
(`LatticeProb.measure_exists_drift_lt_le`).  The estimate from above compares the Brownian motion
with its dyadic skeleton: the first passage of the skeleton below `-δ` overshoots by at most `η`
unless one Gaussian step is larger than `η` (a Chernoff bound, using that the step is independent
of the past), and the exponential martingale is small on the event of survival up to a large time
(`LatticeProb.exp_mul_mul_le_measureReal_exists_le`).  Letting the mesh tend to `0`, then the time
to `∞`, then `η` to `0` gives the upper bound.
-/

open MeasureTheory ProbabilityTheory Filter MeasurableSpace Topology
open scoped ENNReal NNReal

namespace LatticeProb

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The natural filtration of a real process, sampled along a monotone sequence of times. -/
def gridFiltration (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t)) (t : ℕ → ℝ≥0)
    (ht : Monotone t) : Filtration ℕ mΩ :=
  ⟨fun k => brownianFiltration B hm (t k), fun _ _ h => (brownianFiltration B hm).mono (ht h),
    fun _ => (brownianFiltration B hm).le _⟩

/-- **One Gaussian step.**  Between times `s < t` (with `t - s = h`), the exponential martingale
integrated over the event that the drifted process drops by more than `η` is at most
`exp (-η² / (2 h) + 2 c η)`. -/
theorem setIntegral_exp_drift_step_le (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    {c : ℝ} (hc : 0 < c) {s t : ℝ≥0} {h : ℝ} (hh : (t : ℝ) - s = h) (hpos : 0 < h) {η : ℝ}
    (hη : 0 < η) :
    ∫ ω in {ω | (B t ω + c * t) - (B s ω + c * s) < -η},
        Real.exp (-(2 * c) * (B t ω + c * t)) ∂P ≤
      Real.exp (-(η ^ 2 / (2 * h)) + 2 * c * η) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hst : s ≤ t := by
    have : (s : ℝ) < t := by linarith
    exact_mod_cast this.le
  set Z : Ω → ℝ := B t - B s with hZ
  set Mf : Ω → ℝ := fun ω => Real.exp (-(2 * c) * (B s ω + c * s)) with hMf
  set F : ℝ → ℝ := Set.indicator {z : ℝ | z < -η}
    (fun z => Real.exp (-(2 * c ^ 2 * h)) * Real.exp (-(2 * c) * z)) with hF
  have hFm : Measurable F :=
    Measurable.indicator (by fun_prop) (measurableSet_lt measurable_id measurable_const)
  have hFnn : ∀ z, 0 ≤ F z := fun z => by
    simp only [hF, Set.indicator]
    split_ifs
    · positivity
    · exact le_rfl
  have hZm : Measurable Z := (hm t).sub (hm s)
  have hMfnn : ∀ ω, 0 ≤ Mf ω := fun ω => (Real.exp_pos _).le
  have hSm : MeasurableSet {ω | (B t ω + c * t) - (B s ω + c * s) < -η} :=
    measurableSet_lt (((hm t).add_const _).sub ((hm s).add_const _)) measurable_const
  -- independence of `Mf` and `F ∘ Z`
  have hMfmeas : Measurable[brownianFiltration B hm s] Mf :=
    ((Real.continuous_exp.comp (by fun_prop :
      Continuous fun x : ℝ => -(2 * c) * (x + c * s))).comp_stronglyMeasurable
      (Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable) s)).measurable
  have hind : IndepFun Mf (F ∘ Z) P := by
    have h0 := brownian_indep_filtration_sub hB hm hst
    have h1 : Indep (MeasurableSpace.comap Mf inferInstance)
        (MeasurableSpace.comap Z inferInstance) P :=
      indep_of_indep_of_le_left h0 hMfmeas.comap_le
    have h2 : MeasurableSpace.comap (F ∘ Z) inferInstance ≤ MeasurableSpace.comap Z inferInstance := by
      rw [← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono hFm.comap_le
    exact indep_of_indep_of_le_right h1 h2
  -- the integral over the event is dominated by `∫ Mf * (F ∘ Z)`
  have hpt : ∀ ω, {ω | (B t ω + c * t) - (B s ω + c * s) < -η}.indicator
      (fun ω => Real.exp (-(2 * c) * (B t ω + c * t))) ω ≤ Mf ω * F (Z ω) := by
    intro ω
    by_cases hω : ω ∈ {ω | (B t ω + c * t) - (B s ω + c * s) < -η}
    · rw [Set.indicator_of_mem hω]
      have hZlt : Z ω < -η := by
        have : (B t ω + c * t) - (B s ω + c * s) = Z ω + c * h := by
          simp only [hZ, Pi.sub_apply]
          rw [← hh]
          ring
        have hω' : (B t ω + c * t) - (B s ω + c * s) < -η := hω
        nlinarith
      have hFZ : F (Z ω) = Real.exp (-(2 * c ^ 2 * h)) * Real.exp (-(2 * c) * Z ω) := by
        simp only [hF]
        rw [Set.indicator_of_mem (show Z ω ∈ {z : ℝ | z < -η} from hZlt)]
      rw [hFZ]
      refine le_of_eq ?_
      simp only [hMf, hZ, Pi.sub_apply, ← Real.exp_add]
      congr 1
      rw [← hh]
      ring
    · rw [Set.indicator_of_notMem hω]
      exact mul_nonneg (hMfnn ω) (hFnn _)
  have hFZint : Integrable (F ∘ Z) P := by
    refine Integrable.mono' ((brownian_integrable_exp_mul_sub hB (-(2 * c)) s t).const_mul
      (Real.exp (-(2 * c ^ 2 * h)))) (hFm.comp hZm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg (hFnn _)]
    simp only [hF, Set.indicator]
    split_ifs
    · simp only [hZ, Pi.sub_apply]
      exact le_rfl
    · exact mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have hMfint : Integrable Mf P := by
    have : Mf = fun ω => Real.exp (-(2 * c) * B s ω) * Real.exp (-(2 * c ^ 2 * s)) := by
      funext ω
      simp only [hMf, ← Real.exp_add]
      congr 1
      ring
    rw [this]
    exact (brownian_integrable_exp_mul hB _ s).mul_const _
  have hprodint : Integrable (Mf * (F ∘ Z)) P := hind.integrable_mul hMfint hFZint
  -- Chernoff bound for `∫ F ∘ Z`
  have hch : ∫ ω, F (Z ω) ∂P ≤ Real.exp (-(η ^ 2 / (2 * h)) + 2 * c * η) := by
    set a : ℝ := -(2 * c + η / h) with ha
    set K : ℝ := Real.exp (-(2 * c ^ 2 * h) - η ^ 2 / h) with hK
    have hdom : ∀ ω, F (Z ω) ≤ K * Real.exp (a * (B t ω - B s ω)) := by
      intro ω
      simp only [hF, Set.indicator]
      split_ifs with hz
      · have hz' : Z ω < -η := hz
        simp only [hZ, Pi.sub_apply] at hz' ⊢
        rw [hK, ← Real.exp_add, ← Real.exp_add]
        refine Real.exp_le_exp.2 ?_
        have e : -(η ^ 2 / h) - η / h * (B t ω - B s ω) = η / h * (-((B t ω - B s ω) + η)) := by
          ring
        have : 0 ≤ η / h * (-((B t ω - B s ω) + η)) :=
          mul_nonneg (div_pos hη hpos).le (by linarith)
        rw [ha]
        nlinarith
      · positivity
    calc ∫ ω, F (Z ω) ∂P ≤ ∫ ω, K * Real.exp (a * (B t ω - B s ω)) ∂P :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => hFnn _)
            ((brownian_integrable_exp_mul_sub hB a s t).const_mul K)
            (Filter.Eventually.of_forall hdom)
      _ = K * Real.exp (((t : ℝ) - s) * a ^ 2 / 2) := by
          rw [integral_const_mul, brownian_integral_exp_mul_sub hB a hst]
      _ = Real.exp (-(η ^ 2 / (2 * h)) + 2 * c * η) := by
          rw [hK, ← Real.exp_add, hh]
          congr 1
          rw [ha]
          field_simp
          ring
  have hMf1 : ∫ ω, Mf ω ∂P = 1 := integral_exp_drift hB c s
  calc ∫ ω in {ω | (B t ω + c * t) - (B s ω + c * s) < -η},
          Real.exp (-(2 * c) * (B t ω + c * t)) ∂P
      = ∫ ω, {ω | (B t ω + c * t) - (B s ω + c * s) < -η}.indicator
          (fun ω => Real.exp (-(2 * c) * (B t ω + c * t))) ω ∂P := (integral_indicator hSm).symm
    _ ≤ ∫ ω, (Mf * (F ∘ Z)) ω ∂P :=
        integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun ω => Set.indicator_nonneg
            (fun ω _ => (Real.exp_pos _).le) ω) hprodint (Filter.Eventually.of_forall hpt)
    _ = (∫ ω, Mf ω ∂P) * ∫ ω, (F ∘ Z) ω ∂P :=
        hind.integral_mul_eq_mul_integral hMfint.aestronglyMeasurable hFZint.aestronglyMeasurable
    _ ≤ _ := by
        rw [hMf1, one_mul]
        exact hch

/-- **The exponential martingale on survival.**  The integral of `exp (-2 c (B t + c t))` over
the event that `B t + c t > -δ` is at most `exp (c δ - c² t / 2)`. -/
theorem setIntegral_exp_drift_survival_le (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) {c : ℝ} (hc : 0 < c) (t : ℝ≥0) (δ : ℝ) :
    ∫ ω in {ω | -δ < B t ω + c * t}, Real.exp (-(2 * c) * (B t ω + c * t)) ∂P ≤
      Real.exp (c * δ - c ^ 2 * t / 2) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hSm : MeasurableSet {ω | -δ < B t ω + c * t} :=
    measurableSet_lt measurable_const ((hm t).add_const _)
  have hHint : Integrable (fun ω => Real.exp (c * δ - c ^ 2 * t) * Real.exp (-c * B t ω)) P :=
    (brownian_integrable_exp_mul hB (-c) t).const_mul _
  have hdom : ∀ ω ∈ {ω | -δ < B t ω + c * t}, Real.exp (-(2 * c) * (B t ω + c * t)) ≤
      Real.exp (c * δ - c ^ 2 * t) * Real.exp (-c * B t ω) := by
    intro ω hω
    have hω' : -δ < B t ω + c * t := hω
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    nlinarith
  have hint0 : Integrable (fun ω => Real.exp (-(2 * c) * (B t ω + c * t))) P := by
    have : (fun ω => Real.exp (-(2 * c) * (B t ω + c * t))) =
        fun ω => Real.exp (-(2 * c) * B t ω) * Real.exp (-(2 * c ^ 2 * t)) := by
      funext ω
      simp only [← Real.exp_add]
      congr 1
      ring
    rw [this]
    exact (brownian_integrable_exp_mul hB _ t).mul_const _
  calc ∫ ω in {ω | -δ < B t ω + c * t}, Real.exp (-(2 * c) * (B t ω + c * t)) ∂P
      ≤ ∫ ω in {ω | -δ < B t ω + c * t},
          Real.exp (c * δ - c ^ 2 * t) * Real.exp (-c * B t ω) ∂P :=
        setIntegral_mono_on hint0.integrableOn hHint.integrableOn hSm hdom
    _ ≤ ∫ ω, Real.exp (c * δ - c ^ 2 * t) * Real.exp (-c * B t ω) ∂P :=
        setIntegral_le_integral hHint (Filter.Eventually.of_forall fun ω =>
          mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    _ = Real.exp (c * δ - c ^ 2 * t / 2) := by
        rw [integral_const_mul, brownian_integral_exp_mul hB, ← Real.exp_add]
        congr 1
        ring

/-- The dyadic grid `k / 2 ^ N` in `ℝ≥0`. -/
noncomputable def dyadicGrid (N k : ℕ) : ℝ≥0 := (k : ℝ≥0) / 2 ^ N

theorem dyadicGrid_mono (N : ℕ) : Monotone (dyadicGrid N) := fun a b h => by
  simp only [dyadicGrid]
  gcongr

theorem coe_dyadicGrid (N k : ℕ) : (dyadicGrid N k : ℝ) = (k : ℝ) / 2 ^ N := by
  simp [dyadicGrid]

theorem dyadicGrid_zero (N : ℕ) : dyadicGrid N 0 = 0 := by simp [dyadicGrid]

theorem dyadicGrid_succ_sub (N k : ℕ) :
    (dyadicGrid N (k + 1) : ℝ) - dyadicGrid N k = ((2 : ℝ) ^ N)⁻¹ := by
  rw [coe_dyadicGrid, coe_dyadicGrid]
  push_cast
  field_simp
  ring

/-- **Gambler's ruin for the dyadic skeleton.**  For `c, δ, η > 0`, the probability that the
skeleton `B (k / 2 ^ N) + c k / 2 ^ N`, `k ≤ T 2 ^ N`, goes down to `-δ` is at least
`exp (-2 c (δ + η)) (1 - T 2 ^ N q - ρ)`, where `q = exp (-η² 2 ^ N / 2 + 2 c η)` bounds the
cost of one step of size more than `η` and `ρ = exp (c δ - c² T / 2)` bounds the
exponential martingale on survival. -/
theorem exp_mul_mul_le_measureReal_exists_grid (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) {c : ℝ} (hc : 0 < c) {δ : ℝ} (hδ : 0 < δ) {η : ℝ}
    (hη : 0 < η) (N T : ℕ) :
    Real.exp (-(2 * c * (δ + η))) *
        (1 - ((T * 2 ^ N : ℕ) : ℝ) * Real.exp (-(η ^ 2 * 2 ^ N / 2) + 2 * c * η) -
          Real.exp (c * δ - c ^ 2 * T / 2)) ≤
      P.real {ω | ∃ k ≤ T * 2 ^ N, B (dyadicGrid N k) ω + c * dyadicGrid N k ≤ -δ} := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let g : ℕ → ℝ≥0 := dyadicGrid N
  let 𝒢 : Filtration ℕ mΩ := gridFiltration B hm g (dyadicGrid_mono N)
  let Y : ℕ → Ω → ℝ := fun k ω => B (g k) ω + c * g k
  let M : ℕ → Ω → ℝ := fun k ω => Real.exp (-(2 * c) * Y k ω)
  have hmart : Martingale M 𝒢 P :=
    ⟨fun k => (martingale_exp_drift hB hm c).1 (g k),
      fun i j hij => (martingale_exp_drift hB hm c).2 (g i) (g j) (dyadicGrid_mono N hij)⟩
  have hY : ∀ k, Measurable[𝒢 k] (Y k) := fun k =>
    ((Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable) (g k)).measurable
      ).add_const _
  have hY0 : ∀ᵐ ω ∂P, -δ < Y 0 ω := by
    filter_upwards [hB.eval_zero_ae_eq_zero] with ω hω
    have : g 0 = 0 := dyadicGrid_zero N
    simp only [Y, this, hω]
    simpa using hδ
  have hq : ∀ k < T * 2 ^ N, ∫ ω in {ω | Y (k + 1) ω - Y k ω < -η}, M (k + 1) ω ∂P ≤
      Real.exp (-(η ^ 2 * 2 ^ N / 2) + 2 * c * η) := by
    intro k _
    have hstep := setIntegral_exp_drift_step_le hB hm hc (s := g k) (t := g (k + 1))
      (h := ((2 : ℝ) ^ N)⁻¹) (dyadicGrid_succ_sub N k) (by positivity) hη
    have e : η ^ 2 / (2 * ((2 : ℝ) ^ N)⁻¹) = η ^ 2 * 2 ^ N / 2 := by
      field_simp
    rw [e] at hstep
    exact hstep
  have hρ : ∫ ω in survivalSet Y δ (T * 2 ^ N), M (T * 2 ^ N) ω ∂P ≤
      Real.exp (c * δ - c ^ 2 * T / 2) := by
    have hgT : (g (T * 2 ^ N) : ℝ) = T := by
      show (dyadicGrid N (T * 2 ^ N) : ℝ) = T
      rw [coe_dyadicGrid]
      push_cast
      field_simp
    have hbound := setIntegral_exp_drift_survival_le hB hm hc (g (T * 2 ^ N)) δ
    refine le_trans (le_trans ?_ hbound) (le_of_eq (by rw [hgT]))
    refine setIntegral_mono_set (f := fun ω => Real.exp (-(2 * c) *
      (B (g (T * 2 ^ N)) ω + c * (g (T * 2 ^ N) : ℝ)))) ?_
      (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le) ?_
    · exact (hmart.integrable (T * 2 ^ N)).integrableOn
    · refine Filter.Eventually.of_forall fun ω hω => ?_
      exact hω (T * 2 ^ N) le_rfl
  exact exp_mul_mul_le_measureReal_exists_le hmart hY (a := 2 * c) (fun k ω => rfl)
    (by positivity) (integral_exp_drift hB c (g 0)) hY0 η _ _ (T * 2 ^ N) hq hρ

/-- Survival up to a large time costs at least `exp (-2 c (δ + η)) (1 - T 2 ^ N q - ρ)`. -/
theorem measureReal_forall_drift_gt_le_aux (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) {c : ℝ} (hc : 0 < c) {δ : ℝ} (hδ : 0 < δ) {η : ℝ}
    (hη : 0 < η) (N T : ℕ) :
    P.real {ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} ≤
      1 - Real.exp (-(2 * c * (δ + η))) *
        (1 - ((T * 2 ^ N : ℕ) : ℝ) * Real.exp (-(η ^ 2 * 2 ^ N / 2) + 2 * c * η) -
          Real.exp (c * δ - c ^ 2 * T / 2)) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set S : Set Ω := {ω | ∀ k ≤ T * 2 ^ N, -δ < B (dyadicGrid N k) ω + c * dyadicGrid N k} with hS
  have hSm : MeasurableSet S := by
    simp only [hS, Set.ofPred_forall]
    exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      measurableSet_lt measurable_const ((hm _).add_const _)
  have hsub : {ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} ⊆ S := fun ω hω k _ => hω _
  have hcompl : {ω | ∃ k ≤ T * 2 ^ N, B (dyadicGrid N k) ω + c * dyadicGrid N k ≤ -δ} = Sᶜ := by
    ext ω
    simp [hS, not_lt]
  have h1 := exp_mul_mul_le_measureReal_exists_grid hB hm hc hδ hη N T
  rw [hcompl, probReal_compl_eq_one_sub hSm] at h1
  have h2 : P.real {ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} ≤ P.real S := measureReal_mono hsub
  linarith

lemma tendsto_two_pow_mul_exp_neg {b : ℝ} (hb : 0 < b) :
    Tendsto (fun N : ℕ => (2 : ℝ) ^ N * Real.exp (-(b * 2 ^ N))) atTop (𝓝 0) := by
  have hx : Tendsto (fun N : ℕ => b * (2 : ℝ) ^ N) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).const_mul_atTop hb
  have h1 := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hx).const_mul b⁻¹
  rw [mul_zero] at h1
  refine h1.congr fun N => ?_
  simp only [Function.comp_apply, pow_one]
  field_simp

/-- The limit argument: if `p ≤ 1 - e^{-2c(δ+η)} (1 - T 2^N q - ρ)` for all `N`, `T`, `η > 0`
then `p ≤ 1 - e^{-2cδ}`. -/
theorem le_one_sub_exp_of_forall {c δ p : ℝ} (hc : 0 < c)
    (hp : ∀ (N T : ℕ) (η : ℝ), 0 < η → p ≤ 1 - Real.exp (-(2 * c * (δ + η))) *
        (1 - ((T * 2 ^ N : ℕ) : ℝ) * Real.exp (-(η ^ 2 * 2 ^ N / 2) + 2 * c * η) -
          Real.exp (c * δ - c ^ 2 * T / 2))) :
    p ≤ 1 - Real.exp (-(2 * c * δ)) := by
  -- first `N → ∞`
  have hA : ∀ η : ℝ, 0 < η → ∀ T : ℕ, p ≤ 1 - Real.exp (-(2 * c * (δ + η))) *
      (1 - Real.exp (c * δ - c ^ 2 * T / 2)) := by
    intro η hη T
    have hb : 0 < η ^ 2 / 2 := by positivity
    have hX : Tendsto (fun N : ℕ => ((T * 2 ^ N : ℕ) : ℝ) *
        Real.exp (-(η ^ 2 * 2 ^ N / 2) + 2 * c * η)) atTop (𝓝 0) := by
      have h0 := (tendsto_two_pow_mul_exp_neg hb).const_mul ((T : ℝ) * Real.exp (2 * c * η))
      rw [mul_zero] at h0
      refine h0.congr fun N => ?_
      push_cast
      rw [Real.exp_add]
      have : -(η ^ 2 * 2 ^ N / 2) = -(η ^ 2 / 2 * 2 ^ N) := by ring
      rw [this]
      ring
    have hlim := (((tendsto_const_nhds (x := (1 : ℝ))).sub hX).sub
      (tendsto_const_nhds (x := Real.exp (c * δ - c ^ 2 * T / 2)))).const_mul
      (Real.exp (-(2 * c * (δ + η)))) |>.const_sub 1
    simp only [sub_zero] at hlim
    exact ge_of_tendsto' hlim fun N => hp N T η hη
  -- then `T → ∞`
  have hB : ∀ η : ℝ, 0 < η → p ≤ 1 - Real.exp (-(2 * c * (δ + η))) := by
    intro η hη
    have hρ : Tendsto (fun T : ℕ => Real.exp (c * δ - c ^ 2 * T / 2)) atTop (𝓝 0) := by
      have hr : Tendsto (fun T : ℕ => (Real.exp (-(c ^ 2 / 2))) ^ T) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos _).le
          (by simpa using Real.exp_lt_exp.2 (show -(c ^ 2 / 2) < 0 by nlinarith))
      have := hr.const_mul (Real.exp (c * δ))
      rw [mul_zero] at this
      refine this.congr fun T => ?_
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    have hlim := ((tendsto_const_nhds (x := (1 : ℝ))).sub hρ).const_mul
      (Real.exp (-(2 * c * (δ + η)))) |>.const_sub 1
    simp only [sub_zero, mul_one] at hlim
    exact ge_of_tendsto' hlim fun T => hA η hη T
  -- finally `η → 0`
  have hcont : Continuous fun η : ℝ => 1 - Real.exp (-(2 * c * (δ + η))) := by fun_prop
  have hlim := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  simp only [add_zero] at hlim
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun η hη => hB η hη)

/-- **Upper bound for the survival probability.**  For `c, δ > 0`, the probability that
`B t + c t > -δ` for all `t` is at most `1 - exp (-2 c δ)`. -/
theorem measure_forall_drift_gt_le (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    {c : ℝ} (hc : 0 < c) {δ : ℝ} (hδ : 0 < δ) :
    P {ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} ≤ ENNReal.ofReal (1 - Real.exp (-(2 * c * δ))) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hnn : 0 ≤ 1 - Real.exp (-(2 * c * δ)) :=
    sub_nonneg.2 (Real.exp_le_one_iff.2 (by nlinarith))
  rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hnn]
  exact le_one_sub_exp_of_forall hc fun N T η hη =>
    measureReal_forall_drift_gt_le_aux hB hm hc hδ hη N T

/-- **Lower bound for the survival probability** (continuous paths): the probability that
`B t + c t > -δ` for all `t` is at least `1 - exp (-2 c δ)`. -/
theorem le_measure_forall_drift_gt (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) {c : ℝ} (hc : 0 < c) (δ : ℝ) :
    ENNReal.ofReal (1 - Real.exp (-(2 * c * δ))) ≤ P {ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  rw [← ENNReal.ofReal_toReal (measure_ne_top P {ω | ∀ t : ℝ≥0, -δ < B t ω + c * t})]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : ∀ δ' : ℝ, δ' < δ → 1 - Real.exp (-(2 * c * δ')) ≤
      P.real {ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} := by
    intro δ' hδ'
    set A : Set Ω := {ω | ∃ t : ℝ≥0, B t ω + c * t < -δ'} with hA
    have hAle : P.real A ≤ Real.exp (-(2 * c * δ')) :=
      ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le
        (measure_exists_drift_lt_le hB hm hcont hc δ')
    have hsub : Aᶜ ⊆ {ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} := by
      intro ω hω t
      have : ¬ B t ω + c * t < -δ' := fun h => hω ⟨t, h⟩
      have := not_lt.1 this
      linarith
    have hun : (1 : ℝ) ≤ P.real A + P.real Aᶜ := by
      have := measureReal_union_le (μ := P) A Aᶜ
      rw [Set.union_compl_self, probReal_univ] at this
      exact this
    have := measureReal_mono (μ := P) hsub
    linarith
  have hcont' : Continuous fun δ' : ℝ => 1 - Real.exp (-(2 * c * δ')) := by fun_prop
  exact le_of_tendsto ((hcont'.tendsto δ).mono_left (nhdsWithin_le_nhds (s := Set.Iio δ)))
    (eventually_nhdsWithin_of_forall fun δ' hδ' => h1 δ' hδ')

/-- **Gambler's ruin for Brownian motion with positive drift.**  If `B` is a pre-Brownian motion
with continuous paths, `c > 0` and `δ > 0`, the probability that `B t + c t > -δ` for all `t ≥ 0`
is `1 - exp (-2 c δ)`. -/
theorem measure_forall_drift_gt (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) {c : ℝ} (hc : 0 < c) {δ : ℝ} (hδ : 0 < δ) :
    P {ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} = ENNReal.ofReal (1 - Real.exp (-(2 * c * δ))) :=
  le_antisymm (measure_forall_drift_gt_le hB hm hc hδ) (le_measure_forall_drift_gt hB hm hcont hc δ)

end LatticeProb
