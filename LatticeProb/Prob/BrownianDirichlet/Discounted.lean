import LatticeProb.Prob.BrownianDirichlet.Dynkin

/-!
# Discounted Brownian compensation

The discounted observable includes the time integral of discount times forcing,
with generator `(σ² / 2) Δ` on the Euclidean Brownian path carrier.
-/

open MeasureTheory ProbabilityTheory InnerProductSpace Laplacian Set
open scoped NNReal ENNReal Topology

noncomputable section

namespace LatticeProb

/-- The forcing corresponding to discount `μd` and Brownian scale `σ`. -/
def discountedForcing {d : ℕ} (f : Euc d → ℝ) (σ μd : ℝ) (y : Euc d) : ℝ :=
  μd * f y - σ ^ 2 / 2 * Δ f y

/-- The discounted compensated observable, including its ordinary time integral. -/
def discountedObservable {d : ℕ} (f : Euc d → ℝ) (σ μd : ℝ)
    (x : Euc d) (t : ℝ≥0) (ω : BrownianPath d) : ℝ :=
  Real.exp (-μd * (t : ℝ)) * f (x + σ • ω t) +
    ∫ s in (0 : ℝ)..(t : ℝ),
      Real.exp (-μd * s) * discountedForcing f σ μd (x + σ • ω s.toNNReal)

/-- The forcing of a compactly supported C² function is continuous and compactly supported. -/
lemma continuous_compactSupport_discountedForcing {d : ℕ} {f : Euc d → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) (σ μd : ℝ) :
    Continuous (discountedForcing f σ μd) ∧ HasCompactSupport (discountedForcing f σ μd) := by
  obtain ⟨hLc, hLs⟩ := continuous_compactSupport_laplacian hf hc
  exact ⟨(continuous_const.mul hf.continuous).sub (continuous_const.mul hLc),
    hc.mul_left.sub hLs.mul_left⟩

/-- Positive discount bounds the observable by the terminal bound plus time times forcing bound. -/
lemma abs_discountedObservable_le {d : ℕ} {f : Euc d → ℝ} {σ μd K L : ℝ}
    (hμd : 0 < μd) (hK : ∀ y, |f y| ≤ K)
    (hL : ∀ y, |discountedForcing f σ μd y| ≤ L)
    (x : Euc d) (t : ℝ≥0) (ω : BrownianPath d) :
    |discountedObservable f σ μd x t ω| ≤ K + (t : ℝ) * L := by
  have he (s : ℝ) (hs : 0 ≤ s) : |Real.exp (-μd * s)| ≤ 1 := by
    rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hμd.le) hs
  have hi : |∫ s in (0 : ℝ)..(t : ℝ),
      Real.exp (-μd * s) * discountedForcing f σ μd (x + σ • ω s.toNNReal)| ≤
      L * (t : ℝ) := by
    simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg t.coe_nonneg] using
      (intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := (t : ℝ))
        (C := L) (f := fun s : ℝ ↦ Real.exp (-μd * s) *
          discountedForcing f σ μd (x + σ • ω s.toNNReal)) (fun s hs ↦ by
          rw [Real.norm_eq_abs, abs_mul]
          exact (mul_le_mul_of_nonneg_right (he s (by
            rw [uIoc_of_le t.coe_nonneg] at hs
            exact hs.1.le)) (abs_nonneg _)).trans (by
              simpa only [one_mul] using hL (x + σ • ω s.toNNReal))))
  calc
    _ ≤ |Real.exp (-μd * (t : ℝ)) * f (x + σ • ω t)| +
        |∫ s in (0 : ℝ)..(t : ℝ),
          Real.exp (-μd * s) * discountedForcing f σ μd (x + σ • ω s.toNNReal)| :=
      abs_add_le _ _
    _ ≤ K + L * (t : ℝ) := add_le_add
      (by
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_right (he t t.coe_nonneg) (abs_nonneg _)).trans
          (by simpa only [one_mul] using hK (x + σ • ω t))) hi
    _ = _ := by rw [mul_comm L]

/-- The discounted observable is jointly measurable in its starting point and path. -/
lemma measurable_discountedObservable_joint {d : ℕ} {f : Euc d → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) (σ μd : ℝ) (t : ℝ≥0) :
    Measurable (fun p : Euc d × BrownianPath d ↦
      discountedObservable f σ μd p.1 t p.2) := by
  obtain ⟨hD, _⟩ := continuous_compactSupport_discountedForcing hf hc σ μd
  have hpos : Continuous (fun p : (Euc d × BrownianPath d) × ℝ ↦
      p.1.1 + σ • p.1.2 p.2.toNNReal) := by fun_prop
  have hi : StronglyMeasurable (fun p : (Euc d × BrownianPath d) × ℝ ↦
      Real.exp (-μd * p.2) * discountedForcing f σ μd
        (p.1.1 + σ • p.1.2 p.2.toNNReal)) :=
    ((by fun_prop : Continuous (fun p : (Euc d × BrownianPath d) × ℝ ↦
      Real.exp (-μd * p.2))).mul (hD.comp hpos)).stronglyMeasurable
  have ht : Measurable (fun p : Euc d × BrownianPath d ↦
      Real.exp (-μd * (t : ℝ)) * f (p.1 + σ • p.2 t)) :=
    measurable_const.mul (hf.continuous.measurable.comp (by fun_prop))
  unfold discountedObservable
  apply ht.add
  simp only [intervalIntegral.integral_of_le t.coe_nonneg]
  exact (hi.integral_prod_right'
    (ν := (volume : Measure ℝ).restrict (Ioc 0 (t : ℝ)))).measurable

/-- The observable depends measurably only on the path up to its observation time. -/
lemma measurable_discountedObservable_past {d : ℕ} {f : Euc d → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (σ μd : ℝ) (x : Euc d) (t : ℝ≥0) :
    Measurable[brownianNaturalFiltration d t] (discountedObservable f σ μd x t) := by
  let stop : BrownianPath d → BrownianPath d := fun ω ↦
    ⟨fun u ↦ ω (min u t), ω.continuous.comp (continuous_id.min continuous_const)⟩
  have hs : Measurable[brownianNaturalFiltration d t] stop := by
    rw [measurable_iff_comap_le]
    conv_lhs =>
      rw [ContinuousMapBorel.ContinuousMap.measurableSpace_eq_iSup_comap_eval]
    rw [MeasurableSpace.comap_iSup, iSup_le_iff]
    intro u
    have hm := (measurable_brownian_position_past (0 : Euc d) 1 (min u t)).mono
      (Filtration.mono (brownianNaturalFiltration d) (min_le_right u t)) le_rfl
    simpa only [MeasurableSpace.comap_comp, Function.comp_def, stop,
      ContinuousMap.coe_mk, zero_add, one_smul] using hm.comap_le
  have heq (ω : BrownianPath d) :
      discountedObservable f σ μd x t (stop ω) = discountedObservable f σ μd x t ω := by
    unfold discountedObservable
    change Real.exp (-μd * (t : ℝ)) * f (x + σ • ω (min t t)) +
      (∫ s in (0 : ℝ)..(t : ℝ), Real.exp (-μd * s) *
        discountedForcing f σ μd (x + σ • ω (min s.toNNReal t))) = _
    rw [min_self]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le t.coe_nonneg] at hs
    have hst : s.toNNReal ≤ t := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs.1]
      exact hs.2
    dsimp only
    rw [min_eq_left hst]
  have hm : Measurable[brownianNaturalFiltration d t]
      (fun ω ↦ discountedObservable f σ μd x t (stop ω)) :=
    (measurable_discountedObservable_joint hf hc σ μd t).comp
      (measurable_const.prodMk hs)
  simpa only [heq] using hm

/-- A finite-time discounted observable is integrable under a standard Brownian law. -/
lemma integrable_discountedObservable {d : ℕ} {μ : Measure (BrownianPath d)}
    (hμ : IsStandardBrownianLaw μ) {f : Euc d → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) {μd : ℝ} (hμd : 0 < μd)
    (σ : ℝ) (x : Euc d) (t : ℝ≥0) :
    Integrable (discountedObservable f σ μd x t) μ := by
  letI : IsProbabilityMeasure μ := hμ.1
  obtain ⟨K, hK⟩ := hc.exists_bound_of_continuous hf.continuous
  obtain ⟨hD, hDc⟩ := continuous_compactSupport_discountedForcing hf hc σ μd
  obtain ⟨L, hL⟩ := hDc.exists_bound_of_continuous hD
  exact (integrable_const (K + (t : ℝ) * L)).mono'
    (((measurable_discountedObservable_joint hf hc σ μd t).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun ω ↦ by
      simpa only [Real.norm_eq_abs] using
        abs_discountedObservable_le hμd hK hL x t ω))

/-- The discounted Dynkin formula for deterministic expectations. -/
lemma discounted_brownian_expectation {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    {σ : ℝ} (hσ : 0 < σ) (μd : ℝ) (x : Euc d) (t : ℝ≥0) :
    Real.exp (-μd * (t : ℝ)) * (∫ ω, f (x + σ • ω t) ∂μ) +
      (∫ s in (0 : ℝ)..(t : ℝ), Real.exp (-μd * s) *
        (∫ ω, discountedForcing f σ μd (x + σ • ω s.toNNReal) ∂μ)) = f x := by
  let E : ℝ → ℝ := fun s ↦ ∫ ω, f (x + σ • ω s.toNNReal) ∂μ
  let G : ℝ → ℝ := fun s ↦ ∫ ω, σ ^ 2 / 2 * Δ f (x + σ • ω s.toNNReal) ∂μ
  have hE : Continuous E :=
    (continuous_brownian_expectation hμ hf.continuous hc x σ).comp
      continuous_real_toNNReal
  obtain ⟨hLc, hLs⟩ := continuous_compactSupport_laplacian hf hc
  have hG : Continuous G := by
    have heq : G = fun s ↦ σ ^ 2 / 2 *
        (∫ ω, Δ f (x + σ • ω s.toNNReal) ∂μ) := by
      funext s
      exact integral_const_mul _ _
    rw [heq]
    exact continuous_const.mul
      ((continuous_brownian_expectation hμ hLc hLs x σ).comp continuous_real_toNNReal)
  have hform (s : ℝ) (hs : 0 ≤ s) :
      E s = f x + ∫ r in (0 : ℝ)..s, G r := by
    simpa only [E, G, Real.coe_toNNReal _ hs] using
      brownian_dynkin hμ hf hc hσ x s.toNNReal
  have hzero : E 0 = f x := by
    simpa only [intervalIntegral.integral_same, add_zero] using hform 0 le_rfl
  have hderiv (a : ℝ) (ha : a ∈ Ioo (0 : ℝ) (t : ℝ)) :
      HasDerivWithinAt E (G a) (Ioi a) a := by
    have hp := (intervalIntegral.integral_hasDerivAt_right
      (hG.intervalIntegrable 0 a) hG.aestronglyMeasurable.stronglyMeasurableAtFilter
      hG.continuousAt).const_add (f x)
    exact hp.hasDerivWithinAt.congr (fun y hy ↦ hform y (ha.1.le.trans hy.le))
      (hform a ha.1.le)
  have hweight : Continuous (fun s : ℝ ↦ Real.exp (-μd * s)) := by fun_prop
  have hd (a : ℝ) (ha : a ∈ Ioo (0 : ℝ) (t : ℝ)) :
      HasDerivWithinAt (fun s ↦ Real.exp (-μd * s) * E s)
        (Real.exp (-μd * a) * (G a - μd * E a)) (Ioi a) a := by
    have hw := ((hasDerivAt_id a).const_mul (-μd)).exp
    have hh := hw.hasDerivWithinAt.mul (hderiv a ha)
    apply hh.congr_deriv
    simp only [id_eq, mul_one]
    generalize Real.exp (-μd * a) = e
    ring
  have hint := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    t.coe_nonneg (hweight.mul hE).continuousOn hd
    ((hweight.mul (hG.sub (continuous_const.mul hE))).intervalIntegrable 0 t)
  have hforce (s : ℝ) :
      (∫ ω, discountedForcing f σ μd (x + σ • ω s.toNNReal) ∂μ) =
        μd * E s - G s := by
    change (∫ ω, μd * f (x + σ • ω s.toNNReal) -
      σ ^ 2 / 2 * Δ f (x + σ • ω s.toNNReal) ∂μ) = _
    rw [integral_sub
      ((integrable_brownian_position hμ hf.continuous hc x σ _).const_mul μd)
      ((integrable_brownian_position hμ hLc hLs x σ _).const_mul _), integral_const_mul]
  simp_rw [hforce]
  have hneg : (∫ s in (0 : ℝ)..(t : ℝ),
      Real.exp (-μd * s) * (μd * E s - G s)) =
      -(∫ s in (0 : ℝ)..(t : ℝ), Real.exp (-μd * s) * (G s - μd * E s)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only
    generalize Real.exp (-μd * s) = e
    ring
  rw [hneg, hint]
  simp only [Pi.mul_apply]
  rw [hzero]
  simp only [mul_zero, Real.exp_zero, one_mul, Real.toNNReal_coe, E]
  generalize Real.exp (-μd * (t : ℝ)) = e
  ring

/-- Discounted compensation preserves the expectation at every deterministic time. -/
theorem integral_discounted {d : ℕ} {μ : Measure (BrownianPath d)}
    (hμ : IsStandardBrownianLaw μ) {f : Euc d → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) {σ : ℝ} (hσ : 0 < σ)
    (μd : ℝ) (x : Euc d) (t : ℝ≥0) :
    (∫ ω, discountedObservable f σ μd x t ω ∂μ) = f x := by
  letI : IsProbabilityMeasure μ := hμ.1
  let ν : Measure ℝ := volume.restrict (Ioc 0 (t : ℝ))
  obtain ⟨hD, hDc⟩ := continuous_compactSupport_discountedForcing hf hc σ μd
  obtain ⟨L, hL⟩ := hDc.exists_bound_of_continuous hD
  let g : BrownianPath d × ℝ → ℝ := fun p ↦ Real.exp (-μd * p.2) *
    discountedForcing f σ μd (x + σ • p.1 p.2.toNNReal)
  have hg : Continuous g := by
    dsimp only [g]
    apply Continuous.mul
    · fun_prop
    · exact hD.comp (by fun_prop)
  have hb : Integrable (fun s : ℝ ↦ Real.exp (-μd * s) * L) ν :=
    (show Continuous (fun s : ℝ ↦ Real.exp (-μd * s) * L) by fun_prop
      ).intervalIntegrable 0 t |>.1
  have hi : Integrable g (μ.prod ν) :=
    (hb.comp_snd μ).mono' hg.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p ↦ by
        dsimp only [g]
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_left (hL _) (Real.exp_pos _).le))
  have ht := (integrable_brownian_position hμ hf.continuous hc x σ t).const_mul
    (Real.exp (-μd * (t : ℝ)))
  have hswap := integral_integral_swap (f := fun ω s ↦ g (ω, s)) hi
  change (∫ ω, Real.exp (-μd * (t : ℝ)) * f (x + σ • ω t) +
    (∫ s in (0 : ℝ)..(t : ℝ), g (ω, s)) ∂μ) = f x
  simp only [intervalIntegral.integral_of_le t.coe_nonneg]
  rw [integral_add ht hi.integral_prod_left, integral_const_mul, hswap]
  have he := discounted_brownian_expectation hμ hf hc hσ μd x t
  simpa only [intervalIntegral.integral_of_le t.coe_nonneg, g, ν, integral_const_mul]
    using he

/-- Integrating a bounded functional of the current position and future increments
on an event of the past integrates the future against a fresh Brownian law. -/
private lemma setIntegral_brownian_position_shift {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (σ : ℝ) (x : Euc d) (s : ℝ≥0) {H : Set (BrownianPath d)}
    (hH : MeasurableSet[brownianNaturalFiltration d s] H)
    {G : Euc d × BrownianPath d → ℝ} (hG : Measurable G)
    {C : ℝ} (hC : ∀ p, ‖G p‖ ≤ C) :
    (∫ ω in H, G (x + σ • ω s, shiftedBrownianPath s ω) ∂μ) =
      ∫ ω in H, (∫ η, G (x + σ • ω s, η) ∂μ) ∂μ := by
  letI : IsProbabilityMeasure μ := hμ.1
  let Y : BrownianPath d → Euc d := fun ω ↦ x + σ • ω s
  have hYp := measurable_brownian_position_past x σ s
  have hY : Measurable Y := hYp.mono ((brownianNaturalFiltration d).le s) le_rfl
  have hW := hY.prodMk (measurable_shiftedBrownianPath s)
  have hlaw : (μ.restrict H).map (fun ω ↦ (Y ω, shiftedBrownianPath s ω)) =
      ((μ.restrict H).map Y).prod μ := by
    refine (Measure.prod_eq (fun A B hA hB ↦ ?_)).symm
    rw [Measure.map_apply hW (hA.prod hB), Measure.restrict_apply (hW (hA.prod hB)),
      Measure.map_apply hY hA, Measure.restrict_apply (hY hA)]
    have heq : (fun ω ↦ (Y ω, shiftedBrownianPath s ω)) ⁻¹' (A ×ˢ B) ∩ H =
        (shiftedBrownianPath s ⁻¹' B) ∩ (Y ⁻¹' A ∩ H) := by
      ext ω
      simp only [mem_inter_iff, mem_preimage, mem_prod]
      tauto
    rw [heq, standardBrownianLaw_shift_inter_past hμ s ((hYp hA).inter hH) hB,
      mul_comm]
  have hi : Integrable G (((μ.restrict H).map Y).prod μ) :=
    (integrable_const C).mono' hG.aestronglyMeasurable
      (Filter.Eventually.of_forall hC)
  calc
    _ = ∫ p, G p ∂((μ.restrict H).map (fun ω ↦ (Y ω, shiftedBrownianPath s ω))) :=
      (integral_map hW.aemeasurable hG.aestronglyMeasurable).symm
    _ = ∫ p, G p ∂(((μ.restrict H).map Y).prod μ) := by rw [hlaw]
    _ = ∫ y, (∫ η, G (y, η) ∂μ) ∂((μ.restrict H).map Y) := integral_prod _ hi
    _ = _ := integral_map hY.aemeasurable
      hG.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable

/-- Splitting at a deterministic time expresses the compensated increment through the
shifted path, with the discount factor at the splitting time. -/
lemma discountedObservable_add {d : ℕ} {f : Euc d → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (σ μd : ℝ) (x : Euc d) (s u : ℝ≥0) (ω : BrownianPath d) :
    discountedObservable f σ μd x (s + u) ω - discountedObservable f σ μd x s ω =
      Real.exp (-μd * (s : ℝ)) *
        (discountedObservable f σ μd (x + σ • ω s) u (shiftedBrownianPath s ω) -
          f (x + σ • ω s)) := by
  obtain ⟨hD, _⟩ := continuous_compactSupport_discountedForcing hf hc σ μd
  let g : ℝ → ℝ := fun r ↦ Real.exp (-μd * r) *
    discountedForcing f σ μd (x + σ • ω r.toNNReal)
  have hg : Continuous g := by
    apply Continuous.mul
    · fun_prop
    · exact hD.comp (by fun_prop)
  have hpos (v : ℝ≥0) :
      x + σ • ω s + σ • shiftedBrownianPath s ω v = x + σ • ω (s + v) := by
    change x + σ • ω s + σ • (ω (s + v) - ω s) = _
    rw [smul_sub]
    abel
  have hweight (a b : ℝ) :
      Real.exp (-μd * (a + b)) = Real.exp (-μd * a) * Real.exp (-μd * b) := by
    rw [mul_add, Real.exp_add]
  have hrun : Real.exp (-μd * (s : ℝ)) *
      (∫ r in (0 : ℝ)..(u : ℝ), Real.exp (-μd * r) *
        discountedForcing f σ μd
          (x + σ • ω s + σ • shiftedBrownianPath s ω r.toNNReal)) =
      ∫ r in (s : ℝ)..((s : ℝ) + (u : ℝ)), g r := by
    rw [← intervalIntegral.integral_const_mul]
    have hshift := intervalIntegral.integral_comp_add_left g (s : ℝ)
      (a := (0 : ℝ)) (b := (u : ℝ))
    rw [add_zero] at hshift
    rw [← hshift]
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le u.coe_nonneg] at hr
    have htime : s + r.toNNReal = ((s : ℝ) + r).toNNReal := by
      apply NNReal.coe_injective
      rw [NNReal.coe_add, Real.coe_toNNReal _ hr.1,
        Real.coe_toNNReal _ (add_nonneg s.coe_nonneg hr.1)]
    dsimp only [g]
    rw [hpos, htime, hweight]
    exact (mul_assoc _ _ _).symm
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable (μ := volume) 0 s)
    (hg.intervalIntegrable (μ := volume) s ((s : ℝ) + (u : ℝ)))
  unfold discountedObservable
  rw [hpos, NNReal.coe_add, hweight]
  change _ - (_ + ∫ r in (0 : ℝ)..(s : ℝ), g r) = _
  rw [show (∫ r in (0 : ℝ)..((s : ℝ) + (u : ℝ)), g r) =
    (∫ r in (0 : ℝ)..(s : ℝ), g r) +
      ∫ r in (s : ℝ)..((s : ℝ) + (u : ℝ)), g r from hsplit.symm, ← hrun]
  generalize Real.exp (-μd * (s : ℝ)) = a
  generalize Real.exp (-μd * (u : ℝ)) = b
  ring

/-- Discounted compensation has equal integrals at two times on every event of the
natural past at the earlier time. -/
theorem setIntegral_discounted_past {d : ℕ} {μ : Measure (BrownianPath d)}
    (hμ : IsStandardBrownianLaw μ) {f : Euc d → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) {σ μd : ℝ}
    (hσ : 0 < σ) (hμd : 0 < μd) (x : Euc d) {s t : ℝ≥0} (hst : s ≤ t)
    {H : Set (BrownianPath d)} (hH : MeasurableSet[brownianNaturalFiltration d s] H) :
    (∫ ω in H, discountedObservable f σ μd x t ω ∂μ) =
      ∫ ω in H, discountedObservable f σ μd x s ω ∂μ := by
  letI : IsProbabilityMeasure μ := hμ.1
  obtain ⟨u, rfl⟩ := exists_add_of_le hst
  obtain ⟨K, hK⟩ := hc.exists_bound_of_continuous hf.continuous
  obtain ⟨hD, hDc⟩ := continuous_compactSupport_discountedForcing hf hc σ μd
  obtain ⟨L, hL⟩ := hDc.exists_bound_of_continuous hD
  let G : Euc d × BrownianPath d → ℝ := fun p ↦
    discountedObservable f σ μd p.1 u p.2 - f p.1
  have hG : Measurable G :=
    (measurable_discountedObservable_joint hf hc σ μd u).sub
      (hf.continuous.measurable.comp measurable_fst)
  have hGb (p : Euc d × BrownianPath d) : ‖G p‖ ≤ K + (u : ℝ) * L + K := by
    exact (norm_sub_le _ _).trans (add_le_add
      (by simpa only [Real.norm_eq_abs] using
        abs_discountedObservable_le hμd hK hL p.1 u p.2)
      (by simpa only [Real.norm_eq_abs] using hK p.1))
  have hz (y : Euc d) : (∫ η, G (y, η) ∂μ) = 0 := by
    dsimp only [G]
    rw [integral_sub (integrable_discountedObservable hμ hf hc hμd σ y u)
      (integrable_const (f y)), integral_discounted hμ hf hc hσ]
    simp
  have hr := setIntegral_brownian_position_shift hμ σ x s hH hG hGb
  simp_rw [hz] at hr
  rw [integral_zero] at hr
  have hi := (integrable_discountedObservable hμ hf hc hμd σ x (s + u)).integrableOn (s := H)
  have hj := (integrable_discountedObservable hμ hf hc hμd σ x s).integrableOn (s := H)
  have hdiff : (∫ ω in H, discountedObservable f σ μd x (s + u) ω -
      discountedObservable f σ μd x s ω ∂μ) = 0 := by
    calc
      _ = ∫ ω in H, Real.exp (-μd * (s : ℝ)) *
          G (x + σ • ω s, shiftedBrownianPath s ω) ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall
          (fun ω ↦ discountedObservable_add hf hc σ μd x s u ω))
      _ = Real.exp (-μd * (s : ℝ)) *
          (∫ ω in H, G (x + σ • ω s, shiftedBrownianPath s ω) ∂μ) :=
        integral_const_mul _ _
      _ = 0 := by rw [hr, mul_zero]
  rw [integral_sub hi hj] at hdiff
  exact sub_eq_zero.mp hdiff

/-- A nonzero smooth bump under an existing one-dimensional Brownian law satisfies
the discounted identity at unit scale, discount, and time. -/
theorem exists_brownian_bump_discounted :
    let b : ContDiffBump (0 : Euc 1) := ⟨1, 2, one_pos, one_lt_two⟩
    ∃ μ : Measure (BrownianPath 1), IsStandardBrownianLaw μ ∧ b (0 : Euc 1) = 1 ∧
      (∫ ω, discountedObservable (⇑b) 1 1 (0 : Euc 1) 1 ω ∂μ) = 1 := by
  intro b
  obtain ⟨μ, hμ⟩ := BrownianPathCoordsExample.exists_isStandardBrownianLaw_one
  have hb : b (0 : Euc 1) = 1 := b.one_of_mem_closedBall (by simp [b])
  exact ⟨μ, hμ, hb, (integral_discounted hμ b.contDiff b.hasCompactSupport
    zero_lt_one 1 (0 : Euc 1) 1).trans hb⟩

end LatticeProb
