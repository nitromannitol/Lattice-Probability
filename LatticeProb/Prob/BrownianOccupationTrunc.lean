import LatticeProb.Prob.BrownianMarginalDensity
import LatticeProb.Prob.BrownianRestartCanonical

/-!
# The occupation integral of Brownian motion up to a stopping time and a horizon

For the motion of `LatticeProb.IsBrownianSpace` started at `x` and a bounded measurable `φ`, the
expected integral of `φ` along the path up to time `N` is the integral of `φ` against the heat
kernel integrated over `[0, N]`, by Fubini's theorem and the marginal density. Splitting the
occupation integral at a stopping time `τ` and restarting the motion at `τ` with the strong Markov
property gives the expected occupation integral up to `τ ∧ N`: the full occupation integral up to
`N`, minus, on the event `τ < N`, the occupation integral of the restarted motion from `B τ` over
the remaining horizon `N - τ`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}

/-- A Brownian motion started at the origin, translated by `z`, is a Brownian motion started
at `z`. -/
theorem IsBrownianSpace.const_add {W : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsBrownianSpace d 0 W P) (z : EuclideanSpace ℝ (Fin d)) :
    IsBrownianSpace d z (fun t ω => z + W t ω) P where
  start := by
    filter_upwards [hW.start] with ω hω
    rw [hω, add_zero]
  coord := by
    intro i
    have heq : (fun (t : ℝ≥0) (ω : Ω) => Real.sqrt d * ((z + W t ω) i - z i))
        = fun t ω => Real.sqrt d * (W t ω i - (0 : EuclideanSpace ℝ (Fin d)) i) := by
      funext t ω
      simp
    rw [heq]
    exact hW.coord i
  indep := by
    have h := hW.indep.comp (fun (i : Fin d) (f : ℝ≥0 → ℝ) (t : ℝ≥0) => z i + f t)
      (fun i => Measurable.of_eval fun t => measurable_const.add (measurable_pi_apply t))
    convert h using 1
    funext i ω
    funext t
    simp [Function.comp]

/-- **The expected occupation integral over a deterministic horizon.** For a Brownian motion
started at `z` and a bounded measurable `φ`, the expected integral of `φ` along the path over
`[0, s]` is the integral of `φ` against the heat kernel integrated over `[0, s]`. -/
theorem IsBrownianSpace.integral_intervalIntegral_eq (hd : 1 ≤ d)
    {z : EuclideanSpace ℝ (Fin d)} {C : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hC : IsBrownianSpace d z C P) (hm : ∀ t, Measurable (C t))
    (hcont : ∀ ω, Continuous fun t => C t ω) {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : Measurable φ) {M : ℝ} (hM : ∀ y, |φ y| ≤ M) {s : ℝ} (hs : 0 ≤ s) :
    ∫ ω, (∫ r in (0 : ℝ)..s, φ (C r.toNNReal ω)) ∂P
      = ∫ y, φ y * ∫ t in (0 : ℝ)..s, brownianHeatKernel d t z y := by
  have hP : IsProbabilityMeasure P := hC.isProbabilityMeasure
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hjointC : StronglyMeasurable (Function.uncurry C) :=
    stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hcont
      fun t => (hm t).stronglyMeasurable
  have hf : Measurable fun p : Ω × ℝ => φ (C p.2.toNNReal p.1) :=
    hφ.comp (hjointC.measurable.comp (measurable_real_toNNReal.comp measurable_snd |>.prodMk
      measurable_fst))
  have hk : Measurable fun p : ℝ × EuclideanSpace ℝ (Fin d) => brownianHeatKernel d p.1 z p.2 := by
    unfold brownianHeatKernel
    fun_prop
  have hk0 : ∀ t, 0 ≤ t → ∀ y, 0 ≤ brownianHeatKernel d t z y := fun t ht y => by
    unfold brownianHeatKernel
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le
  have hfk : Measurable fun p : ℝ × EuclideanSpace ℝ (Fin d) => φ p.2 * brownianHeatKernel d p.1 z p.2 :=
    (hφ.comp measurable_snd).mul hk
  -- the heat kernel at a positive time is a probability density
  have hdens : ∀ r : ℝ, 0 < r → P.map (C r.toNNReal)
      = volume.withDensity fun y => ENNReal.ofReal (brownianHeatKernel d r z y) := fun r hr => by
    rw [hC.map_eq_withDensity P hd z C hm r.toNNReal (Real.toNNReal_pos.2 hr),
      Real.coe_toNNReal r hr.le]
  have hkint : ∀ r : ℝ, 0 < r → Integrable (fun y => brownianHeatKernel d r z y) ∧
      ∫ y, brownianHeatKernel d r z y = 1 := fun r hr => by
    have hm1 : ∫⁻ y, ENNReal.ofReal (brownianHeatKernel d r z y) = 1 := by
      have h := congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin d)) => μ Set.univ) (hdens r hr)
      simp only [Measure.map_apply (hm _) MeasurableSet.univ, Set.preimage_univ, measure_univ,
        withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
      exact h.symm
    have hmeas : Measurable fun y => brownianHeatKernel d r z y :=
      hk.comp (measurable_const.prodMk measurable_id)
    refine ⟨⟨hmeas.aestronglyMeasurable, ?_⟩, ?_⟩
    · rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (hk0 r hr.le)), hm1]
      exact ENNReal.one_lt_top
    · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (hk0 r hr.le))
        hmeas.aestronglyMeasurable, hm1, ENNReal.toReal_one]
  -- swap the time and the sample
  have hint1 : Integrable (Function.uncurry fun (ω : Ω) (r : ℝ) => φ (C r.toNNReal ω))
      (P.prod (volume.restrict (Set.Ioc (0 : ℝ) s))) :=
    (integrable_const M).mono' hf.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hM _)
  have hlhs : ∫ ω, (∫ r in (0 : ℝ)..s, φ (C r.toNNReal ω)) ∂P
      = ∫ r in Set.Ioc (0 : ℝ) s, ∫ y, φ y * brownianHeatKernel d r z y := by
    simp_rw [intervalIntegral.integral_of_le hs]
    rw [integral_integral_swap hint1]
    refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
    rw [← integral_map (hm _).aemeasurable hφ.aestronglyMeasurable, hdens r hr.1]
    have hmeas : Measurable fun y => (brownianHeatKernel d r z y).toNNReal :=
      (hk.comp (measurable_const.prodMk measurable_id)).real_toNNReal
    rw [show (fun y => ENNReal.ofReal (brownianHeatKernel d r z y))
        = fun y => (((brownianHeatKernel d r z y).toNNReal : ℝ≥0) : ℝ≥0∞) from rfl,
      integral_withDensity_eq_integral_smul hmeas]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (hk0 r hr.1.le y)]
    ring
  -- swap the time and the space variable
  have hint2 : Integrable (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
      φ p.2 * brownianHeatKernel d p.1 z p.2) ((volume.restrict (Set.Ioc (0 : ℝ) s)).prod volume) := by
    refine (integrable_prod_iff hfk.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun r hr => ?_)
      refine ((hkint r hr.1).1.const_mul M).mono' (hfk.comp (measurable_const.prodMk
        measurable_id)).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hk0 r hr.1.le y)]
      exact mul_le_mul_of_nonneg_right (hM y) (hk0 r hr.1.le y)
    · refine (integrable_const M).mono' hfk.aestronglyMeasurable.norm.integral_prod_right' ?_
      refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun r hr => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      calc ∫ y, ‖φ y * brownianHeatKernel d r z y‖
          ≤ ∫ y, M * brownianHeatKernel d r z y := by
            refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
              ((hkint r hr.1).1.const_mul M) (Filter.Eventually.of_forall fun y => ?_)
            show ‖φ y * brownianHeatKernel d r z y‖ ≤ M * brownianHeatKernel d r z y
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hk0 r hr.1.le y)]
            exact mul_le_mul_of_nonneg_right (hM y) (hk0 r hr.1.le y)
        _ = M := by rw [integral_const_mul, (hkint r hr.1).2, mul_one]
  rw [hlhs, integral_integral_swap hint2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show ∫ r in Set.Ioc (0 : ℝ) s, φ y * brownianHeatKernel d r z y
    = φ y * ∫ t in (0 : ℝ)..s, brownianHeatKernel d t z y
  rw [intervalIntegral.integral_of_le hs, integral_const_mul]

/-- **The expected occupation integral up to a stopping time and a horizon.** For a Brownian
motion started at `x`, a stopping time `τ` of its natural filtration, a bounded measurable `φ` and
a horizon `N`, the expected integral of `φ` along the path up to `τ ∧ N` is the expected integral
up to `N` minus, on the event `τ < N`, the expected integral of the motion restarted at `B τ` over
the remaining horizon `N - τ`, each written against the heat kernel. -/
theorem IsBrownianSpace.integral_occupation_trunc (P : Measure Ω) [IsProbabilityMeasure P]
    (hd : 1 ≤ d) (x : EuclideanSpace ℝ (Fin d)) (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (hB : IsBrownianSpace d x B P) (hm : ∀ t, StronglyMeasurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (natFiltration B hm) (fun ω => (τ ω : ℝ≥0∞)))
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (hφ : Measurable φ) (hφb : ∃ M, ∀ z, |φ z| ≤ M)
    (N : ℝ≥0) :
    ∫ ω, (∫ r in (0 : ℝ)..((min (τ ω) N : ℝ≥0) : ℝ), φ (B r.toNNReal ω)) ∂P
      = (∫ y, φ y * ∫ t in (0 : ℝ)..(N : ℝ), brownianHeatKernel d t x y)
        - ∫ ω in {ω | τ ω < N}, (∫ y, φ y *
            ∫ t in (0 : ℝ)..((N : ℝ) - τ ω), brownianHeatKernel d t (B (τ ω) ω) y) ∂P := by
  obtain ⟨M, hM⟩ := hφb
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hmB : ∀ t, Measurable (B t) := fun t => (hm t).measurable
  have hτm : Measurable τ := measurable_of_isStoppingTime hτ
  have hNR : (0 : ℝ) ≤ N := N.coe_nonneg
  have hpath : ∀ ω, Measurable fun r : ℝ => φ (B r.toNNReal ω) := fun ω =>
    hφ.comp ((hcont ω).measurable.comp measurable_real_toNNReal)
  have hII : ∀ ω (a b : ℝ), IntervalIntegrable (fun r : ℝ => φ (B r.toNNReal ω)) volume a b :=
    fun ω a b => (intervalIntegrable_const (c := M)).mono_fun' (hpath ω).aestronglyMeasurable
      (Filter.Eventually.of_forall fun r => by
        show ‖φ (B r.toNNReal ω)‖ ≤ M
        rw [Real.norm_eq_abs]
        exact hM _)
  -- the event `τ < N`
  set E : Set Ω := {ω | τ ω < N} with hE_def
  have hEτ : MeasurableSet[hτ.measurableSpace] E := by
    have h := hτ.measurableSet_lt' (N : ℝ≥0)
    convert h using 1
    ext ω
    exact ENNReal.coe_lt_coe.symm
  have hEm : MeasurableSet E := hτ.measurableSpace_le _ hEτ
  -- splitting the occupation integral at `τ`
  have hsplit : ∀ ω, (∫ r in (0 : ℝ)..((min (τ ω) N : ℝ≥0) : ℝ), φ (B r.toNNReal ω))
      = (∫ r in (0 : ℝ)..(N : ℝ), φ (B r.toNNReal ω))
        - E.indicator (fun ω => ∫ r in (τ ω : ℝ)..(N : ℝ), φ (B r.toNNReal ω)) ω := by
    intro ω
    by_cases h : τ ω < N
    · rw [Set.indicator_of_mem (show ω ∈ E from h), min_eq_left h.le, eq_sub_iff_add_eq,
        intervalIntegral.integral_add_adjacent_intervals (hII ω _ _) (hII ω _ _)]
    · rw [Set.indicator_of_notMem (show ω ∉ E from h), sub_zero, min_eq_right (not_lt.1 h)]
  -- the full occupation integral
  have hjointB : StronglyMeasurable (Function.uncurry B) :=
    stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hcont hm
  have hf : Measurable fun p : Ω × ℝ => φ (B p.2.toNNReal p.1) :=
    hφ.comp (hjointB.measurable.comp ((measurable_real_toNNReal.comp measurable_snd).prodMk
      measurable_fst))
  have hI0 : Integrable (fun ω => ∫ r in (0 : ℝ)..(N : ℝ), φ (B r.toNNReal ω)) P := by
    have hmeas : StronglyMeasurable fun ω => ∫ r in Set.Ioc (0 : ℝ) N, φ (B r.toNNReal ω) :=
      hf.stronglyMeasurable.integral_prod_right'
    refine (integrable_const (M * N)).mono' ?_ (Filter.Eventually.of_forall fun ω => ?_)
    · simp_rw [intervalIntegral.integral_of_le hNR]
      exact hmeas.aestronglyMeasurable
    · rw [intervalIntegral.integral_of_le hNR]
      refine (norm_setIntegral_le_of_norm_le_const (C := M) measure_Ioc_lt_top fun r _ => ?_).trans
        (le_of_eq ?_)
      · rw [Real.norm_eq_abs]
        exact hM _
      · rw [Real.volume_real_Ioc_of_le hNR, sub_zero]
  -- the occupation integral after `τ` as a functional of the past and the restarted path
  let F : (ℝ≥0 × EuclideanSpace ℝ (Fin d)) × BrownianPath d → ℝ := fun q =>
    ∫ u in Set.Ioc (0 : ℝ) N,
      (Set.Iic ((N : ℝ) - q.1.1)).indicator (fun u => φ (q.1.2 + q.2 u.toNNReal)) u
  have hFm : Measurable F := by
    have hg : Measurable fun p : ((ℝ≥0 × EuclideanSpace ℝ (Fin d)) × BrownianPath d) × ℝ =>
        (Set.Iic ((N : ℝ) - p.1.1.1)).indicator (fun u => φ (p.1.1.2 + p.1.2 u.toNNReal)) p.2 := by
      have hset : MeasurableSet {p : ((ℝ≥0 × EuclideanSpace ℝ (Fin d)) × BrownianPath d) × ℝ |
          p.2 ≤ (N : ℝ) - p.1.1.1} :=
        measurableSet_le measurable_snd (measurable_const.sub
          (measurable_subtype_coe.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))))
      have hφm : Measurable fun p : ((ℝ≥0 × EuclideanSpace ℝ (Fin d)) × BrownianPath d) × ℝ =>
          φ (p.1.1.2 + p.1.2 p.2.toNNReal) := by
        have hev : Continuous fun p : ((ℝ≥0 × EuclideanSpace ℝ (Fin d)) × BrownianPath d) × ℝ =>
            p.1.2 p.2.toNNReal :=
          Continuous.eval (f := fun p : ((ℝ≥0 × EuclideanSpace ℝ (Fin d)) × BrownianPath d) × ℝ =>
            p.1.2) (g := fun p => p.2.toNNReal) (by fun_prop)
            (continuous_real_toNNReal.comp continuous_snd)
        exact hφ.comp (Measurable.add (by fun_prop) hev.measurable)
      convert hφm.indicator hset using 1
      funext p
      simp only [Set.indicator_apply, Set.mem_Iic, Set.mem_ofPred_eq]
    exact hg.stronglyMeasurable.integral_prod_right'.measurable
  have hFbound : ∀ q, ‖F q‖ ≤ M * N := fun q => by
    refine (norm_setIntegral_le_of_norm_le_const (C := M) measure_Ioc_lt_top fun u _ => ?_).trans
      (le_of_eq (by rw [Real.volume_real_Ioc_of_le hNR, sub_zero]))
    rw [Real.norm_eq_abs]
    by_cases hu : u ∈ Set.Iic ((N : ℝ) - q.1.1)
    · rw [Set.indicator_of_mem hu]
      exact hM _
    · rw [Set.indicator_of_notMem hu, abs_zero]
      exact hM0
  have hFIoc : ∀ (s : ℝ≥0) (z : EuclideanSpace ℝ (Fin d)) (w : BrownianPath d),
      F ((s, z), w) = ∫ u in Set.Ioc (0 : ℝ) ((N : ℝ) - s), φ (z + w u.toNNReal) := by
    intro s z w
    show ∫ u in Set.Ioc (0 : ℝ) N,
      (Set.Iic ((N : ℝ) - s)).indicator (fun u => φ (z + w u.toNNReal)) u = _
    have hset : Set.Ioc (0 : ℝ) N ∩ Set.Iic ((N : ℝ) - s) = Set.Ioc 0 ((N : ℝ) - s) := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iic]
      constructor
      · rintro ⟨⟨h0, -⟩, h1⟩
        exact ⟨h0, h1⟩
      · rintro ⟨h0, h1⟩
        exact ⟨⟨h0, h1.trans (sub_le_self _ s.coe_nonneg)⟩, h1⟩
    rw [setIntegral_indicator measurableSet_Iic, hset]
  -- the past at `τ`
  have hτF : Measurable[hτ.measurableSpace] τ := by
    let _ : MeasurableSpace Ω := hτ.measurableSpace
    refine measurable_of_Iic fun a => ?_
    have h2 : τ ⁻¹' Set.Iic a = {ω | ((τ ω : ℝ≥0) : ℝ≥0∞) ≤ (a : ℝ≥0∞)} := by
      ext ω
      exact ENNReal.coe_le_coe.symm
    rw [h2]
    exact hτ.measurableSet_le' a
  have hprog : IsStronglyProgressive (natFiltration B hm) B :=
    (stronglyAdapted_natFiltration B hm).isStronglyProgressive_of_continuous hcont
  have hBτ : Measurable[hτ.measurableSpace] fun ω => B (τ ω) ω :=
    measurable_stoppedValue hprog hτ
  have hY : Measurable[hτ.measurableSpace] fun ω => (τ ω, B (τ ω) ω) := hτF.prodMk hBτ
  have hRm := measurable_restartPath hm hcont hτm
  have hYm : Measurable fun ω => (τ ω, B (τ ω) ω) := hY.mono hτ.measurableSpace_le le_rfl
  have hFi : Integrable (fun ω => F ((τ ω, B (τ ω) ω), restartPath B hcont τ ω)) (P.restrict E) :=
    (integrable_const (M * N)).mono' (hFm.comp (hYm.prodMk hRm)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => hFbound _)
  -- on `τ < N` the occupation integral after `τ` is the functional of the restarted path
  have hEq : ∀ ω ∈ E, (∫ r in (τ ω : ℝ)..(N : ℝ), φ (B r.toNNReal ω))
      = F ((τ ω, B (τ ω) ω), restartPath B hcont τ ω) := by
    intro ω hω
    have hlt : (τ ω : ℝ) < N := by exact_mod_cast hω
    rw [hFIoc, ← intervalIntegral.integral_of_le (sub_nonneg.2 hlt.le)]
    have h1 := intervalIntegral.integral_comp_add_right (fun r : ℝ => φ (B r.toNNReal ω))
      (τ ω : ℝ) (a := 0) (b := (N : ℝ) - τ ω)
    rw [zero_add, sub_add_cancel] at h1
    rw [← h1]
    refine intervalIntegral.integral_congr fun u hu => ?_
    have hu0 : 0 ≤ u := by
      rw [Set.uIcc_of_le (sub_nonneg.2 hlt.le)] at hu
      exact hu.1
    show φ (B (u + τ ω).toNNReal ω) = φ (B (τ ω) ω + (B (τ ω + u.toNNReal) ω - B (τ ω) ω))
    rw [add_sub_cancel, Real.toNNReal_add hu0 (τ ω).coe_nonneg, Real.toNNReal_coe, add_comm]
  -- the restarted occupation integral is that of a fresh motion started at `B τ`
  have hinner : ∀ (s : ℝ≥0) (z : EuclideanSpace ℝ (Fin d)), (s : ℝ) < N →
      ∫ w, F ((s, z), w) ∂(P.map (restartPath B hcont fun _ => 0))
        = ∫ y, φ y * ∫ t in (0 : ℝ)..((N : ℝ) - s), brownianHeatKernel d t z y := by
    intro s z hs
    have hR0m := measurable_restartPath hm hcont (measurable_const (a := (0 : ℝ≥0)))
    have hFsec : AEStronglyMeasurable (fun w => F ((s, z), w))
        (P.map (restartPath B hcont fun _ => 0)) :=
      (hFm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    rw [integral_map hR0m.aemeasurable hFsec]
    have hC := (hB.shift 0).const_add z
    have hmC : ∀ t, Measurable fun ω => z + (B (0 + t) ω - B 0 ω) := fun t =>
      measurable_const.add ((hmB _).sub (hmB 0))
    have hcontC : ∀ ω, Continuous fun t => z + (B (0 + t) ω - B 0 ω) := fun ω =>
      continuous_const.add (((hcont ω).comp (continuous_const.add continuous_id)).sub
        continuous_const)
    rw [← hC.integral_intervalIntegral_eq hd hmC hcontC hφ hM (sub_nonneg.2 hs.le)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    show F ((s, z), restartPath B hcont (fun _ => 0) ω)
      = ∫ r in (0 : ℝ)..((N : ℝ) - s), φ (z + (B (0 + r.toNNReal) ω - B 0 ω))
    rw [hFIoc, intervalIntegral.integral_of_le (sub_nonneg.2 hs.le)]
    rfl
  -- assembly
  have hIE : Integrable (E.indicator fun ω => ∫ r in (τ ω : ℝ)..(N : ℝ), φ (B r.toNNReal ω)) P :=
    (integrable_indicator_iff hEm).2 (hFi.congr ((ae_restrict_iff' hEm).2
      (Filter.Eventually.of_forall fun ω hω => (hEq ω hω).symm)))
  simp_rw [hsplit]
  rw [integral_sub hI0 hIE, integral_indicator hEm,
    hB.integral_intervalIntegral_eq hd hmB hcont hφ hM hNR,
    setIntegral_congr_fun hEm hEq,
    IsBrownianSpace.setIntegral_restart_canonical P x B hB hm hcont τ hτ _ hY E hEτ F hFm hFi]
  rw [setIntegral_congr_fun hEm fun ω hω => hinner (τ ω) (B (τ ω) ω) (by exact_mod_cast hω)]

end LatticeProb
