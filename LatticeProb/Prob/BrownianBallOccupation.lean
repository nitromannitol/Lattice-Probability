import LatticeProb.Prob.BrownianExitDynkin
import LatticeProb.Prob.BrownianExitKelvin
import LatticeProb.Prob.BrownianOccupationTrunc
import LatticeProb.Analysis.BrownianHeatTime
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Occupation of a ball by Brownian motion

The Green kernel for the occupation measure of Brownian motion stopped on leaving a ball.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

/-- The Green kernel of a ball with centre `x`. -/
def ballGreen (d : ℕ) (s : ℝ) (x z : EuclideanSpace ℝ (Fin d)) : ℝ :=
  if ‖x - z‖ < s then
    (if d = 2 then (1 / (2 * Real.pi)) * Real.log (s / ‖x - z‖)
     else (1 / (4 * Real.pi)) * (1 / ‖x - z‖ - 1 / s))
  else 0

/-- The exit time from a ball has finite Lebesgue integral in positive dimension. -/
theorem IsBrownianSpace.lintegral_exitTime_lt_top {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {d : ℕ} (hd : 1 ≤ d) {x : EuclideanSpace ℝ (Fin d)}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} (hB : IsBrownianSpace d x B P)
    (s : ℝ) : (∫⁻ ω, exitTime B x s ω ∂P) < ∞ := by
  have := hB.isProbabilityMeasure
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
  have hsd : Real.sqrt d ≠ 0 := (Real.sqrt_pos.mpr hdpos).ne'
  have hc : (Real.sqrt d)⁻¹ ≠ 0 := inv_ne_zero hsd
  obtain ⟨C, hCm, hC, -, hCW, hcoord, hindep⟩ := hB.exists_continuousVersion
  have hμ : IsStandardBrownianLaw (P.map (pathMap C hC)) :=
    isStandardBrownianLaw_map_pathMap hCm hC hcoord hindep
  let V := (fun w : EuclideanSpace ℝ (Fin d) => x + (Real.sqrt d)⁻¹ • w) ⁻¹' Metric.ball x s
  have hVo : IsOpen V := Metric.isOpen_ball.preimage (by fun_prop)
  have hVb : Bornology.IsBounded V := isBounded_preimage_affine Metric.isBounded_ball x hc
  have hτm : Measurable (continuousExitTime V 0) := measurable_continuousExitTime hVo 0
  have hmap : Measurable (pathMap C hC) := measurable_pathMap C hCm hC
  have hτ : ∀ᵐ ω ∂P, exitTime B x s ω = continuousExitTime V 0 (pathMap C hC ω) := by
    simpa only [exitTime_eq_openExitTime_ball] using
      (ae_openExitTime_eq_continuousExitTime hd hC hCW (U := Metric.ball x s))
  have hfin := standardBrownianLaw_lintegral_continuousExitTime_lt_top hd hμ hVo hVb 0
  rw [lintegral_map hτm hmap] at hfin
  have heq : (∫⁻ ω, exitTime B x s ω ∂P) =
      ∫⁻ ω, continuousExitTime V 0 (pathMap C hC ω) ∂P := lintegral_congr_ae hτ
  rw [heq]
  exact hfin

/-- The exit time from a ball is almost surely finite in positive dimension. -/
theorem IsBrownianSpace.ae_exitTime_lt_top {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {d : ℕ} (hd : 1 ≤ d) {x : EuclideanSpace ℝ (Fin d)}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} (hB : IsBrownianSpace d x B P)
    (hm : ∀ t, StronglyMeasurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω)
    (s : ℝ) : ∀ᵐ ω ∂P, exitTime B x s ω < ∞ :=
  ae_lt_top (measurable_exitTime hm hcont x s) (hB.lintegral_exitTime_lt_top hd s).ne

/-- The exit time from a ball has finite expectation in positive dimension. -/
theorem IsBrownianSpace.integrable_exitTime {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {d : ℕ} (hd : 1 ≤ d) {x : EuclideanSpace ℝ (Fin d)}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} (hB : IsBrownianSpace d x B P)
    (hm : ∀ t, StronglyMeasurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω)
    (s : ℝ) : Integrable (fun ω => (exitTime B x s ω).toReal) P :=
  integrable_toReal_of_lintegral_ne_top (measurable_exitTime hm hcont x s).aemeasurable
    (hB.lintegral_exitTime_lt_top hd s).ne

/-- The accumulated reward of a bounded measurable function up to the exit time is integrable. -/
theorem IsBrownianSpace.integrable_occupation_exitTime {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {d : ℕ} (hd : 1 ≤ d) {x : EuclideanSpace ℝ (Fin d)}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} (hB : IsBrownianSpace d x B P)
    (hm : ∀ t, StronglyMeasurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω)
    (s : ℝ) {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : Measurable φ)
    (hb : ∃ M, ∀ z, |φ z| ≤ M) :
    Integrable (fun ω => ∫ r in (0 : ℝ)..(exitTime B x s ω).toReal,
      φ (B r.toNNReal ω)) P := by
  have := hB.isProbabilityMeasure
  obtain ⟨M, hM⟩ := hb
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  let τ : Ω → ℝ := fun ω => (exitTime B x s ω).toReal
  have hτ : Measurable τ := ENNReal.measurable_toReal.comp (measurable_exitTime hm hcont x s)
  have hτint : Integrable τ P := hB.integrable_exitTime hd hm hcont s
  have hBjoint := stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hcont hm
  have hF : Measurable (fun p : Ω × ℝ => φ (B p.2.toNNReal p.1)) :=
    hφ.comp (hBjoint.measurable.comp
      ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst))
  let A : Set (Ω × ℝ) := {p | 0 < p.2 ∧ p.2 ≤ τ p.1}
  have hA : MeasurableSet A :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (hτ.comp measurable_fst))
  have hI : StronglyMeasurable (fun ω => ∫ r in (0 : ℝ)..τ ω, φ (B r.toNNReal ω)) := by
    have h := (hF.indicator hA).stronglyMeasurable.integral_prod_right' (ν := volume)
    convert h using 1
    funext ω
    rw [intervalIntegral.integral_of_le ENNReal.toReal_nonneg]
    change (∫ r in Set.Ioc 0 (τ ω), φ (B r.toNNReal ω)) = _
    rw [← integral_indicator measurableSet_Ioc]
    rfl
  refine (hτint.const_mul M).mono' hI.aestronglyMeasurable (Filter.Eventually.of_forall ?_)
  intro ω
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := τ ω)
    (fun r _ => show ‖φ (B r.toNNReal ω)‖ ≤ M by simpa only [Real.norm_eq_abs] using hM _)
  simpa [τ, abs_of_nonneg ENNReal.toReal_nonneg, hM0] using hbound

/-- A logarithmic potential with its pole outside the closed ball satisfies the exit identity. -/
theorem IsBrownianSpace.integral_log_norm_exit_ball_of_outside {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (x : EuclideanSpace ℝ (Fin 2))
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 2)) (hB : IsBrownianSpace 2 x B P)
    {s : ℝ} {y : EuclideanSpace ℝ (Fin 2)} (hy : s < ‖y - x‖) :
    ∫ ω, Real.log ‖B (exitTime B x s ω).toNNReal ω - y‖ ∂P = Real.log ‖x - y‖ := by
  have hsub : closure (Metric.ball x s) ⊆ {y}ᶜ := by
    intro z hz hzy
    have hz' : ‖z - x‖ ≤ s := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using
        (Metric.closure_ball_subset_closedBall hz)
    have : z = y := hzy
    subst z
    linarith
  have hh : HarmonicNearClosure (fun z => Real.log ‖z - y‖) (Metric.ball x s) :=
    harmonicNearClosure_iff.2 ((harmonicOnNhd_log_norm_sub y).mono hsub)
  simpa only [exitTime_eq_openExitTime_ball] using
    (integral_openExit_harmonicNearClosure (by norm_num) hB Metric.isOpen_ball
      Metric.isBounded_ball hh)

/-- An inverse-distance potential with its pole outside the closed ball satisfies the exit identity. -/
theorem IsBrownianSpace.integral_inv_norm_exit_ball_of_outside {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (x : EuclideanSpace ℝ (Fin 3))
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 3)) (hB : IsBrownianSpace 3 x B P)
    {s : ℝ} {y : EuclideanSpace ℝ (Fin 3)} (hy : s < ‖y - x‖) :
    ∫ ω, ‖B (exitTime B x s ω).toNNReal ω - y‖⁻¹ ∂P = ‖x - y‖⁻¹ := by
  have hsub : closure (Metric.ball x s) ⊆ {y}ᶜ := by
    intro z hz hzy
    have hz' : ‖z - x‖ ≤ s := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using
        (Metric.closure_ball_subset_closedBall hz)
    have : z = y := hzy
    subst z
    linarith
  have hh : HarmonicNearClosure (fun z => ‖z - y‖⁻¹) (Metric.ball x s) :=
    harmonicNearClosure_iff.2 ((harmonicOnNhd_inv_norm_sub y).mono hsub)
  simpa only [exitTime_eq_openExitTime_ball] using
    (integral_openExit_harmonicNearClosure (by norm_num) hB Metric.isOpen_ball
      Metric.isBounded_ball hh)

/-- The ball Green kernel is measurable in its spatial argument. -/
theorem measurable_ballGreen (d : ℕ) (s : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    Measurable (ballGreen d s x) := by
  unfold ballGreen
  have hr : Measurable fun z : EuclideanSpace ℝ (Fin d) => ‖x - z‖ :=
    (continuous_const.sub continuous_id).norm.measurable
  by_cases hd : d = 2
  · simp only [hd, ↓reduceIte]
    exact Measurable.ite (measurableSet_lt hr measurable_const)
      ((measurable_const.div hr).log.const_mul _) measurable_const
  · simp only [hd, ↓reduceIte]
    exact Measurable.ite (measurableSet_lt hr measurable_const)
      (((measurable_const.div hr).sub measurable_const).const_mul _) measurable_const

/-- Away from its centre, the ball Green kernel is nonnegative. -/
theorem ballGreen_nonneg_of_ne (d : ℕ) {s : ℝ}
    {x z : EuclideanSpace ℝ (Fin d)} (hxz : x ≠ z) : 0 ≤ ballGreen d s x z := by
  have hr : 0 < ‖x - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxz)
  unfold ballGreen
  split_ifs with h h2
  · apply mul_nonneg (by positivity)
    apply Real.log_nonneg
    exact (one_le_div hr).2 h.le
  · apply mul_nonneg (by positivity)
    exact sub_nonneg.mpr (one_div_le_one_div_of_le hr h.le)
  · exact le_rfl

/-- The ball Green kernel is nonnegative almost everywhere. -/
theorem ae_ballGreen_nonneg {d : ℕ} [NeZero d] (s : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      0 ≤ ballGreen d s x z := by
  filter_upwards [Measure.ae_ne volume x] with z hz
  exact ballGreen_nonneg_of_ne d hz.symm

/-- Expected bounded rewards stopped at an integrable time are limits of their truncations. -/
theorem tendsto_integral_occupation_trunc {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {d : ℕ} {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hm : ∀ t, StronglyMeasurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω)
    {τ : Ω → ℝ≥0} (hτ : Measurable τ) (hτint : Integrable (fun ω => (τ ω : ℝ)) P)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : Measurable φ)
    (hb : ∃ M, ∀ z, |φ z| ≤ M) :
    Filter.Tendsto (fun n : ℕ => ∫ ω, (∫ r in (0 : ℝ)..((min (τ ω) n : ℝ≥0) : ℝ),
        φ (B r.toNNReal ω)) ∂P) Filter.atTop
      (nhds (∫ ω, (∫ r in (0 : ℝ)..(τ ω : ℝ), φ (B r.toNNReal ω)) ∂P)) := by
  obtain ⟨M, hM⟩ := hb
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hBjoint := stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hcont hm
  have hF : Measurable (fun p : Ω × ℝ => φ (B p.2.toNNReal p.1)) :=
    hφ.comp (hBjoint.measurable.comp
      ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst))
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (fun ω =>
      ∫ r in (0 : ℝ)..((min (τ ω) n : ℝ≥0) : ℝ), φ (B r.toNNReal ω)) P := by
    intro n
    let A : Set (Ω × ℝ) := {p | 0 < p.2 ∧ p.2 ≤ ((min (τ p.1) n : ℝ≥0) : ℝ)}
    have hA : MeasurableSet A :=
      (measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd (measurable_coe_nnreal_real.comp ((hτ.comp measurable_fst).min measurable_const)))
    have h := (hF.indicator hA).stronglyMeasurable.integral_prod_right' (ν := volume)
    apply StronglyMeasurable.aestronglyMeasurable
    convert h using 1
    funext ω
    rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg _)]
    rw [← integral_indicator measurableSet_Ioc]
    rfl
  refine tendsto_integral_of_dominated_convergence (fun ω => M * (τ ω : ℝ)) hmeas
    (hτint.const_mul M) ?_ ?_
  · intro n
    filter_upwards [] with ω
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := ((min (τ ω) n : ℝ≥0) : ℝ))
      (fun r _ => show ‖φ (B r.toNNReal ω)‖ ≤ M by simpa only [Real.norm_eq_abs] using hM _)
    calc
      _ ≤ M * ((min (τ ω) n : ℝ≥0) : ℝ) := by
        simpa only [sub_zero, abs_of_nonneg (NNReal.coe_nonneg (min (τ ω) n))] using hbound
      _ ≤ M * (τ ω : ℝ) := mul_le_mul_of_nonneg_left (by exact_mod_cast min_le_left (τ ω) n) hM0
  · filter_upwards [] with ω
    obtain ⟨N, hN⟩ := exists_nat_gt (τ ω : ℝ)
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    have hnτ : τ ω ≤ (n : ℝ≥0) := by exact_mod_cast (le_trans hN.le (Nat.cast_le.mpr hn))
    simp only [min_eq_left hnτ]

/-- The time-integrated heat kernel is integrable in space and has mass `T`. -/
theorem IsBrownianSpace.integrable_greenTime_and_integral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {d : ℕ} (hd : 1 ≤ d) {x : EuclideanSpace ℝ (Fin d)}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} (hB : IsBrownianSpace d x B P)
    (hm : ∀ t, Measurable (B t)) {T : ℝ} (hT : 0 ≤ T) :
    Integrable (fun y => ∫ t in (0 : ℝ)..T, brownianHeatKernel d t x y) ∧
      (∫ y, ∫ t in (0 : ℝ)..T, brownianHeatKernel d t x y) = T := by
  have : IsProbabilityMeasure P := hB.isProbabilityMeasure
  have hk : Measurable fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
      brownianHeatKernel d p.1 x p.2 := by
    unfold brownianHeatKernel
    fun_prop
  have hk0 : ∀ t, 0 ≤ t → ∀ y, 0 ≤ brownianHeatKernel d t x y :=
    fun t ht y => brownianHeatKernel_nonneg ht x y
  have hkint : ∀ r : ℝ, 0 < r → Integrable (fun y => brownianHeatKernel d r x y) ∧
      ∫ y, brownianHeatKernel d r x y = 1 := fun r hr => by
    have hdens : P.map (B r.toNNReal) = volume.withDensity
        (fun y => ENNReal.ofReal (brownianHeatKernel d r x y)) := by
      rw [hB.map_eq_withDensity P hd x B hm r.toNNReal (Real.toNNReal_pos.2 hr),
        Real.coe_toNNReal r hr.le]
    have hm1 : ∫⁻ y, ENNReal.ofReal (brownianHeatKernel d r x y) = 1 := by
      have h := congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin d)) => μ Set.univ) hdens
      simp only [Measure.map_apply (hm _) MeasurableSet.univ, Set.preimage_univ, measure_univ,
        withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
      exact h.symm
    have hmeas : Measurable fun y => brownianHeatKernel d r x y :=
      hk.comp (measurable_const.prodMk measurable_id)
    refine ⟨⟨hmeas.aestronglyMeasurable, ?_⟩, ?_⟩
    · rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (hk0 r hr.le)), hm1]
      exact ENNReal.one_lt_top
    · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (hk0 r hr.le))
        hmeas.aestronglyMeasurable, hm1, ENNReal.toReal_one]
  have hint : Integrable (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
      brownianHeatKernel d p.1 x p.2) ((volume.restrict (Set.Ioc (0 : ℝ) T)).prod volume) := by
    refine (integrable_prod_iff hk.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · exact (ae_restrict_iff' measurableSet_Ioc).2
        (Filter.Eventually.of_forall fun r hr => (hkint r hr.1).1)
    · refine (integrable_const (1 : ℝ)).mono' hk.aestronglyMeasurable.norm.integral_prod_right' ?_
      refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun r hr => ?_)
      have heq : (∫ y, ‖brownianHeatKernel d r x y‖) = 1 := by
        simp_rw [Real.norm_eq_abs, abs_of_nonneg (hk0 r hr.1.le _)]
        exact (hkint r hr.1).2
      change ‖(∫ y, ‖brownianHeatKernel d r x y‖)‖ ≤ (1 : ℝ)
      rw [heq, Real.norm_eq_abs, abs_one]
  constructor
  · simpa only [intervalIntegral.integral_of_le hT] using hint.integral_prod_right
  · simp_rw [intervalIntegral.integral_of_le hT]
    have hint' : Integrable (Function.uncurry fun y t => brownianHeatKernel d t x y)
        (volume.prod (volume.restrict (Set.Ioc (0 : ℝ) T))) := hint.swap
    rw [integral_integral_swap hint']
    have heq : (∫ r in Set.Ioc (0 : ℝ) T, ∫ y, brownianHeatKernel d r x y) =
        ∫ r in Set.Ioc (0 : ℝ) T, (1 : ℝ) := by
      refine setIntegral_congr_fun measurableSet_Ioc ?_
      intro r hr
      exact (hkint r hr.1).2
    rw [heq, setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le hT]
    simp

/-- Time-integrated heat kernels have finite mass for every starting point. -/
theorem IsBrownianSpace.integrable_greenTime_and_integral_of_start {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ} (hd : 1 ≤ d)
    {x : EuclideanSpace ℝ (Fin d)} {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hB : IsBrownianSpace d x B P) (hm : ∀ t, Measurable (B t))
    (z : EuclideanSpace ℝ (Fin d)) {T : ℝ} (hT : 0 ≤ T) :
    Integrable (fun y => ∫ t in (0 : ℝ)..T, brownianHeatKernel d t z y) ∧
      (∫ y, ∫ t in (0 : ℝ)..T, brownianHeatKernel d t z y) = T := by
  have hC := (hB.shift 0).const_add z
  apply hC.integrable_greenTime_and_integral hd _ hT
  intro t
  exact measurable_const.add ((hm (0 + t)).sub (hm 0))

/-- The time-integrated heat kernel is jointly measurable in time and both spatial variables. -/
theorem measurable_greenTime (d : ℕ) : Measurable (fun p :
    (ℝ≥0 × EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) =>
      ∫ t in (0 : ℝ)..(p.1 : ℝ), brownianHeatKernel d t p.2.1 p.2.2) := by
  let A : Set ((ℝ≥0 × EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) × ℝ) :=
    {p | 0 < p.2 ∧ p.2 ≤ (p.1.1 : ℝ)}
  have hA : MeasurableSet A :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_coe_nnreal_real.comp
        (measurable_fst.comp measurable_fst)))
  have hk : Measurable (fun p :
      (ℝ≥0 × EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) × ℝ =>
        brownianHeatKernel d p.2 p.1.2.1 p.1.2.2) := by
    unfold brownianHeatKernel
    fun_prop
  have h := (hk.indicator hA).stronglyMeasurable.integral_prod_right' (ν := volume)
  apply StronglyMeasurable.measurable
  convert h using 1
  funext p
  rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg p.1)]
  rw [← integral_indicator measurableSet_Ioc]
  rfl

/-- Heat kernels with a bounded random time and measurable random starting point are integrable
on the product of the probability space and Euclidean space. -/
theorem IsBrownianSpace.integrable_random_greenTime {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {d : ℕ} (hd : 1 ≤ d) {x : EuclideanSpace ℝ (Fin d)}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} (hB : IsBrownianSpace d x B P)
    (hm : ∀ t, Measurable (B t)) {u : Ω → ℝ≥0} (hu : Measurable u)
    {a : Ω → EuclideanSpace ℝ (Fin d)} (ha : Measurable a) {N : ℝ≥0}
    (huN : ∀ ω, u ω ≤ N) :
    Integrable (fun p : Ω × EuclideanSpace ℝ (Fin d) =>
      ∫ t in (0 : ℝ)..(u p.1 : ℝ), brownianHeatKernel d t (a p.1) p.2) (P.prod volume) := by
  have : IsProbabilityMeasure P := hB.isProbabilityMeasure
  have hq : Measurable (fun p : Ω × EuclideanSpace ℝ (Fin d) =>
      ∫ t in (0 : ℝ)..(u p.1 : ℝ), brownianHeatKernel d t (a p.1) p.2) := by
    exact (measurable_greenTime d).comp
      ((hu.comp measurable_fst).prodMk ((ha.comp measurable_fst).prodMk measurable_snd))
  have hnonneg : ∀ ω y, 0 ≤ ∫ t in (0 : ℝ)..(u ω : ℝ),
      brownianHeatKernel d t (a ω) y := by
    intro ω y
    apply intervalIntegral.integral_nonneg (NNReal.coe_nonneg _)
    intro t ht
    exact brownianHeatKernel_nonneg ht.1 _ _
  have hmass : ∀ ω, Integrable (fun y => ∫ t in (0 : ℝ)..(u ω : ℝ),
      brownianHeatKernel d t (a ω) y) ∧
      (∫ y, ∫ t in (0 : ℝ)..(u ω : ℝ), brownianHeatKernel d t (a ω) y) = u ω :=
    fun ω => hB.integrable_greenTime_and_integral_of_start hd hm (a ω) (NNReal.coe_nonneg _)
  refine (integrable_prod_iff hq.aestronglyMeasurable).2 ⟨?_, ?_⟩
  · exact Filter.Eventually.of_forall fun ω => (hmass ω).1
  · refine (integrable_const (N : ℝ)).mono' hq.aestronglyMeasurable.norm.integral_prod_right' ?_
    filter_upwards [] with ω
    have heq : (∫ y, ‖∫ t in (0 : ℝ)..(u ω : ℝ), brownianHeatKernel d t (a ω) y‖) =
        (u ω : ℝ) := by
      simp_rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg ω _)]
      exact (hmass ω).2
    change ‖(∫ y, ‖∫ t in (0 : ℝ)..(u ω : ℝ), brownianHeatKernel d t (a ω) y‖)‖ ≤ (N : ℝ)
    rw [heq, Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]
    exact_mod_cast huN ω

/-- A bounded spatial weight may be taken outside the expectation of an integrable kernel. -/
theorem integral_setIntegral_mul_kernel {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
    {q : Ω × EuclideanSpace ℝ (Fin d) → ℝ}
    (hq : Integrable q (P.prod volume)) (E : Set Ω)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : Measurable φ)
    (hb : ∃ M, ∀ z, |φ z| ≤ M) :
    (∫ ω in E, ∫ y, φ y * q (ω, y) ∂volume ∂P) =
      ∫ y, φ y * ∫ ω in E, q (ω, y) ∂P := by
  obtain ⟨M, hM⟩ := hb
  have hqE : Integrable q ((P.restrict E).prod volume) :=
    hq.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hI : Integrable (Function.uncurry fun ω y => φ y * q (ω, y))
      ((P.restrict E).prod volume) := by
    apply hqE.bdd_mul ((hφ.comp measurable_snd).aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun p => by
      simpa only [Real.norm_eq_abs, Function.comp_apply] using hM p.2
  rw [integral_integral_swap hI]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [integral_const_mul]

/-- The finite-horizon density of occupation before a stopping time. -/
def stoppedHeatDensity {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (x : EuclideanSpace ℝ (Fin d))
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (τ : Ω → ℝ≥0) (N : ℝ≥0)
    (y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (∫ t in (0 : ℝ)..(N : ℝ), brownianHeatKernel d t x y) -
    ∫ ω in {ω | τ ω < N}, (∫ t in (0 : ℝ)..((N - τ ω : ℝ≥0) : ℝ),
      brownianHeatKernel d t (B (τ ω) ω) y) ∂P

/-- The finite-horizon stopped heat density is integrable. -/
theorem IsBrownianSpace.integrable_stoppedHeatDensity {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {d : ℕ} (hd : 1 ≤ d) {x : EuclideanSpace ℝ (Fin d)}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} (hB : IsBrownianSpace d x B P)
    (hm : ∀ t, StronglyMeasurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω)
    {τ : Ω → ℝ≥0} (hτ : Measurable τ) (N : ℝ≥0) :
    Integrable (stoppedHeatDensity P x B τ N) := by
  have : IsProbabilityMeasure P := hB.isProbabilityMeasure
  have hA : Measurable fun ω => B (τ ω) ω := by
    have h := stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hcont hm
    exact h.measurable.comp (hτ.prodMk measurable_id)
  have hu : Measurable fun ω => N - τ ω := measurable_const.sub hτ
  have huN : ∀ ω, N - τ ω ≤ N := fun ω => tsub_le_self
  let q : Ω × EuclideanSpace ℝ (Fin d) → ℝ := fun p =>
    ∫ t in (0 : ℝ)..((N - τ p.1 : ℝ≥0) : ℝ), brownianHeatKernel d t (B (τ p.1) p.1) p.2
  have hq : Integrable q (P.prod volume) :=
    hB.integrable_random_greenTime hd (fun t => (hm t).measurable)
      (u := fun ω => N - τ ω) (a := fun ω => B (τ ω) ω) (N := N) hu hA huN
  let E : Set Ω := {ω | τ ω < N}
  have hqE : Integrable q ((P.restrict E).prod volume) :=
    hq.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hq1 : Integrable (fun y => ∫ t in (0 : ℝ)..(N : ℝ), brownianHeatKernel d t x y) :=
    (hB.integrable_greenTime_and_integral hd (fun t => (hm t).measurable) (NNReal.coe_nonneg _)).1
  have hq2 : Integrable (fun y => ∫ ω in E, q (ω, y) ∂P) := hqE.integral_prod_right
  exact hq1.sub hq2

/-- The finite-horizon stopped occupation measure has the stopped heat density. -/
theorem IsBrownianSpace.integral_occupation_stoppedHeatDensity {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (hd : 1 ≤ d)
    (x : EuclideanSpace ℝ (Fin d)) (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (hB : IsBrownianSpace d x B P) (hm : ∀ t, StronglyMeasurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (natFiltration B hm) (fun ω => (τ ω : ℝ≥0∞))) (N : ℝ≥0)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : Measurable φ)
    (hb : ∃ M, ∀ y, |φ y| ≤ M) :
    Integrable (stoppedHeatDensity P x B τ N) ∧
    (∫ ω, (∫ r in (0 : ℝ)..((min (τ ω) N : ℝ≥0) : ℝ), φ (B r.toNNReal ω)) ∂P) =
      ∫ y, φ y * stoppedHeatDensity P x B τ N y := by
  have hτm : Measurable τ := measurable_of_isStoppingTime hτ
  have hA : Measurable fun ω => B (τ ω) ω := by
    have h := stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hcont hm
    exact h.measurable.comp (hτm.prodMk measurable_id)
  have hu : Measurable fun ω => N - τ ω := measurable_const.sub hτm
  have huN : ∀ ω, N - τ ω ≤ N := fun ω => tsub_le_self
  let q : Ω × EuclideanSpace ℝ (Fin d) → ℝ := fun p =>
    ∫ t in (0 : ℝ)..((N - τ p.1 : ℝ≥0) : ℝ), brownianHeatKernel d t (B (τ p.1) p.1) p.2
  have hq : Integrable q (P.prod volume) :=
    hB.integrable_random_greenTime hd (fun t => (hm t).measurable)
      (u := fun ω => N - τ ω) (a := fun ω => B (τ ω) ω) (N := N) hu hA huN
  let E : Set Ω := {ω | τ ω < N}
  have hqE : Integrable q ((P.restrict E).prod volume) :=
    hq.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hq1 : Integrable (fun y => ∫ t in (0 : ℝ)..(N : ℝ), brownianHeatKernel d t x y) :=
    (hB.integrable_greenTime_and_integral hd (fun t => (hm t).measurable) (NNReal.coe_nonneg _)).1
  have hq2 : Integrable (fun y => ∫ ω in E, q (ω, y) ∂P) := hqE.integral_prod_right
  have hden : Integrable (stoppedHeatDensity P x B τ N) := hq1.sub hq2
  refine ⟨hden, ?_⟩
  have htrunc := hB.integral_occupation_trunc P hd x B hm hcont τ hτ φ hφ hb N
  have hrem : (∫ ω in E, (∫ y, φ y * ∫ t in (0 : ℝ)..((N : ℝ) - τ ω),
      brownianHeatKernel d t (B (τ ω) ω) y) ∂P) =
      ∫ y, φ y * ∫ ω in E, q (ω, y) ∂P := by
    rw [← integral_setIntegral_mul_kernel hq E hφ hb]
    apply setIntegral_congr_fun (measurableSet_lt hτm measurable_const)
    intro ω hω
    simp only [q, NNReal.coe_sub hω.le]
  rw [hrem] at htrunc
  obtain ⟨M, hM⟩ := hb
  have hweight : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), ‖φ y‖ ≤ M :=
    Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hM y
  have hi1 := hq1.bdd_mul hφ.aestronglyMeasurable hweight
  have hi2 := hq2.bdd_mul hφ.aestronglyMeasurable hweight
  rw [← integral_sub hi1 hi2] at htrunc
  convert htrunc using 1
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [stoppedHeatDensity, E, q, mul_sub]

/-- The finite-horizon stopped heat density is nonnegative almost everywhere. -/
theorem IsBrownianSpace.ae_nonneg_stoppedHeatDensity {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (hd : 1 ≤ d)
    (x : EuclideanSpace ℝ (Fin d)) (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (hB : IsBrownianSpace d x B P) (hm : ∀ t, StronglyMeasurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (natFiltration B hm) (fun ω => (τ ω : ℝ≥0∞))) (N : ℝ≥0) :
    0 ≤ᵐ[volume] stoppedHeatDensity P x B τ N := by
  have hτm : Measurable τ := measurable_of_isStoppingTime hτ
  apply ae_nonneg_of_forall_setIntegral_nonneg (hB.integrable_stoppedHeatDensity hd hm hcont hτm N)
  intro E hE hEfin
  let φ : EuclideanSpace ℝ (Fin d) → ℝ := E.indicator (fun _ => 1)
  have hφ : Measurable φ := measurable_const.indicator hE
  have hφ0 : ∀ z, 0 ≤ φ z := by
    intro z
    by_cases hz : z ∈ E <;> simp [φ, hz]
  have hφb : ∃ M, ∀ z, |φ z| ≤ M := by
    refine ⟨1, fun z => ?_⟩
    by_cases hz : z ∈ E <;> simp [φ, hz]
  have heq := (hB.integral_occupation_stoppedHeatDensity P hd x B hm hcont τ hτ N hφ hφb).2
  have hrew : 0 ≤ ∫ ω, (∫ r in (0 : ℝ)..((min (τ ω) N : ℝ≥0) : ℝ),
      φ (B r.toNNReal ω)) ∂P := by
    apply integral_nonneg
    intro ω
    exact intervalIntegral.integral_nonneg (NNReal.coe_nonneg _) fun r _ => hφ0 _
  rw [heq] at hrew
  convert hrew using 1
  rw [← integral_indicator hE]
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : y ∈ E <;> simp [φ, hy]

/-- A bounded reward accumulated up to a bounded measurable time is integrable. -/
theorem integrable_occupation_of_bounded_time {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} (hm : ∀ t, StronglyMeasurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) {u : Ω → ℝ≥0} (hu : Measurable u)
    {N : ℝ≥0} (huN : ∀ ω, u ω ≤ N) {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : Measurable φ) (hb : ∃ M, ∀ y, |φ y| ≤ M) :
    Integrable (fun ω => ∫ r in (0 : ℝ)..(u ω : ℝ), φ (B r.toNNReal ω)) P := by
  obtain ⟨M, hM⟩ := hb
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hBjoint := stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hcont hm
  have hF : Measurable (fun p : Ω × ℝ => φ (B p.2.toNNReal p.1)) :=
    hφ.comp (hBjoint.measurable.comp
      ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst))
  let A : Set (Ω × ℝ) := {p | 0 < p.2 ∧ p.2 ≤ (u p.1 : ℝ)}
  have hA : MeasurableSet A :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_coe_nnreal_real.comp (hu.comp measurable_fst)))
  have hmeas : StronglyMeasurable (fun ω =>
      ∫ r in (0 : ℝ)..(u ω : ℝ), φ (B r.toNNReal ω)) := by
    have h := (hF.indicator hA).stronglyMeasurable.integral_prod_right' (ν := volume)
    convert h using 1
    funext ω
    rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg _)]
    rw [← integral_indicator measurableSet_Ioc]
    rfl
  refine (integrable_const (M * (N : ℝ))).mono' hmeas.aestronglyMeasurable ?_
  filter_upwards [] with ω
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := (u ω : ℝ))
    (fun r _ => show ‖φ (B r.toNNReal ω)‖ ≤ M by simpa only [Real.norm_eq_abs] using hM _)
  calc
    _ ≤ M * (u ω : ℝ) := by
      simpa only [sub_zero, abs_of_nonneg (NNReal.coe_nonneg (u ω))] using hbound
    _ ≤ M * (N : ℝ) := mul_le_mul_of_nonneg_left (by exact_mod_cast huN ω) hM0

/-- Stopped heat densities increase almost everywhere with the time horizon. -/
theorem IsBrownianSpace.ae_stoppedHeatDensity_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (hd : 1 ≤ d)
    (x : EuclideanSpace ℝ (Fin d)) (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (hB : IsBrownianSpace d x B P) (hm : ∀ t, StronglyMeasurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (natFiltration B hm) (fun ω => (τ ω : ℝ≥0∞)))
    {N M : ℝ≥0} (hNM : N ≤ M) :
    stoppedHeatDensity P x B τ N ≤ᵐ[volume] stoppedHeatDensity P x B τ M := by
  have hτm : Measurable τ := measurable_of_isStoppingTime hτ
  apply ae_le_of_forall_setIntegral_le
    (hB.integrable_stoppedHeatDensity hd hm hcont hτm N)
    (hB.integrable_stoppedHeatDensity hd hm hcont hτm M)
  intro E hE hEfin
  let φ : EuclideanSpace ℝ (Fin d) → ℝ := E.indicator (fun _ => 1)
  have hφ : Measurable φ := measurable_const.indicator hE
  have hφ0 : ∀ z, 0 ≤ φ z := by
    intro z
    by_cases hz : z ∈ E <;> simp [φ, hz]
  have hφb : ∃ C, ∀ z, |φ z| ≤ C := by
    refine ⟨1, fun z => ?_⟩
    by_cases hz : z ∈ E <;> simp [φ, hz]
  have hN := (hB.integral_occupation_stoppedHeatDensity P hd x B hm hcont τ hτ N hφ hφb).2
  have hM := (hB.integral_occupation_stoppedHeatDensity P hd x B hm hcont τ hτ M hφ hφb).2
  have heq : ∀ K : ℝ≥0, (∫ y, φ y * stoppedHeatDensity P x B τ K y) =
      ∫ y in E, stoppedHeatDensity P x B τ K y := by
    intro K
    rw [← integral_indicator hE]
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : y ∈ E <;> simp [φ, hy]
  rw [heq] at hN hM
  rw [← hN, ← hM]
  have hiN := integrable_occupation_of_bounded_time (P := P) hm hcont (hτm.min measurable_const)
    (u := fun ω => min (τ ω) N) (N := N) (fun ω => min_le_right _ _) hφ hφb
  have hiM := integrable_occupation_of_bounded_time (P := P) hm hcont (hτm.min measurable_const)
    (u := fun ω => min (τ ω) M) (N := M) (fun ω => min_le_right _ _) hφ hφb
  refine integral_mono_ae hiN hiM (Filter.Eventually.of_forall fun ω => ?_)
  have hpath : Measurable fun r : ℝ => φ (B r.toNNReal ω) :=
    hφ.comp ((hcont ω).measurable.comp measurable_real_toNNReal)
  have hII : IntervalIntegrable (fun r : ℝ => φ (B r.toNNReal ω)) volume 0 (min (τ ω) M : ℝ≥0) := by
    refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun' hpath.aestronglyMeasurable ?_
    filter_upwards [] with r
    rw [Real.norm_eq_abs]
    dsimp [φ]
    by_cases hr : B r.toNNReal ω ∈ E <;> simp [hr]
  apply intervalIntegral.integral_mono_interval le_rfl (NNReal.coe_nonneg _) ?_
    (Filter.Eventually.of_forall fun r => hφ0 _) hII
  exact_mod_cast min_le_min_left (τ ω) hNM

/-- Before a horizon, truncating an exit time at a later time does not alter it. -/
theorem exitTimeTrunc_lt_iff {Ω : Type*} {d : ℕ}
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (x : EuclideanSpace ℝ (Fin d))
    (s : ℝ) {N M : ℝ≥0} (hNM : N ≤ M) (ω : Ω) :
    exitTimeTrunc B x s M ω < N ↔ exitTime B x s ω < (N : ℝ≥0∞) := by
  rw [← ENNReal.coe_lt_coe, coe_exitTimeTrunc, min_lt_iff]
  simp only [ENNReal.coe_lt_coe, not_lt_of_ge hNM, or_false]

/-- Exit-time truncations at two horizons agree when the exit occurs before both. -/
theorem exitTimeTrunc_eq_of_lt {Ω : Type*} {d : ℕ}
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (x : EuclideanSpace ℝ (Fin d))
    (s : ℝ) {N M : ℝ≥0} (hNM : N ≤ M) (ω : Ω)
    (h : exitTimeTrunc B x s M ω < N) :
    exitTimeTrunc B x s M ω = exitTimeTrunc B x s N ω := by
  have he : exitTime B x s ω < (N : ℝ≥0∞) := (exitTimeTrunc_lt_iff B x s hNM ω).1 h
  apply ENNReal.coe_injective
  rw [coe_exitTimeTrunc, coe_exitTimeTrunc, inf_eq_left.mpr he.le,
    inf_eq_left.mpr (he.le.trans (by exact_mod_cast hNM))]

/-- The stopped heat density does not depend on a later exit-time truncation. -/
theorem stoppedHeatDensity_exitTimeTrunc_eq {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (x : EuclideanSpace ℝ (Fin d))
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (hm : ∀ t, StronglyMeasurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω)
    (s : ℝ) {N M : ℝ≥0} (hNM : N ≤ M) :
    stoppedHeatDensity P x B (exitTimeTrunc B x s M) N =
      stoppedHeatDensity P x B (exitTimeTrunc B x s N) N := by
  have hevent : {ω | exitTimeTrunc B x s M ω < N} =
      {ω | exitTimeTrunc B x s N ω < N} := by
    ext ω
    exact (exitTimeTrunc_lt_iff B x s hNM ω).trans
      (exitTimeTrunc_lt_iff B x s le_rfl ω).symm
  funext y
  unfold stoppedHeatDensity
  congr 1
  rw [← hevent]
  apply setIntegral_congr_fun
    (measurableSet_lt (measurable_exitTimeTrunc hm hcont x s M) measurable_const)
  intro ω hω
  dsimp only
  rw [exitTimeTrunc_eq_of_lt B x s hNM ω hω]

/-- The finite-horizon occupation density for exit from a ball. -/
def exitHeatDensity {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (x : EuclideanSpace ℝ (Fin d))
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (s : ℝ) (N : ℝ≥0) :
    EuclideanSpace ℝ (Fin d) → ℝ :=
  stoppedHeatDensity P x B (exitTimeTrunc B x s N) N

/-- Exit occupation densities are nonnegative almost everywhere. -/
theorem IsBrownianSpace.ae_nonneg_exitHeatDensity {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (hd : 1 ≤ d)
    (x : EuclideanSpace ℝ (Fin d)) (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (hB : IsBrownianSpace d x B P) (hm : ∀ t, StronglyMeasurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) (s : ℝ) (N : ℝ≥0) :
    0 ≤ᵐ[volume] exitHeatDensity P x B s N :=
  hB.ae_nonneg_stoppedHeatDensity P hd x B hm hcont (exitTimeTrunc B x s N)
    (isStoppingTime_exitTimeTrunc hm hcont x s N) N

/-- Exit occupation densities increase almost everywhere with the horizon. -/
theorem IsBrownianSpace.ae_exitHeatDensity_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (hd : 1 ≤ d)
    (x : EuclideanSpace ℝ (Fin d)) (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (hB : IsBrownianSpace d x B P) (hm : ∀ t, StronglyMeasurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) (s : ℝ) {N M : ℝ≥0} (hNM : N ≤ M) :
    exitHeatDensity P x B s N ≤ᵐ[volume] exitHeatDensity P x B s M := by
  have h := hB.ae_stoppedHeatDensity_le P hd x B hm hcont (exitTimeTrunc B x s M)
    (isStoppingTime_exitTimeTrunc hm hcont x s M) hNM
  rw [stoppedHeatDensity_exitTimeTrunc_eq P x B hm hcont s hNM] at h
  exact h

/-- Expected rewards accumulated until truncated exit converge to the exit reward. -/
theorem IsBrownianSpace.tendsto_integral_occupation_exitTimeTrunc {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ} (hd : 1 ≤ d)
    {x : EuclideanSpace ℝ (Fin d)} {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hB : IsBrownianSpace d x B P) (hm : ∀ t, StronglyMeasurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) (s : ℝ)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : Measurable φ)
    (hb : ∃ M, ∀ y, |φ y| ≤ M) :
    Filter.Tendsto (fun n : ℕ => ∫ ω,
      (∫ r in (0 : ℝ)..(exitTimeTrunc B x s n ω : ℝ), φ (B r.toNNReal ω)) ∂P)
      Filter.atTop (nhds (∫ ω, (∫ r in (0 : ℝ)..(exitTime B x s ω).toReal,
        φ (B r.toNNReal ω)) ∂P)) := by
  have hτm : Measurable fun ω => (exitTime B x s ω).toNNReal :=
    ENNReal.measurable_toNNReal.comp (measurable_exitTime hm hcont x s)
  have hτi : Integrable (fun ω => ((exitTime B x s ω).toNNReal : ℝ)) P :=
    hB.integrable_exitTime hd hm hcont s
  have ht := tendsto_integral_occupation_trunc hm hcont hτm hτi hφ hb
  convert ht using 1
  funext n
  apply integral_congr_ae
  filter_upwards [hB.ae_exitTime_lt_top hd hm hcont s] with ω hω
  have heq : exitTimeTrunc B x s n ω = min (exitTime B x s ω).toNNReal n := by
    apply ENNReal.coe_injective
    rw [coe_exitTimeTrunc]
    simp only [ENNReal.coe_min, ENNReal.coe_toNNReal hω.ne, ENNReal.coe_natCast]
  · rw [heq]
  · simp only [ENNReal.coe_toNNReal_eq_toReal]

/-- The exit occupation density is expressed using the exit time and exit position. -/
theorem exitHeatDensity_eq {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (x : EuclideanSpace ℝ (Fin d))
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (hm : ∀ t, StronglyMeasurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω)
    (s : ℝ) (N : ℝ≥0) (y : EuclideanSpace ℝ (Fin d)) :
    exitHeatDensity P x B s N y =
      (∫ t in (0 : ℝ)..(N : ℝ), brownianHeatKernel d t x y) -
      ∫ ω in {ω | exitTime B x s ω < (N : ℝ≥0∞)},
        (∫ t in (0 : ℝ)..((N : ℝ) - (exitTime B x s ω).toReal),
          brownianHeatKernel d t (B (exitTime B x s ω).toNNReal ω) y) ∂P := by
  unfold exitHeatDensity stoppedHeatDensity
  congr 1
  have hevent : {ω | exitTimeTrunc B x s N ω < N} =
      {ω | exitTime B x s ω < (N : ℝ≥0∞)} := by
    ext ω
    exact exitTimeTrunc_lt_iff B x s le_rfl ω
  rw [← hevent]
  apply setIntegral_congr_fun
    (measurableSet_lt (measurable_exitTimeTrunc hm hcont x s N) measurable_const)
  intro ω hω
  have he : exitTime B x s ω < (N : ℝ≥0∞) :=
    (exitTimeTrunc_lt_iff B x s le_rfl ω).1 hω
  have heq : exitTimeTrunc B x s N ω = (exitTime B x s ω).toNNReal := by
    simp only [exitTimeTrunc, inf_eq_left.mpr he.le]
  dsimp only
  rw [NNReal.coe_sub hω.le, heq, ENNReal.coe_toNNReal_eq_toReal]

/-- A point away from the boundary sphere stays uniformly away from the exit position. -/
theorem IsBrownianSpace.ae_exit_distance_lower_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {d : ℕ} (hd : 1 ≤ d) {x : EuclideanSpace ℝ (Fin d)}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} (hB : IsBrownianSpace d x B P)
    {s : ℝ} (hs : 0 < s) (y : EuclideanSpace ℝ (Fin d)) :
    ∀ᵐ ω ∂P, |‖y - x‖ - s| ≤ ‖B (exitTime B x s ω).toNNReal ω - y‖ := by
  have h := hB.ae_mem_sphere_openExitTime_ball hd hs
  simp_rw [← exitTime_eq_openExitTime_ball] at h
  filter_upwards [h] with ω hω
  have hn : ‖B (exitTime B x s ω).toNNReal ω - x‖ = s := mem_sphere_iff_norm.1 hω
  have hd := abs_norm_sub_norm_le (y - x) (B (exitTime B x s ω).toNNReal ω - x)
  rw [hn] at hd
  have heq : y - x - (B (exitTime B x s ω).toNNReal ω - x) =
      y - B (exitTime B x s ω).toNNReal ω := by abel
  rw [heq] at hd
  simpa only [norm_sub_rev] using hd

/-- In dimension three, finite-horizon heat integrals are bounded by the Newtonian kernel. -/
theorem intervalIntegral_brownianHeatKernel_three_le {x y : EuclideanSpace ℝ (Fin 3)}
    (hxy : x ≠ y) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, brownianHeatKernel 3 t x y) ≤ 3 / (2 * Real.pi * ‖x - y‖) := by
  rw [intervalIntegral.integral_of_le hT, ← integral_brownianHeatKernel_three hxy]
  apply setIntegral_mono_set (integrableOn_brownianHeatKernel_three hxy)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact brownianHeatKernel_nonneg ht.le x y
  · exact Filter.Eventually.of_forall fun t ht => ht.1

/-- The finite-horizon heat integral is uniformly bounded away from the pole in dimension three. -/
theorem intervalIntegral_brownianHeatKernel_three_le_of_distance
    {x y : EuclideanSpace ℝ (Fin 3)} {δ : ℝ} (hδ : 0 < δ) (hxy : δ ≤ ‖x - y‖)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, brownianHeatKernel 3 t x y) ≤ 3 / (2 * Real.pi * δ) := by
  have hr : 0 < ‖x - y‖ := hδ.trans_le hxy
  have hne : x ≠ y := sub_ne_zero.mp (norm_pos_iff.mp hr)
  refine (intervalIntegral_brownianHeatKernel_three_le hne hT).trans ?_
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  exact mul_le_mul_of_nonneg_left hxy (by positivity)

/-- In dimension three, the expected remaining heat integral converges to the exit potential. -/
theorem IsBrownianSpace.tendsto_integral_greenTime_exit_three {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (x : EuclideanSpace ℝ (Fin 3))
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 3)) (hB : IsBrownianSpace 3 x B P)
    (hm : ∀ t, StronglyMeasurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω)
    {s : ℝ} (hs : 0 < s) (y : EuclideanSpace ℝ (Fin 3)) (hy : ‖y - x‖ ≠ s) :
    Filter.Tendsto (fun n : ℕ => ∫ ω,
      (∫ t in (0 : ℝ)..(((n : ℝ≥0) - (exitTime B x s ω).toNNReal : ℝ≥0) : ℝ),
        brownianHeatKernel 3 t (B (exitTime B x s ω).toNNReal ω) y) ∂P) Filter.atTop
      (nhds (∫ ω, 3 / (2 * Real.pi * ‖B (exitTime B x s ω).toNNReal ω - y‖) ∂P)) := by
  let τ : Ω → ℝ≥0 := fun ω => (exitTime B x s ω).toNNReal
  let a : Ω → EuclideanSpace ℝ (Fin 3) := fun ω => B (τ ω) ω
  let δ : ℝ := |‖y - x‖ - s|
  have hδ : 0 < δ := abs_pos.mpr (sub_ne_zero.mpr hy)
  have hτ : Measurable τ := ENNReal.measurable_toNNReal.comp (measurable_exitTime hm hcont x s)
  have ha : Measurable a := by
    have hj := stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hcont hm
    exact hj.measurable.comp (hτ.prodMk measurable_id)
  have hmG : ∀ n : ℕ, AEStronglyMeasurable (fun ω =>
      ∫ t in (0 : ℝ)..(((n : ℝ≥0) - τ ω : ℝ≥0) : ℝ), brownianHeatKernel 3 t (a ω) y) P := by
    intro n
    exact ((measurable_greenTime 3).comp
      (((measurable_const.sub hτ).prodMk (ha.prodMk measurable_const)))).aestronglyMeasurable
  refine tendsto_integral_of_dominated_convergence (fun _ => 3 / (2 * Real.pi * δ)) hmG
    (integrable_const _) ?_ ?_
  · intro n
    filter_upwards [hB.ae_exit_distance_lower_bound (by norm_num) hs y] with ω hdist
    have hq0 : 0 ≤ ∫ t in (0 : ℝ)..(((n : ℝ≥0) - τ ω : ℝ≥0) : ℝ),
        brownianHeatKernel 3 t (a ω) y := by
      apply intervalIntegral.integral_nonneg (NNReal.coe_nonneg _)
      intro t ht
      exact brownianHeatKernel_nonneg ht.1 _ _
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact intervalIntegral_brownianHeatKernel_three_le_of_distance hδ hdist (NNReal.coe_nonneg _)
  · filter_upwards [hB.ae_exit_distance_lower_bound (by norm_num) hs y] with ω hdist
    have hne : a ω ≠ y := sub_ne_zero.mp (norm_pos_iff.mp (hδ.trans_le hdist))
    have ht : Filter.Tendsto (fun n : ℕ => (((n : ℝ≥0) - τ ω : ℝ≥0) : ℝ))
        Filter.atTop Filter.atTop := by
      apply Filter.tendsto_atTop.2
      intro R
      obtain ⟨N, hN⟩ := exists_nat_gt (max R 0 + (τ ω : ℝ))
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      have hnr : (N : ℝ) ≤ n := by exact_mod_cast hn
      have hnτ : τ ω ≤ (n : ℝ≥0) := by
        apply NNReal.coe_le_coe.mp
        simp only [NNReal.coe_natCast]
        linarith [le_max_right R 0]
      rw [NNReal.coe_sub hnτ, NNReal.coe_natCast]
      linarith [le_max_left R 0]
    exact (tendsto_intervalIntegral_brownianHeatKernel_three hne).comp ht

/-- The three-dimensional exit density converges away from the centre and boundary sphere. -/
theorem IsBrownianSpace.tendsto_exitHeatDensity_three_potential {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (x : EuclideanSpace ℝ (Fin 3))
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 3)) (hB : IsBrownianSpace 3 x B P)
    (hm : ∀ t, StronglyMeasurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω)
    {s : ℝ} (hs : 0 < s) {y : EuclideanSpace ℝ (Fin 3)} (hxy : x ≠ y)
    (hy : ‖y - x‖ ≠ s) :
    Filter.Tendsto (fun n : ℕ => exitHeatDensity P x B s n y) Filter.atTop
      (nhds (3 / (2 * Real.pi * ‖x - y‖) -
        ∫ ω, 3 / (2 * Real.pi * ‖B (exitTime B x s ω).toNNReal ω - y‖) ∂P)) := by
  have hfirst := (tendsto_intervalIntegral_brownianHeatKernel_three hxy).comp
    (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop)
  have hsecond := hB.tendsto_integral_greenTime_exit_three P x B hm hcont hs y hy
  have hrem : ∀ n : ℕ,
      (∫ ω in {ω | exitTime B x s ω < ((n : ℝ≥0) : ℝ≥0∞)},
        (∫ t in (0 : ℝ)..((n : ℝ) - (exitTime B x s ω).toReal),
          brownianHeatKernel 3 t (B (exitTime B x s ω).toNNReal ω) y) ∂P) =
      ∫ ω, (∫ t in (0 : ℝ)..(((n : ℝ≥0) - (exitTime B x s ω).toNNReal : ℝ≥0) : ℝ),
          brownianHeatKernel 3 t (B (exitTime B x s ω).toNNReal ω) y) ∂P := by
    intro n
    let E : Set Ω := {ω | exitTime B x s ω < ((n : ℝ≥0) : ℝ≥0∞)}
    have hE : MeasurableSet E := measurableSet_lt (measurable_exitTime hm hcont x s) measurable_const
    rw [← integral_indicator hE]
    apply integral_congr_ae
    filter_upwards [hB.ae_exitTime_lt_top (by norm_num) hm hcont s] with ω hω
    by_cases h : ω ∈ E
    · rw [Set.indicator_of_mem h]
      have hle : (exitTime B x s ω).toNNReal ≤ (n : ℝ≥0) := by
        apply ENNReal.coe_le_coe.mp
        rw [ENNReal.coe_toNNReal hω.ne]
        exact h.le
      rw [NNReal.coe_sub hle, NNReal.coe_natCast, ENNReal.coe_toNNReal_eq_toReal]
    · rw [Set.indicator_of_notMem h]
      have hle : (n : ℝ≥0) ≤ (exitTime B x s ω).toNNReal := by
        apply ENNReal.coe_le_coe.mp
        rw [ENNReal.coe_toNNReal hω.ne]
        exact not_lt.mp h
      simp only [tsub_eq_zero_of_le hle, NNReal.coe_zero, intervalIntegral.integral_same]
  have h := hfirst.sub hsecond
  convert h using 1
  funext n
  rw [exitHeatDensity_eq P x B hm hcont s n y]
  simp only [NNReal.coe_natCast]
  rw [hrem n]
  rfl

/-- The three-dimensional exit density converges to six times the ball Green kernel. -/
theorem IsBrownianSpace.tendsto_exitHeatDensity_three {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (x : EuclideanSpace ℝ (Fin 3))
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 3)) (hB : IsBrownianSpace 3 x B P)
    (hm : ∀ t, StronglyMeasurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω)
    {s : ℝ} (hs : 0 < s) {y : EuclideanSpace ℝ (Fin 3)} (hxy : x ≠ y)
    (hy : ‖y - x‖ ≠ s) :
    Filter.Tendsto (fun n : ℕ => exitHeatDensity P x B s n y) Filter.atTop
      (nhds (6 * ballGreen 3 s x y)) := by
  have ht := hB.tendsto_exitHeatDensity_three_potential P x B hm hcont hs hxy hy
  have hfactor : ∀ z : EuclideanSpace ℝ (Fin 3), 3 / (2 * Real.pi * ‖z - y‖) =
      (3 / (2 * Real.pi)) * ‖z - y‖⁻¹ := by
    intro z
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  simp_rw [hfactor] at ht
  rw [integral_const_mul] at ht
  by_cases hyin : ‖y - x‖ < s
  · rw [hB.integral_inv_norm_exit_ball P x B hs hyin] at ht
    have hx : ‖x - y‖ < s := by simpa only [norm_sub_rev] using hyin
    have heq : (3 / (2 * Real.pi)) * ‖x - y‖⁻¹ - (3 / (2 * Real.pi)) * s⁻¹ =
        6 * ballGreen 3 s x y := by
      simp only [ballGreen, hx, ↓reduceIte, show (3 : ℕ) ≠ 2 by norm_num, one_div]
      ring
    rw [← heq]
    exact ht
  · have hyout : s < ‖y - x‖ := lt_of_le_of_ne (le_of_not_gt hyin) hy.symm
    rw [hB.integral_inv_norm_exit_ball_of_outside P x B hyout] at ht
    have hx : ¬ ‖x - y‖ < s := by simpa only [norm_sub_rev] using hyin
    simp only [ballGreen, hx, ↓reduceIte, mul_zero]
    simpa only [sub_self] using ht

/-- The two-dimensional heat kernel is bounded by the reciprocal of time. -/
theorem brownianHeatKernel_two_le_inv_time {a y : EuclideanSpace ℝ (Fin 2)}
    {t : ℝ} (ht : 0 < t) : brownianHeatKernel 2 t a y ≤ (Real.pi * t)⁻¹ := by
  unfold brownianHeatKernel
  norm_num only [Nat.cast_ofNat]
  have he : Real.exp (-(2 : ℝ) * ‖a - y‖ ^ 2 / (2 * t)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg ‖a - y‖]) (by positivity)
  have hh : (2 * Real.pi * t / (2 : ℝ)) ^ (-(1 : ℝ)) = (Real.pi * t)⁻¹ := by
    have hb : 2 * Real.pi * t / (2 : ℝ) = Real.pi * t := by ring
    rw [hb, Real.rpow_neg_one]
  rw [hh]
  nlinarith [inv_nonneg.mpr (mul_nonneg Real.pi_pos.le ht.le)]

/-- The two-dimensional heat kernel is uniformly bounded away from its pole. -/
theorem brownianHeatKernel_two_le_of_distance {a y : EuclideanSpace ℝ (Fin 2)}
    {δ t : ℝ} (hδ : 0 < δ) (hxy : δ ≤ ‖a - y‖) (ht : 0 < t) :
    brownianHeatKernel 2 t a y ≤ (Real.pi * δ ^ 2)⁻¹ := by
  have hr : 0 < ‖a - y‖ := hδ.trans_le hxy
  have hne : a ≠ y := sub_ne_zero.mp (norm_pos_iff.mp hr)
  have hb := brownianHeatKernel_le (by norm_num) hne ht
  norm_num only [Nat.cast_ofNat] at hb
  have hh : (2 * Real.pi * ‖a - y‖ ^ 2 / (2 : ℝ)) ^ (-(1 : ℝ)) =
      (Real.pi * ‖a - y‖ ^ 2)⁻¹ := by
    have hb : 2 * Real.pi * ‖a - y‖ ^ 2 / (2 : ℝ) = Real.pi * ‖a - y‖ ^ 2 := by ring
    rw [hb, Real.rpow_neg_one]
  rw [hh] at hb
  have he : Real.exp (-(2 : ℝ) / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hi : (Real.pi * ‖a - y‖ ^ 2)⁻¹ ≤ (Real.pi * δ ^ 2)⁻¹ := by
    apply inv_le_inv₀ (by positivity) (by positivity) |>.2
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ.le hxy 2) Real.pi_pos.le
  have hn : 0 ≤ (Real.pi * ‖a - y‖ ^ 2)⁻¹ := by positivity
  nlinarith

/-- The logarithmic ratio to a point off the boundary is uniformly bounded at the exit position. -/
theorem IsBrownianSpace.ae_abs_log_exit_ratio_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {d : ℕ} (hd : 1 ≤ d) {x y : EuclideanSpace ℝ (Fin d)}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} (hB : IsBrownianSpace d x B P)
    {s : ℝ} (hs : 0 < s) (hxy : x ≠ y) (hy : ‖y - x‖ ≠ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ ω ∂P,
      |Real.log (‖B (exitTime B x s ω).toNNReal ω - y‖ / ‖x - y‖)| ≤ C := by
  let δ : ℝ := |‖y - x‖ - s|
  let R : ℝ := s + ‖x - y‖
  let r : ℝ := ‖x - y‖
  have hδ : 0 < δ := abs_pos.mpr (sub_ne_zero.mpr hy)
  have hr : 0 < r := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hR : 0 < R := by dsimp [R]; positivity
  refine ⟨|Real.log (δ / r)| + |Real.log (R / r)|, add_nonneg (abs_nonneg _) (abs_nonneg _), ?_⟩
  have hsphere := hB.ae_mem_sphere_openExitTime_ball hd hs
  simp_rw [← exitTime_eq_openExitTime_ball] at hsphere
  filter_upwards [hB.ae_exit_distance_lower_bound hd hs y, hsphere] with ω hlo hω
  have hnorm : ‖B (exitTime B x s ω).toNNReal ω - x‖ = s := mem_sphere_iff_norm.1 hω
  have hhi : ‖B (exitTime B x s ω).toNNReal ω - y‖ ≤ R := by
    have h := norm_sub_le_norm_sub_add_norm_sub (B (exitTime B x s ω).toNNReal ω) x y
    rw [hnorm] at h
    exact h
  have hpos : 0 < ‖B (exitTime B x s ω).toNNReal ω - y‖ := hδ.trans_le hlo
  have hlow : Real.log (δ / r) ≤
      Real.log (‖B (exitTime B x s ω).toNNReal ω - y‖ / r) :=
    Real.log_le_log (div_pos hδ hr) (div_le_div_of_nonneg_right hlo hr.le)
  have hupper : Real.log (‖B (exitTime B x s ω).toNNReal ω - y‖ / r) ≤
      Real.log (R / r) :=
    Real.log_le_log (div_pos hpos hr) (div_le_div_of_nonneg_right hhi hr.le)
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le (Real.log (δ / r)), abs_nonneg (Real.log (R / r))]
  · linarith [le_abs_self (Real.log (R / r)), abs_nonneg (Real.log (δ / r))]

/-- Expected differences of two-dimensional heat integrals converge to a logarithmic potential. -/
theorem IsBrownianSpace.tendsto_integral_greenTime_sub_exit_two {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (x : EuclideanSpace ℝ (Fin 2))
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 2)) (hB : IsBrownianSpace 2 x B P)
    (hm : ∀ t, StronglyMeasurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω)
    {s : ℝ} (hs : 0 < s) {y : EuclideanSpace ℝ (Fin 2)} (hxy : x ≠ y)
    (hy : ‖y - x‖ ≠ s) :
    Filter.Tendsto (fun n : ℕ => ∫ ω,
      ((∫ t in (0 : ℝ)..(n : ℝ), brownianHeatKernel 2 t x y) -
       (∫ t in (0 : ℝ)..(n : ℝ), brownianHeatKernel 2 t
          (B (exitTime B x s ω).toNNReal ω) y)) ∂P) Filter.atTop
      (nhds (∫ ω, (2 / Real.pi) * Real.log
        (‖B (exitTime B x s ω).toNNReal ω - y‖ / ‖x - y‖) ∂P)) := by
  let τ : Ω → ℝ≥0 := fun ω => (exitTime B x s ω).toNNReal
  let a : Ω → EuclideanSpace ℝ (Fin 2) := fun ω => B (τ ω) ω
  have hτ : Measurable τ := ENNReal.measurable_toNNReal.comp (measurable_exitTime hm hcont x s)
  have ha : Measurable a := by
    have hj := stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hcont hm
    exact hj.measurable.comp (hτ.prodMk measurable_id)
  obtain ⟨C, hC, hlog⟩ := hB.ae_abs_log_exit_ratio_le (by norm_num) hs hxy hy
  have hmG : ∀ n : ℕ, AEStronglyMeasurable (fun ω =>
      (∫ t in (0 : ℝ)..(n : ℝ), brownianHeatKernel 2 t x y) -
      (∫ t in (0 : ℝ)..(n : ℝ), brownianHeatKernel 2 t (a ω) y)) P := by
    intro n
    have hq : Measurable (fun ω => ∫ t in (0 : ℝ)..(n : ℝ), brownianHeatKernel 2 t (a ω) y) := by
      have h : Measurable (fun ω : Ω => ∫ t in (0 : ℝ)..((n : ℝ≥0) : ℝ),
          brownianHeatKernel 2 t (a ω) y) :=
        (measurable_greenTime 2).comp (measurable_const.prodMk (ha.prodMk measurable_const))
      simpa only [NNReal.coe_natCast] using h
    exact (measurable_const.sub hq).aestronglyMeasurable
  refine tendsto_integral_of_dominated_convergence (fun _ => (2 / Real.pi) * C) hmG
    (integrable_const _) ?_ ?_
  · intro n
    filter_upwards [hlog, hB.ae_exit_distance_lower_bound (by norm_num) hs y] with ω hbound hdist
    have hδ : 0 < |‖y - x‖ - s| := abs_pos.mpr (sub_ne_zero.mpr hy)
    have hne : a ω ≠ y := sub_ne_zero.mp (norm_pos_iff.mp (hδ.trans_le hdist))
    by_cases hn : n = 0
    · subst n
      simp only [Nat.cast_zero, intervalIntegral.integral_same, sub_self, norm_zero]
      positivity
    · have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      rw [Real.norm_eq_abs]
      exact (abs_intervalIntegral_brownianHeatKernel_two_sub_le hxy hne hnR).trans
        (mul_le_mul_of_nonneg_left hbound (by positivity))
  · filter_upwards [hB.ae_exit_distance_lower_bound (by norm_num) hs y] with ω hdist
    have hδ : 0 < |‖y - x‖ - s| := abs_pos.mpr (sub_ne_zero.mpr hy)
    have hne : a ω ≠ y := sub_ne_zero.mp (norm_pos_iff.mp (hδ.trans_le hdist))
    exact (tendsto_greenTime_sub_two hxy hne).comp
      (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop)

/-- A two-dimensional heat integral is bounded by its time length away from the pole. -/
theorem intervalIntegral_brownianHeatKernel_two_le_of_distance
    {a y : EuclideanSpace ℝ (Fin 2)} {δ u v : ℝ} (hδ : 0 < δ)
    (hxy : δ ≤ ‖a - y‖) (hu : 0 ≤ u) (huv : u ≤ v) :
    (∫ t in u..v, brownianHeatKernel 2 t a y) ≤ (v - u) * (Real.pi * δ ^ 2)⁻¹ := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := u) (b := v)
    (f := fun t => brownianHeatKernel 2 t a y) fun t ht => by
      rw [Set.uIoc_of_le huv] at ht
      have ht0 : 0 < t := hu.trans_lt ht.1
      rw [Real.norm_of_nonneg (brownianHeatKernel_nonneg ht0.le a y)]
      exact brownianHeatKernel_two_le_of_distance hδ hxy ht0
  rw [abs_of_nonneg (sub_nonneg.mpr huv), mul_comm] at hb
  exact (Real.le_norm_self _).trans hb

/-- A two-dimensional heat integral starting after zero is bounded by inverse time. -/
theorem intervalIntegral_brownianHeatKernel_two_le_of_time
    {a y : EuclideanSpace ℝ (Fin 2)} {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    (∫ t in u..v, brownianHeatKernel 2 t a y) ≤ (v - u) * (Real.pi * u)⁻¹ := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (C := (Real.pi * u)⁻¹) (a := u) (b := v)
    (f := fun t => brownianHeatKernel 2 t a y) fun t ht => by
      rw [Set.uIoc_of_le huv] at ht
      have ht0 : 0 < t := hu.trans ht.1
      rw [Real.norm_of_nonneg (brownianHeatKernel_nonneg ht0.le a y)]
      refine (brownianHeatKernel_two_le_inv_time ht0).trans ?_
      apply inv_le_inv₀ (by positivity) (by positivity) |>.2
      exact mul_le_mul_of_nonneg_left ht.1.le Real.pi_pos.le
  rw [abs_of_nonneg (sub_nonneg.mpr huv), mul_comm] at hb
  exact (Real.le_norm_self _).trans hb

/-- The late two-dimensional heat contribution vanishes in expectation. -/
theorem IsBrownianSpace.tendsto_integral_greenTime_remainder_two {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (x : EuclideanSpace ℝ (Fin 2)) (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 2))
    (hB : IsBrownianSpace 2 x B P) (hm : ∀ t, StronglyMeasurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) {s : ℝ} (hs : 0 < s)
    {y : EuclideanSpace ℝ (Fin 2)} (hy : ‖y - x‖ ≠ s) :
    Filter.Tendsto (fun n : ℕ => ∫ ω,
      ((∫ t in (0 : ℝ)..(n : ℝ), brownianHeatKernel 2 t
          (B (exitTime B x s ω).toNNReal ω) y) -
       (∫ t in (0 : ℝ)..(((n : ℝ≥0) - (exitTime B x s ω).toNNReal : ℝ≥0) : ℝ),
          brownianHeatKernel 2 t (B (exitTime B x s ω).toNNReal ω) y)) ∂P)
      Filter.atTop (nhds 0) := by
  let τ : Ω → ℝ≥0 := fun ω => (exitTime B x s ω).toNNReal
  let a : Ω → EuclideanSpace ℝ (Fin 2) := fun ω => B (τ ω) ω
  let δ : ℝ := |‖y - x‖ - s|
  have hδ : 0 < δ := abs_pos.mpr (sub_ne_zero.mpr hy)
  have hτ : Measurable τ := ENNReal.measurable_toNNReal.comp (measurable_exitTime hm hcont x s)
  have hτi : Integrable (fun ω => (τ ω : ℝ)) P := hB.integrable_exitTime (by norm_num) hm hcont s
  have ha : Measurable a := by
    have hj := stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hcont hm
    exact hj.measurable.comp (hτ.prodMk measurable_id)
  have hmG : ∀ n : ℕ, AEStronglyMeasurable (fun ω =>
      (∫ t in (0 : ℝ)..(n : ℝ), brownianHeatKernel 2 t (a ω) y) -
      (∫ t in (0 : ℝ)..(((n : ℝ≥0) - τ ω : ℝ≥0) : ℝ), brownianHeatKernel 2 t (a ω) y)) P := by
    intro n
    have hq1 : Measurable (fun ω : Ω => ∫ t in (0 : ℝ)..((n : ℝ≥0) : ℝ),
        brownianHeatKernel 2 t (a ω) y) :=
      (measurable_greenTime 2).comp (measurable_const.prodMk (ha.prodMk measurable_const))
    have hq2 : Measurable (fun ω : Ω => ∫ t in (0 : ℝ)..(((n : ℝ≥0) - τ ω : ℝ≥0) : ℝ),
        brownianHeatKernel 2 t (a ω) y) :=
      (measurable_greenTime 2).comp ((measurable_const.sub hτ).prodMk (ha.prodMk measurable_const))
    have hq : Measurable (fun ω : Ω =>
        (∫ t in (0 : ℝ)..((n : ℝ≥0) : ℝ), brownianHeatKernel 2 t (a ω) y) -
        (∫ t in (0 : ℝ)..(((n : ℝ≥0) - τ ω : ℝ≥0) : ℝ), brownianHeatKernel 2 t (a ω) y)) := hq1.sub hq2
    simpa only [NNReal.coe_natCast] using hq.aestronglyMeasurable
  have hu : ∀ (n : ℕ) (ω : Ω), (((n : ℝ≥0) - τ ω : ℝ≥0) : ℝ) ≤ n := by
    intro n ω
    exact_mod_cast (tsub_le_self : (n : ℝ≥0) - τ ω ≤ n)
  have hlen : ∀ (n : ℕ) (ω : Ω), (n : ℝ) - (((n : ℝ≥0) - τ ω : ℝ≥0) : ℝ) ≤ τ ω := by
    intro n ω
    by_cases h : τ ω ≤ (n : ℝ≥0)
    · rw [NNReal.coe_sub h, NNReal.coe_natCast]
      ring_nf
      exact le_rfl
    · have hn : (n : ℝ≥0) ≤ τ ω := le_of_not_ge h
      rw [tsub_eq_zero_of_le hn, NNReal.coe_zero, sub_zero]
      exact_mod_cast hn
  have hsplit : ∀ (n : ℕ) (ω : Ω), a ω ≠ y →
      (∫ t in (0 : ℝ)..(n : ℝ), brownianHeatKernel 2 t (a ω) y) -
      (∫ t in (0 : ℝ)..(((n : ℝ≥0) - τ ω : ℝ≥0) : ℝ), brownianHeatKernel 2 t (a ω) y) =
      ∫ t in (((n : ℝ≥0) - τ ω : ℝ≥0) : ℝ)..(n : ℝ), brownianHeatKernel 2 t (a ω) y := by
    intro n ω hne
    rw [intervalIntegral.integral_interval_sub_left
      (intervalIntegrable_brownianHeatKernel (by norm_num) hne (by positivity) (by positivity))
      (intervalIntegrable_brownianHeatKernel (by norm_num) hne (by positivity) (by positivity))]
  conv_rhs => rw [← integral_zero (μ := P) (G := ℝ)]
  refine tendsto_integral_of_dominated_convergence (f := fun _ => (0 : ℝ))
    (fun ω => (τ ω : ℝ) * (Real.pi * δ ^ 2)⁻¹)
    hmG (hτi.mul_const _) ?_ ?_
  · intro n
    filter_upwards [hB.ae_exit_distance_lower_bound (by norm_num) hs y] with ω hdist
    have hne : a ω ≠ y := sub_ne_zero.mp (norm_pos_iff.mp (hδ.trans_le hdist))
    rw [hsplit n ω hne, Real.norm_eq_abs,
      abs_of_nonneg (intervalIntegral.integral_nonneg (hu n ω) fun t ht =>
        brownianHeatKernel_nonneg ((NNReal.coe_nonneg _).trans ht.1) _ _)]
    exact (intervalIntegral_brownianHeatKernel_two_le_of_distance hδ hdist
      (NNReal.coe_nonneg _) (hu n ω)).trans
      (mul_le_mul_of_nonneg_right (hlen n ω) (by positivity))
  · filter_upwards [hB.ae_exit_distance_lower_bound (by norm_num) hs y] with ω hdist
    have hne : a ω ≠ y := sub_ne_zero.mp (norm_pos_iff.mp (hδ.trans_le hdist))
    have ht : Filter.Tendsto (fun n : ℕ => (((n : ℝ≥0) - τ ω : ℝ≥0) : ℝ))
        Filter.atTop Filter.atTop := by
      apply Filter.tendsto_atTop.2
      intro R
      obtain ⟨N, hN⟩ := exists_nat_gt (max R 0 + (τ ω : ℝ))
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      have hnr : (N : ℝ) ≤ n := by exact_mod_cast hn
      have hnτ : τ ω ≤ (n : ℝ≥0) := by
        apply NNReal.coe_le_coe.mp
        simp only [NNReal.coe_natCast]
        linarith [le_max_right R 0]
      rw [NNReal.coe_sub hnτ, NNReal.coe_natCast]
      linarith [le_max_left R 0]
    have hbound : Filter.Tendsto (fun n : ℕ => (τ ω : ℝ) *
        (Real.pi * (((n : ℝ≥0) - τ ω : ℝ≥0) : ℝ))⁻¹) Filter.atTop (nhds 0) := by
      simpa using (tendsto_inv_atTop_zero.comp (ht.const_mul_atTop Real.pi_pos)).const_mul (τ ω : ℝ)
    have hlim : Filter.Tendsto (fun n : ℕ =>
        ∫ t in (((n : ℝ≥0) - τ ω : ℝ≥0) : ℝ)..(n : ℝ), brownianHeatKernel 2 t (a ω) y)
        Filter.atTop (nhds 0) := by
      refine squeeze_zero' ?_ ?_ hbound
      · exact Filter.Eventually.of_forall fun n => intervalIntegral.integral_nonneg (hu n ω)
          (fun t ht => brownianHeatKernel_nonneg ((NNReal.coe_nonneg _).trans ht.1) _ _)
      · filter_upwards [ht.eventually (Filter.eventually_gt_atTop 0)] with n hn
        exact (intervalIntegral_brownianHeatKernel_two_le_of_time hn (hu n ω)).trans
          (mul_le_mul_of_nonneg_right (hlen n ω) (by positivity))
    exact hlim.congr' (Filter.Eventually.of_forall fun n => (hsplit n ω hne).symm)

/-- The exit density can be written using the nonnegative remaining time. -/
theorem IsBrownianSpace.exitHeatDensity_eq_integral_greenTime {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {d : ℕ} (hd : 1 ≤ d) (x : EuclideanSpace ℝ (Fin d))
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (hB : IsBrownianSpace d x B P)
    (hm : ∀ t, StronglyMeasurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω)
    (s : ℝ) (N : ℝ≥0) (y : EuclideanSpace ℝ (Fin d)) :
    exitHeatDensity P x B s N y =
      (∫ t in (0 : ℝ)..(N : ℝ), brownianHeatKernel d t x y) -
      ∫ ω, (∫ t in (0 : ℝ)..((N - (exitTime B x s ω).toNNReal : ℝ≥0) : ℝ),
        brownianHeatKernel d t (B (exitTime B x s ω).toNNReal ω) y) ∂P := by
  rw [exitHeatDensity_eq P x B hm hcont s N y]
  congr 1
  let E : Set Ω := {ω | exitTime B x s ω < (N : ℝ≥0∞)}
  have hE : MeasurableSet E := measurableSet_lt (measurable_exitTime hm hcont x s) measurable_const
  rw [← integral_indicator hE]
  apply integral_congr_ae
  filter_upwards [hB.ae_exitTime_lt_top hd hm hcont s] with ω hω
  by_cases h : ω ∈ E
  · rw [Set.indicator_of_mem h]
    have hle : (exitTime B x s ω).toNNReal ≤ N := by
      apply ENNReal.coe_le_coe.mp
      rw [ENNReal.coe_toNNReal hω.ne]
      exact h.le
    rw [NNReal.coe_sub hle, ENNReal.coe_toNNReal_eq_toReal]
  · rw [Set.indicator_of_notMem h]
    have hle : N ≤ (exitTime B x s ω).toNNReal := by
      apply ENNReal.coe_le_coe.mp
      rw [ENNReal.coe_toNNReal hω.ne]
      exact not_lt.mp h
    simp only [tsub_eq_zero_of_le hle, NNReal.coe_zero, intervalIntegral.integral_same]

/-- A finite-horizon heat integral at the exit position is integrable away from the boundary. -/
theorem IsBrownianSpace.integrable_greenTime_exit_two {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (x : EuclideanSpace ℝ (Fin 2))
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 2)) (hB : IsBrownianSpace 2 x B P)
    (hm : ∀ t, StronglyMeasurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω)
    {s : ℝ} (hs : 0 < s) {y : EuclideanSpace ℝ (Fin 2)} (hy : ‖y - x‖ ≠ s)
    {u : Ω → ℝ≥0} (hu : Measurable u) {N : ℝ≥0} (huN : ∀ ω, u ω ≤ N) :
    Integrable (fun ω => ∫ t in (0 : ℝ)..(u ω : ℝ), brownianHeatKernel 2 t
      (B (exitTime B x s ω).toNNReal ω) y) P := by
  let δ : ℝ := |‖y - x‖ - s|
  let τ : Ω → ℝ≥0 := fun ω => (exitTime B x s ω).toNNReal
  let a : Ω → EuclideanSpace ℝ (Fin 2) := fun ω => B (τ ω) ω
  have hδ : 0 < δ := abs_pos.mpr (sub_ne_zero.mpr hy)
  have hτ : Measurable τ := ENNReal.measurable_toNNReal.comp (measurable_exitTime hm hcont x s)
  have ha : Measurable a := by
    have hj := stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hcont hm
    exact hj.measurable.comp (hτ.prodMk measurable_id)
  have hq : Measurable (fun ω => ∫ t in (0 : ℝ)..(u ω : ℝ), brownianHeatKernel 2 t (a ω) y) :=
    (measurable_greenTime 2).comp (hu.prodMk (ha.prodMk measurable_const))
  refine (integrable_const ((N : ℝ) * (Real.pi * δ ^ 2)⁻¹)).mono' hq.aestronglyMeasurable ?_
  filter_upwards [hB.ae_exit_distance_lower_bound (by norm_num) hs y] with ω hdist
  rw [Real.norm_eq_abs, abs_of_nonneg (intervalIntegral.integral_nonneg (NNReal.coe_nonneg _)
    fun t ht => brownianHeatKernel_nonneg ht.1 _ _)]
  calc
    _ ≤ ((u ω : ℝ) - 0) * (Real.pi * δ ^ 2)⁻¹ :=
      intervalIntegral_brownianHeatKernel_two_le_of_distance hδ hdist le_rfl (NNReal.coe_nonneg _)
    _ ≤ (N : ℝ) * (Real.pi * δ ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_right (by simpa only [sub_zero] using (NNReal.coe_le_coe.mpr (huN ω))) (by positivity)

/-- In dimension two, the exit density converges to the expected logarithmic potential. -/
theorem IsBrownianSpace.tendsto_exitHeatDensity_two_potential {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (x : EuclideanSpace ℝ (Fin 2))
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 2)) (hB : IsBrownianSpace 2 x B P)
    (hm : ∀ t, StronglyMeasurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω)
    {s : ℝ} (hs : 0 < s) {y : EuclideanSpace ℝ (Fin 2)} (hxy : x ≠ y)
    (hy : ‖y - x‖ ≠ s) :
    Filter.Tendsto (fun n : ℕ => exitHeatDensity P x B s n y) Filter.atTop
      (nhds (∫ ω, (2 / Real.pi) * Real.log
        (‖B (exitTime B x s ω).toNNReal ω - y‖ / ‖x - y‖) ∂P)) := by
  have h1 := hB.tendsto_integral_greenTime_sub_exit_two P x B hm hcont hs hxy hy
  have h2 := hB.tendsto_integral_greenTime_remainder_two P x B hm hcont hs hy
  have ht := h1.add h2
  simp only [add_zero] at ht
  convert ht using 1
  funext n
  let τ : Ω → ℝ≥0 := fun ω => (exitTime B x s ω).toNNReal
  let a : Ω → EuclideanSpace ℝ (Fin 2) := fun ω => B (τ ω) ω
  have hτ : Measurable τ := ENNReal.measurable_toNNReal.comp (measurable_exitTime hm hcont x s)
  have hq1 : Integrable (fun ω => ∫ t in (0 : ℝ)..(n : ℝ), brownianHeatKernel 2 t (a ω) y) P := by
    have h := hB.integrable_greenTime_exit_two P x B hm hcont hs hy
      (u := fun _ => (n : ℝ≥0)) (N := n) measurable_const (fun _ => le_rfl)
    simpa only [NNReal.coe_natCast] using h
  have hq2 : Integrable (fun ω => ∫ t in (0 : ℝ)..(((n : ℝ≥0) - τ ω : ℝ≥0) : ℝ),
      brownianHeatKernel 2 t (a ω) y) P :=
    hB.integrable_greenTime_exit_two P x B hm hcont hs hy
      (u := fun ω => (n : ℝ≥0) - τ ω) (N := n) (measurable_const.sub hτ) (fun _ => tsub_le_self)
  rw [hB.exitHeatDensity_eq_integral_greenTime P (by norm_num) x B hm hcont s n y]
  simp only [NNReal.coe_natCast]
  rw [integral_sub (integrable_const _) hq1, integral_sub hq1 hq2]
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul]
  ring

/-- The logarithm of the distance from the exit point is integrable off the boundary sphere. -/
theorem IsBrownianSpace.integrable_log_norm_exit_of_off_sphere {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (x : EuclideanSpace ℝ (Fin 2))
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 2)) (hB : IsBrownianSpace 2 x B P)
    (hm : ∀ t, StronglyMeasurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω)
    {s : ℝ} (hs : 0 < s) {y : EuclideanSpace ℝ (Fin 2)} (hxy : x ≠ y)
    (hy : ‖y - x‖ ≠ s) :
    Integrable (fun ω => Real.log ‖B (exitTime B x s ω).toNNReal ω - y‖) P := by
  let τ : Ω → ℝ≥0 := fun ω => (exitTime B x s ω).toNNReal
  let a : Ω → EuclideanSpace ℝ (Fin 2) := fun ω => B (τ ω) ω
  have hτ : Measurable τ := ENNReal.measurable_toNNReal.comp (measurable_exitTime hm hcont x s)
  have ha : Measurable a := by
    have hj := stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hcont hm
    exact hj.measurable.comp (hτ.prodMk measurable_id)
  obtain ⟨C, hC, hbound⟩ := hB.ae_abs_log_exit_ratio_le (by norm_num) hs hxy hy
  have hratio : Integrable (fun ω => Real.log (‖a ω - y‖ / ‖x - y‖)) P := by
    refine (integrable_const C).mono' (((ha.sub measurable_const).norm.div measurable_const).log
      |>.aestronglyMeasurable) ?_
    filter_upwards [hbound] with ω hω
    simpa only [Real.norm_eq_abs] using hω
  have hr : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)
  refine (hratio.add (integrable_const (Real.log ‖x - y‖))).congr ?_
  filter_upwards [hB.ae_exit_distance_lower_bound (by norm_num) hs y] with ω hdist
  have hδ : 0 < |‖y - x‖ - s| := abs_pos.mpr (sub_ne_zero.mpr hy)
  have ha0 : ‖a ω - y‖ ≠ 0 := (hδ.trans_le hdist).ne'
  dsimp only [Pi.add_apply]
  rw [Real.log_div ha0 hr]
  ring

/-- The two-dimensional exit density converges to four times the ball Green kernel. -/
theorem IsBrownianSpace.tendsto_exitHeatDensity_two {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (x : EuclideanSpace ℝ (Fin 2))
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 2)) (hB : IsBrownianSpace 2 x B P)
    (hm : ∀ t, StronglyMeasurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω)
    {s : ℝ} (hs : 0 < s) {y : EuclideanSpace ℝ (Fin 2)} (hxy : x ≠ y)
    (hy : ‖y - x‖ ≠ s) :
    Filter.Tendsto (fun n : ℕ => exitHeatDensity P x B s n y) Filter.atTop
      (nhds (4 * ballGreen 2 s x y)) := by
  have ht := hB.tendsto_exitHeatDensity_two_potential P x B hm hcont hs hxy hy
  have hlogint := hB.integrable_log_norm_exit_of_off_sphere P x B hm hcont hs hxy hy
  have hr : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)
  have hratio : (∫ ω, Real.log (‖B (exitTime B x s ω).toNNReal ω - y‖ / ‖x - y‖) ∂P) =
      (∫ ω, Real.log ‖B (exitTime B x s ω).toNNReal ω - y‖ ∂P) - Real.log ‖x - y‖ := by
    have heq : (fun ω => Real.log (‖B (exitTime B x s ω).toNNReal ω - y‖ / ‖x - y‖)) =ᵐ[P]
        fun ω => Real.log ‖B (exitTime B x s ω).toNNReal ω - y‖ - Real.log ‖x - y‖ := by
      filter_upwards [hB.ae_exit_distance_lower_bound (by norm_num) hs y] with ω hdist
      have hδ : 0 < |‖y - x‖ - s| := abs_pos.mpr (sub_ne_zero.mpr hy)
      exact Real.log_div (hδ.trans_le hdist).ne' hr
    rw [integral_congr_ae heq, integral_sub hlogint (integrable_const _)]
    simp
  rw [integral_const_mul, hratio] at ht
  by_cases hyin : ‖y - x‖ < s
  · rw [hB.integral_log_norm_exit_ball P x B hs hyin] at ht
    have hx : ‖x - y‖ < s := by simpa only [norm_sub_rev] using hyin
    have heq : (2 / Real.pi) * (Real.log s - Real.log ‖x - y‖) =
        4 * ballGreen 2 s x y := by
      simp only [ballGreen, hx, ↓reduceIte]
      rw [Real.log_div hs.ne' hr]
      ring
    rw [← heq]
    exact ht
  · have hyout : s < ‖y - x‖ := lt_of_le_of_ne (le_of_not_gt hyin) hy.symm
    rw [hB.integral_log_norm_exit_ball_of_outside P x B hyout] at ht
    have hx : ¬ ‖x - y‖ < s := by simpa only [norm_sub_rev] using hyin
    simp only [ballGreen, hx, ↓reduceIte, mul_zero]
    simpa only [sub_self, mul_zero] using ht

/-- The exit occupation density converges almost everywhere to the ball Green kernel. -/
theorem IsBrownianSpace.ae_tendsto_exitHeatDensity {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (hd : d = 2 ∨ d = 3)
    (x : EuclideanSpace ℝ (Fin d)) (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (hB : IsBrownianSpace d x B P) (hm : ∀ t, StronglyMeasurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) {s : ℝ} (hs : 0 < s) :
    ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      Filter.Tendsto (fun n : ℕ => exitHeatDensity P x B s n y) Filter.atTop
        (nhds (2 * (d : ℝ) * ballGreen d s x y)) := by
  rcases hd with rfl | rfl
  · have hsp : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))),
        y ∉ Metric.sphere x s := ae_iff.mpr (by
          have heq : {y | ¬ y ∉ Metric.sphere x s} = Metric.sphere x s := by ext y; simp
          rw [heq]
          exact Measure.addHaar_sphere volume x s)
    filter_upwards [Measure.ae_ne volume x, hsp] with y hy hys
    have hxy : x ≠ y := hy.symm
    have hne : ‖y - x‖ ≠ s := fun h => hys (mem_sphere_iff_norm.mpr h)
    norm_num only [Nat.cast_ofNat, show (2 : ℝ) * 2 = 4 by norm_num]
    exact hB.tendsto_exitHeatDensity_two P x B hm hcont hs hxy hne
  · have hsp : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))),
        y ∉ Metric.sphere x s := ae_iff.mpr (by
          have heq : {y | ¬ y ∉ Metric.sphere x s} = Metric.sphere x s := by ext y; simp
          rw [heq]
          exact Measure.addHaar_sphere volume x s)
    filter_upwards [Measure.ae_ne volume x, hsp] with y hy hys
    have hxy : x ≠ y := hy.symm
    have hne : ‖y - x‖ ≠ s := fun h => hys (mem_sphere_iff_norm.mpr h)
    norm_num only [Nat.cast_ofNat, show (2 : ℝ) * 3 = 6 by norm_num]
    exact hB.tendsto_exitHeatDensity_three P x B hm hcont hs hxy hne

/-- The total mass of a finite-horizon exit density is bounded by the mean exit time. -/
theorem IsBrownianSpace.integral_exitHeatDensity_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (hd : 1 ≤ d)
    (x : EuclideanSpace ℝ (Fin d)) (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (hB : IsBrownianSpace d x B P) (hm : ∀ t, StronglyMeasurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) (s : ℝ) (N : ℝ≥0) :
    (∫ y, exitHeatDensity P x B s N y) ≤ ∫ ω, (exitTime B x s ω).toReal ∂P := by
  let τ : Ω → ℝ≥0 := exitTimeTrunc B x s N
  have hτm : Measurable τ := measurable_exitTimeTrunc hm hcont x s N
  have hτN : ∀ ω, τ ω ≤ N := by
    intro ω
    apply ENNReal.coe_le_coe.mp
    rw [coe_exitTimeTrunc]
    exact inf_le_right
  have hτi : Integrable (fun ω => (τ ω : ℝ)) P := by
    refine (integrable_const (N : ℝ)).mono' (measurable_coe_nnreal_real.comp hτm).aestronglyMeasurable ?_
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]
    exact_mod_cast hτN ω
  have hφ : Measurable (fun _ : EuclideanSpace ℝ (Fin d) => (1 : ℝ)) := measurable_const
  have hb : ∃ M, ∀ y : EuclideanSpace ℝ (Fin d), |(1 : ℝ)| ≤ M := ⟨1, fun _ => by norm_num⟩
  have heq := (hB.integral_occupation_stoppedHeatDensity P hd x B hm hcont τ
    (isStoppingTime_exitTimeTrunc hm hcont x s N) N hφ hb).2
  simp only [one_mul, intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_one] at heq
  have heq' : (∫ ω, (τ ω : ℝ) ∂P) = ∫ y, exitHeatDensity P x B s N y := by
    convert heq using 2
    funext ω
    · rw [min_eq_left (hτN ω)]
    · rfl
  rw [← heq']
  refine integral_mono_ae hτi (hB.integrable_exitTime hd hm hcont s) ?_
  filter_upwards [hB.ae_exitTime_lt_top hd hm hcont s] with ω hfin
  have he : ((τ ω : ℝ≥0) : ℝ≥0∞) ≤ exitTime B x s ω := by
    rw [coe_exitTimeTrunc]
    exact inf_le_left
  have he' : τ ω ≤ (exitTime B x s ω).toNNReal := by
    apply ENNReal.coe_le_coe.mp
    rw [ENNReal.coe_toNNReal hfin.ne]
    exact he
  exact_mod_cast he'

/-- The ball Green kernel is integrable in dimensions two and three. -/
theorem IsBrownianSpace.integrable_ballGreen {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (hd : d = 2 ∨ d = 3)
    (x : EuclideanSpace ℝ (Fin d)) (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (hB : IsBrownianSpace d x B P) (hm : ∀ t, StronglyMeasurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) {s : ℝ} (hs : 0 < s) :
    Integrable (ballGreen d s x) := by
  have hd1 : 1 ≤ d := by rcases hd with rfl | rfl <;> norm_num
  let f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ := fun n => exitHeatDensity P x B s n
  let F : EuclideanSpace ℝ (Fin d) → ℝ := fun y => 2 * (d : ℝ) * ballGreen d s x y
  have hfi : ∀ n, Integrable (f n) := fun n =>
    hB.integrable_stoppedHeatDensity hd1 hm hcont
      (measurable_exitTimeTrunc hm hcont x s n) n
  have hF : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      Filter.Tendsto (fun n => f n y) Filter.atTop (nhds (F y)) :=
    hB.ae_tendsto_exitHeatDensity P hd x B hm hcont hs
  have hnonneg : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), ∀ n, 0 ≤ f n y := by
    rw [ae_all_iff]
    exact fun n => hB.ae_nonneg_exitHeatDensity P hd1 x B hm hcont s n
  have hmono : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), Monotone fun n => f n y := by
    have hstep : ∀ n : ℕ, ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
        f n y ≤ f (n + 1) y := fun n =>
      hB.ae_exitHeatDensity_le P hd1 x B hm hcont s (by exact_mod_cast Nat.le_succ n)
    filter_upwards [(ae_all_iff.mpr hstep)] with y hy
    exact monotone_nat_of_le_succ hy
  have hF0 : 0 ≤ᵐ[volume] F := by
    filter_upwards [hF, hnonneg] with y hy hn
    exact ge_of_tendsto' hy hn
  have hlim : Filter.Tendsto (fun n : ℕ => ∫⁻ y, ENNReal.ofReal (f n y)) Filter.atTop
      (nhds (∫⁻ y, ENNReal.ofReal (F y))) := by
    apply lintegral_tendsto_of_tendsto_of_monotone
    · exact fun n => (hfi n).aemeasurable.ennreal_ofReal
    · filter_upwards [hmono] with y hy n m hnm
      exact ENNReal.ofReal_le_ofReal (hy hnm)
    · filter_upwards [hF] with y hy
      exact (ENNReal.continuous_ofReal.tendsto _).comp hy
  have hbound : (∫⁻ y, ENNReal.ofReal (F y)) ≤
      ENNReal.ofReal (∫ ω, (exitTime B x s ω).toReal ∂P) := by
    apply le_of_tendsto hlim
    filter_upwards [] with n
    rw [← ofReal_integral_eq_lintegral_ofReal (hfi n)
      ((ae_all_iff.mp hnonneg) n)]
    exact ENNReal.ofReal_le_ofReal (hB.integral_exitHeatDensity_le P hd1 x B hm hcont s n)
  have hFi : Integrable F := by
    refine ⟨((measurable_ballGreen d s x).const_mul _).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hF0]
    exact hbound.trans_lt ENNReal.ofReal_lt_top
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
  have hc : (2 * (d : ℝ)) ≠ 0 := by positivity
  have h := hFi.const_mul (2 * (d : ℝ))⁻¹
  simpa only [F, ← mul_assoc, inv_mul_cancel₀ hc, one_mul] using h

/-- The expected occupation measure of a ball has the ball Green density. -/
theorem IsBrownianSpace.ballOccupation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (hd : d = 2 ∨ d = 3)
    (x : EuclideanSpace ℝ (Fin d)) (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (hB : IsBrownianSpace d x B P) (hm : ∀ t, StronglyMeasurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) (s : ℝ) (hs : 0 < s)
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (hφ : Measurable φ)
    (hb : ∃ M, ∀ y, |φ y| ≤ M) :
    Integrable (fun ω => ∫ r in (0 : ℝ)..(exitTime B x s ω).toReal, φ (B r.toNNReal ω)) P ∧
    (∫ ω, (∫ r in (0 : ℝ)..(exitTime B x s ω).toReal, φ (B r.toNNReal ω)) ∂P) =
      2 * (d : ℝ) * ∫ y, φ y * ballGreen d s x y := by
  have hd1 : 1 ≤ d := by rcases hd with rfl | rfl <;> norm_num
  refine ⟨hB.integrable_occupation_exitTime hd1 hm hcont s hφ hb, ?_⟩
  obtain ⟨M, hM⟩ := hb
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  let f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ := fun n => exitHeatDensity P x B s n
  let F : EuclideanSpace ℝ (Fin d) → ℝ := fun y => 2 * (d : ℝ) * ballGreen d s x y
  have hfi : ∀ n, Integrable (f n) := fun n =>
    hB.integrable_stoppedHeatDensity hd1 hm hcont (measurable_exitTimeTrunc hm hcont x s n) n
  have hF : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      Filter.Tendsto (fun n => f n y) Filter.atTop (nhds (F y)) :=
    hB.ae_tendsto_exitHeatDensity P hd x B hm hcont hs
  have hnonneg : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), ∀ n, 0 ≤ f n y := by
    rw [ae_all_iff]
    exact fun n => hB.ae_nonneg_exitHeatDensity P hd1 x B hm hcont s n
  have hmono : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), Monotone fun n => f n y := by
    have hstep : ∀ n : ℕ, ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
        f n y ≤ f (n + 1) y := fun n =>
      hB.ae_exitHeatDensity_le P hd1 x B hm hcont s (by exact_mod_cast Nat.le_succ n)
    filter_upwards [(ae_all_iff.mpr hstep)] with y hy
    exact monotone_nat_of_le_succ hy
  have hFint : Integrable F := (hB.integrable_ballGreen P hd x B hm hcont hs).const_mul _
  have hmeas' : ∀ n, AEStronglyMeasurable (fun y => φ y * f n y) := fun n =>
    ((hfi n).bdd_mul hφ.aestronglyMeasurable (Filter.Eventually.of_forall fun y => by
      simpa only [Real.norm_eq_abs] using hM y)).aestronglyMeasurable
  have hspace : Filter.Tendsto (fun n : ℕ => ∫ y, φ y * f n y) Filter.atTop
      (nhds (∫ y, φ y * F y)) := by
    apply tendsto_integral_of_dominated_convergence (fun y => M * F y) hmeas' (hFint.const_mul M)
    · intro n
      filter_upwards [hF, hnonneg, hmono] with y hy hn hmon
      have hle : f n y ≤ F y := by
        apply ge_of_tendsto hy
        filter_upwards [Filter.eventually_ge_atTop n] with k hk
        exact hmon hk
      have hnn : 0 ≤ f n y := hn n
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
      exact (mul_le_mul_of_nonneg_right (hM y) hnn).trans
        (mul_le_mul_of_nonneg_left hle hM0)
    · filter_upwards [hF] with y hy
      exact tendsto_const_nhds.mul hy
  have htime := hB.tendsto_integral_occupation_exitTimeTrunc hd1 hm hcont s hφ ⟨M, hM⟩
  have heq : ∀ n : ℕ, (∫ ω, (∫ r in (0 : ℝ)..(exitTimeTrunc B x s n ω : ℝ),
      φ (B r.toNNReal ω)) ∂P) = ∫ y, φ y * f n y := by
    intro n
    have hτ : IsStoppingTime (natFiltration B hm)
        (fun ω => ((exitTimeTrunc B x s n ω : ℝ≥0) : ℝ≥0∞)) :=
      isStoppingTime_exitTimeTrunc hm hcont x s n
    have hτn : ∀ ω, exitTimeTrunc B x s n ω ≤ n := by
      intro ω
      apply ENNReal.coe_le_coe.mp
      rw [coe_exitTimeTrunc]
      exact inf_le_right
    have h := (hB.integral_occupation_stoppedHeatDensity P hd1 x B hm hcont
      (exitTimeTrunc B x s n) hτ n hφ ⟨M, hM⟩).2
    convert h using 2
    funext ω
    · rw [min_eq_left (hτn ω)]
    · rfl
  have heqlim : (∫ ω, (∫ r in (0 : ℝ)..(exitTime B x s ω).toReal,
      φ (B r.toNNReal ω)) ∂P) = ∫ y, φ y * F y := by
    apply tendsto_nhds_unique htime
    apply hspace.congr'
    exact Filter.Eventually.of_forall fun n => (heq n).symm
  rw [heqlim]
  simp_rw [F, show ∀ y, φ y * (2 * (d : ℝ) * ballGreen d s x y) =
    (2 * (d : ℝ)) * (φ y * ballGreen d s x y) from fun y => by ring]
  rw [integral_const_mul]

end LatticeProb
