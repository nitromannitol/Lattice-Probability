import LatticeProb.Prob.Cadlag.HalfLine.Convergence
import LatticeProb.Prob.Cadlag.HalfLine.Separable
import LatticeProb.Prob.Cadlag.HalfLine.Laws
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Averaged increments across a fixed time

The bounded double time integral detects increments across a deterministic time.
Its normalization is the area of the averaging rectangle.
-/

namespace LatticeProb.Cadlag.HalfLine

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology BoundedContinuousFunction ENNReal

noncomputable section

variable {E : Type*} [MetricSpace E]

/-- The real bounded state distance used in time averages. -/
def boundedDistance (a b : E) : ℝ := min (dist a b) 1

/-- The real bounded distance is the finite extended distance `q`. -/
theorem boundedDistance_eq_toReal_q (a b : E) :
    boundedDistance a b = (q a b).toReal := by
  simp only [boundedDistance, q, edist_dist,
    ENNReal.toReal_min ENNReal.ofReal_ne_top ENNReal.one_ne_top,
    ENNReal.toReal_ofReal dist_nonneg, ENNReal.toReal_one]

/-- Bounded state distance is continuous in both state variables. -/
theorem continuous_boundedDistance :
    Continuous (fun p : E × E => boundedDistance p.1 p.2) :=
  continuous_dist.min continuous_const

/-- Bounded state distance is nonnegative. -/
theorem boundedDistance_nonneg (a b : E) : 0 ≤ boundedDistance a b :=
  le_min dist_nonneg zero_le_one

/-- Bounded state distance has norm at most one. -/
theorem norm_boundedDistance_le_one (a b : E) : ‖boundedDistance a b‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (boundedDistance_nonneg a b)]
  exact min_le_right _ _

/-- The area-normalized increment integral across `T`, using the actual half-line path. -/
def averagedIncrement (T : Time) (h : ℝ) (x : D E) : ℝ :=
  (h ^ 2)⁻¹ * ∫ s in (T : ℝ) - h..(T : ℝ),
    ∫ t in (T : ℝ)..(T : ℝ) + h,
      boundedDistance (x.1 s.toNNReal) (x.1 t.toNNReal)

/-- The increment functional vanishes at every constant path. -/
theorem averagedIncrement_const (T : Time) (h : ℝ) (a : E) :
    averagedIncrement T h (const a) = 0 := by
  simp only [averagedIncrement, boundedDistance, const, dist_self, min_eq_left zero_le_one,
    intervalIntegral.integral_zero, mul_zero]

/-- An inner increment integral has norm bounded by the length of its interval. -/
theorem norm_integral_boundedDistance_le (x : D E) (s a b : ℝ) :
    ‖∫ t in a..b, boundedDistance (x.1 s.toNNReal) (x.1 t.toNNReal)‖ ≤ |b - a| := by
  simpa only [one_mul] using intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (fun t _ => norm_boundedDistance_le_one _ _)

/-- Positive-width averaged increments are nonnegative. -/
theorem averagedIncrement_nonneg (T : Time) {h : ℝ} (hh : 0 < h) (x : D E) :
    0 ≤ averagedIncrement T h x := by
  apply mul_nonneg (inv_nonneg.mpr (sq_nonneg h))
  apply intervalIntegral.integral_nonneg_of_forall (by linarith)
  intro s
  exact intervalIntegral.integral_nonneg_of_forall (by linarith)
    (fun t => boundedDistance_nonneg _ _)

/-- The double integral's area normalization bounds the increment functional by one. -/
theorem averagedIncrement_le_one (T : Time) {h : ℝ} (hh : 0 < h) (x : D E) :
    averagedIncrement T h x ≤ 1 := by
  have hb : ‖∫ s in (T : ℝ) - h..(T : ℝ),
      ∫ t in (T : ℝ)..(T : ℝ) + h,
        boundedDistance (x.1 s.toNNReal) (x.1 t.toNNReal)‖ ≤ h ^ 2 := by
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (T : ℝ) - h) (b := (T : ℝ))
      (fun s _ => norm_integral_boundedDistance_le x s (T : ℝ) ((T : ℝ) + h))
    simpa only [add_sub_cancel_left, sub_sub_cancel, abs_of_pos hh, sq] using hi
  unfold averagedIncrement
  calc
    _ ≤ (h ^ 2)⁻¹ * (h ^ 2) :=
      mul_le_mul_of_nonneg_left ((Real.le_norm_self _).trans hb) (by positivity)
    _ = 1 := inv_mul_cancel₀ (ne_of_gt (sq_pos_of_pos hh))

variable [MeasurableSpace E] [BorelSpace E] [SeparableSpace E]

/-- The time-pair increment of a fixed path is jointly measurable. -/
theorem measurable_timePair_boundedDistance (x : D E) :
    Measurable (fun p : ℝ × ℝ =>
      boundedDistance (x.1 p.1.toNNReal) (x.1 p.2.toNNReal)) := by
  have hm := (measurable_isCadlag x.2).comp continuous_real_toNNReal.measurable
  exact continuous_boundedDistance.measurable.comp
    ((hm.comp measurable_fst).prodMk (hm.comp measurable_snd))

/-- Integrating the second time variable leaves a measurable function of the first. -/
theorem measurable_integral_boundedDistance (x : D E) (a b : ℝ) :
    Measurable (fun s : ℝ =>
      ∫ t in a..b, boundedDistance (x.1 s.toNNReal) (x.1 t.toNNReal)) := by
  simp only [intervalIntegral]
  exact ((measurable_timePair_boundedDistance x).stronglyMeasurable.integral_prod_right'
    |>.sub (measurable_timePair_boundedDistance x).stronglyMeasurable.integral_prod_right'
    |>.measurable)

/-- Every time slice of the bounded increment kernel is interval integrable. -/
theorem intervalIntegrable_boundedDistance (x : D E) (s a b : ℝ) :
    IntervalIntegrable (fun t : ℝ =>
      boundedDistance (x.1 s.toNNReal) (x.1 t.toNNReal)) volume a b := by
  apply intervalIntegrable_iff.mpr
  have hm := (measurable_isCadlag x.2).comp continuous_real_toNNReal.measurable
  exact (intervalIntegrable_const (c := (1 : ℝ))).def'.mono'
    (continuous_boundedDistance.measurable.comp
      (measurable_const.prodMk hm)).aestronglyMeasurable.restrict
    (Eventually.of_forall fun t => norm_boundedDistance_le_one _ _)

/-- The inner integral is interval integrable in the remaining time variable. -/
theorem intervalIntegrable_integral_boundedDistance (x : D E) (a b c d : ℝ) :
    IntervalIntegrable (fun s : ℝ =>
      ∫ t in c..d, boundedDistance (x.1 s.toNNReal) (x.1 t.toNNReal)) volume a b := by
  apply intervalIntegrable_iff.mpr
  exact (intervalIntegrable_const (c := |d - c|)).def'.mono'
    (measurable_integral_boundedDistance x c d).aestronglyMeasurable.restrict
    (Eventually.of_forall fun s => norm_integral_boundedDistance_le x s c d)

/-- A lower bound throughout the open averaging rectangle survives area normalization. -/
theorem le_averagedIncrement_of_rectangle (T : Time) {h c : ℝ} (hh : 0 < h)
    (x : D E) (hb : ∀ s ∈ Ioo ((T : ℝ) - h) (T : ℝ),
      ∀ t ∈ Ioo (T : ℝ) ((T : ℝ) + h),
        c ≤ boundedDistance (x.1 s.toNNReal) (x.1 t.toNNReal)) :
    c ≤ averagedIncrement T h x := by
  have hi (s : ℝ) (hs : s ∈ Ioo ((T : ℝ) - h) (T : ℝ)) :
      h * c ≤ ∫ t in (T : ℝ)..(T : ℝ) + h,
        boundedDistance (x.1 s.toNNReal) (x.1 t.toNNReal) := by
    have hm := intervalIntegral.integral_mono_on_of_le_Ioo
      (by linarith : (T : ℝ) ≤ (T : ℝ) + h)
      (intervalIntegrable_const (c := c))
      (intervalIntegrable_boundedDistance x s _ _) (hb s hs)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left] using hm
  have ho := intervalIntegral.integral_mono_on_of_le_Ioo
    (by linarith : (T : ℝ) - h ≤ (T : ℝ))
    (intervalIntegrable_const (c := h * c))
    (intervalIntegrable_integral_boundedDistance x _ _ _ _) hi
  have ho' : h ^ 2 * c ≤ ∫ s in (T : ℝ) - h..(T : ℝ),
      ∫ t in (T : ℝ)..(T : ℝ) + h,
        boundedDistance (x.1 s.toNNReal) (x.1 t.toNNReal) := by
    simpa only [intervalIntegral.integral_const, smul_eq_mul, sub_sub_cancel,
      ← mul_assoc, ← sq] using ho
  unfold averagedIncrement
  exact (le_inv_mul_iff₀ (sq_pos_of_pos hh)).mpr ho'

omit [MeasurableSpace E] [BorelSpace E] [SeparableSpace E] in
/-- The discontinuity times of a fixed path have zero real Lebesgue measure. -/
theorem ae_continuousAt_time (x : D E) :
    ∀ᵐ s : ℝ, 0 ≤ s → ContinuousAt x.1 s.toNNReal := by
  have hae := (x.2.countable_discontinuities.image (fun s : Time => (s : ℝ))).ae_notMem
    volume
  filter_upwards [hae] with s hs hpos
  by_contra hnot
  exact hs ⟨s.toNNReal, hnot, Real.coe_toNNReal s hpos⟩

/-- At a continuity time, inner increment averages converge along converging paths. -/
theorem tendsto_integral_boundedDistance {x : ℕ → D E} {y : D E}
    (hxy : Tendsto x atTop (𝓝 y)) {s : ℝ}
    (hs : ContinuousAt y.1 s.toNNReal) (T : Time) {h : ℝ} (hh : 0 < h) :
    Tendsto (fun n => ∫ t in (T : ℝ)..(T : ℝ) + h,
      boundedDistance ((x n).1 s.toNNReal) ((x n).1 t.toNNReal)) atTop
      (𝓝 (∫ t in (T : ℝ)..(T : ℝ) + h,
        boundedDistance (y.1 s.toNNReal) (y.1 t.toNNReal))) := by
  have hd := tendsto_iff_dist_tendsto_zero.mp hxy
  have hs' := tendsto_eval_of_tendsto_skorohodDistance hd hs
  have hi : Tendsto (fun n => ∫ t in Ioc (T : ℝ) ((T : ℝ) + h),
      boundedDistance ((x n).1 s.toNNReal) ((x n).1 t.toNNReal)) atTop
      (𝓝 (∫ t in Ioc (T : ℝ) ((T : ℝ) + h),
        boundedDistance (y.1 s.toNNReal) (y.1 t.toNNReal))) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => 1)
    · intro n
      have hm := (measurable_isCadlag (x n).2).comp
        continuous_real_toNNReal.measurable
      exact (continuous_boundedDistance.measurable.comp
        (measurable_const.prodMk hm)).aestronglyMeasurable.restrict
    · exact integrable_const 1
    · intro n
      exact Eventually.of_forall fun t => norm_boundedDistance_le_one _ _
    · filter_upwards [(ae_continuousAt_time y).filter_mono
        (ae_mono Measure.restrict_le_self), ae_restrict_mem measurableSet_Ioc] with t ht hTt
      have ht' := tendsto_eval_of_tendsto_skorohodDistance hd
        (ht (T.2.trans hTt.1.le))
      exact continuous_boundedDistance.continuousAt.tendsto.comp (hs'.prodMk_nhds ht')
  simpa only [intervalIntegral.integral_of_le (le_add_of_nonneg_right hh.le)] using hi

/-- The averaged increment across a positive time is continuous for widths below that time. -/
theorem continuous_averagedIncrement (T : Time) {h : ℝ} (hh : 0 < h)
    (hhT : h < (T : ℝ)) : Continuous (averagedIncrement (E := E) T h) := by
  apply continuous_iff_seqContinuous.mpr
  intro x y hxy
  have hi : Tendsto (fun n => ∫ s in Ioc ((T : ℝ) - h) (T : ℝ),
      ∫ t in (T : ℝ)..(T : ℝ) + h,
        boundedDistance ((x n).1 s.toNNReal) ((x n).1 t.toNNReal)) atTop
      (𝓝 (∫ s in Ioc ((T : ℝ) - h) (T : ℝ),
        ∫ t in (T : ℝ)..(T : ℝ) + h,
          boundedDistance (y.1 s.toNNReal) (y.1 t.toNNReal))) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => h)
    · intro n
      exact (measurable_integral_boundedDistance (x n) _ _).aestronglyMeasurable.restrict
    · exact integrable_const h
    · intro n
      exact Eventually.of_forall fun s => by
        simpa only [add_sub_cancel_left, abs_of_pos hh] using
          norm_integral_boundedDistance_le (x n) s (T : ℝ) ((T : ℝ) + h)
    · filter_upwards [(ae_continuousAt_time y).filter_mono
        (ae_mono Measure.restrict_le_self), ae_restrict_mem measurableSet_Ioc] with s hs hTs
      exact tendsto_integral_boundedDistance hxy (hs (by linarith [hTs.1])) T hh
  have hle : (T : ℝ) - h ≤ (T : ℝ) := sub_le_self _ hh.le
  simpa only [Function.comp_def, averagedIncrement, intervalIntegral.integral_of_le hle] using
    hi.const_mul ((h ^ 2)⁻¹)

/-- Continuity makes the positive-width averaged increment Borel measurable. -/
theorem measurable_averagedIncrement (T : Time) {h : ℝ} (hh : 0 < h)
    (hhT : h < (T : ℝ)) : Measurable (averagedIncrement (E := E) T h) :=
  (continuous_averagedIncrement T hh hhT).measurable

/-- A genuine jump forces all sufficiently narrow averaged increments to stay positive. -/
theorem exists_pos_eventually_le_averagedIncrement (T : Time) (hT : 0 < T)
    (x : D E) (hx : ¬ ContinuousAt x.1 T) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ h in 𝓝[>] (0 : ℝ), c ≤ averagedIncrement T h x := by
  obtain ⟨l, hl⟩ := x.2.2 T hT
  have hne : l ≠ x.1 T := by
    intro heq
    apply hx
    apply continuousAt_iff_continuous_left'_right'.mpr
    constructor
    · change Tendsto x.1 (𝓝[<] T) (𝓝 (x.1 T))
      simpa only [heq] using hl
    · exact (x.2.1 T).mono Ioi_subset_Ici_self
  let c := boundedDistance l (x.1 T)
  have hc : 0 < c := lt_min (dist_pos.mpr hne) zero_lt_one
  have hp : Tendsto (fun p : Time × Time => boundedDistance (x.1 p.1) (x.1 p.2))
      ((𝓝[<] T) ×ˢ (𝓝[≥] T)) (𝓝 c) :=
    continuous_boundedDistance.continuousAt.tendsto.comp
      ((hl.comp tendsto_fst).prodMk_nhds
        ((show Tendsto x.1 (𝓝[≥] T) (𝓝 (x.1 T)) from x.2.1 T).comp tendsto_snd))
  obtain ⟨pa, hpa, pb, hpb, hab⟩ := eventually_prod_iff.mp
    (hp.eventually (Ioi_mem_nhds (show c / 2 < c by linarith)))
  obtain ⟨U, hU, hUp⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hpa
  obtain ⟨V, hV, hVp⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hpb
  obtain ⟨a, ha, hUa⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨b, hb, hVb⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨c / 2, half_pos hc, ?_⟩
  have hTr : (0 : ℝ) < (T : ℝ) := hT
  filter_upwards [self_mem_nhdsWithin,
    (nhdsWithin_le_nhds (Iio_mem_nhds hTr) : Iio (T : ℝ) ∈ 𝓝[>] (0 : ℝ)),
    (nhdsWithin_le_nhds (Iio_mem_nhds ha) : Iio a ∈ 𝓝[>] (0 : ℝ)),
    (nhdsWithin_le_nhds (Iio_mem_nhds hb) : Iio b ∈ 𝓝[>] (0 : ℝ))]
    with h hh hhT hha hhb
  change 0 < h at hh
  change h < (T : ℝ) at hhT
  change h < a at hha
  change h < b at hhb
  apply le_averagedIncrement_of_rectangle T hh x
  intro s hs t ht
  have hspos : 0 ≤ s := by linarith [hs.1]
  have htpos : 0 ≤ t := by linarith [ht.1]
  have hsU : s.toNNReal ∈ U := by
    apply hUa
    change |(s.toNNReal : ℝ) - (T : ℝ)| < a
    rw [Real.coe_toNNReal s hspos, abs_of_neg (by linarith [hs.2])]
    linarith [hs.1]
  have htV : t.toNNReal ∈ V := by
    apply hVb
    change |(t.toNNReal : ℝ) - (T : ℝ)| < b
    rw [Real.coe_toNNReal t htpos, abs_of_pos (by linarith [ht.1])]
    linarith [ht.2]
  exact (hab (hUp ⟨hsU, (Real.toNNReal_lt_iff_lt_coe hspos).mpr hs.2⟩)
    (hVp ⟨htV, by
      change (T : ℝ) ≤ (t.toNNReal : ℝ)
      rw [Real.coe_toNNReal t htpos]
      exact ht.1.le⟩)).le

/-- The averaged increment, bundled as a bounded continuous test function. -/
def averagedIncrementTest (T : Time) {h : ℝ} (hh : 0 < h) (hhT : h < (T : ℝ)) :
    D E →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨averagedIncrement T h, continuous_averagedIncrement T hh hhT⟩ 2 (by
      intro x y
      rw [Real.dist_eq]
      change |averagedIncrement T h x - averagedIncrement T h y| ≤ 2
      apply abs_le.mpr
      constructor
      · linarith [averagedIncrement_nonneg T hh x, averagedIncrement_le_one T hh y]
      · linarith [averagedIncrement_le_one T hh x, averagedIncrement_nonneg T hh y])

/-- Uniform averaged-increment bounds pass to every law in the weak closure. -/
theorem integral_averagedIncrement_le_of_mem_closure {A : Type*}
    (μ : A → ProbabilityMeasure (D E)) (T : Time) {h C : ℝ}
    (hh : 0 < h) (hhT : h < (T : ℝ))
    (hb : ∀ a, ∫ x, averagedIncrement T h x ∂(μ a : Measure (D E)) ≤ C)
    {ν : ProbabilityMeasure (D E)} (hν : ν ∈ closure (range μ)) :
    ∫ x, averagedIncrement T h x ∂(ν : Measure (D E)) ≤ C := by
  have hc : Continuous (fun ν : ProbabilityMeasure (D E) =>
      ∫ x, averagedIncrement T h x ∂(ν : Measure (D E))) :=
    ProbabilityMeasure.continuous_integral_boundedContinuousFunction
      (averagedIncrementTest T hh hhT)
  exact closure_minimal (by rintro _ ⟨a, rfl⟩; exact hb a)
    (isClosed_le hc continuous_const) hν

/-- Vanishing uniform averaged increments rule out a terminal jump in every closure law. -/
theorem measure_jump_at_T_eq_zero {A : Type*} (μ : A → ProbabilityMeasure (D E))
    (T : Time) (hT : 0 < T) (g : ℝ → ℝ)
    (hg : Tendsto g (𝓝[>] 0) (𝓝 0))
    (hb : ∀ a h, 0 < h → h < (T : ℝ) →
      ∫ x, averagedIncrement T h x ∂(μ a : Measure (D E)) ≤ g h)
    {ν : ProbabilityMeasure (D E)} (hν : ν ∈ closure (range μ)) :
    (ν : Measure (D E)) {x | ¬ ContinuousAt x.1 T} = 0 := by
  let r : ℕ → ℝ := fun n => ((T : ℝ) / 2) * (1 / (n + 1 : ℝ))
  have hTr : (0 : ℝ) < (T : ℝ) := hT
  have hr (n : ℕ) : 0 < r n ∧ r n < (T : ℝ) := by
    have hf : 0 < (1 / (n + 1 : ℝ)) := by positivity
    have hf' : 1 / (n + 1 : ℝ) ≤ 1 := (div_le_one (by positivity)).mpr (by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith)
    dsimp only [r]
    constructor
    · positivity
    · nlinarith
  have hr0 : Tendsto r atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [mul_zero] using
        tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ((T : ℝ) / 2)
    · exact Eventually.of_forall fun n => (hr n).1
  have hi (n : ℕ) : Integrable (averagedIncrement T (r n)) (ν : Measure (D E)) := by
    apply (integrable_const (1 : ℝ)).mono'
      (measurable_averagedIncrement T (hr n).1 (hr n).2).aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (averagedIncrement_nonneg T (hr n).1 x)]
      exact averagedIncrement_le_one T (hr n).1 x
  have he : Tendsto (fun n => ∫ x, averagedIncrement T (r n) x
      ∂(ν : Measure (D E))) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hg.comp hr0)
    · intro n
      exact integral_nonneg fun x => averagedIncrement_nonneg T (hr n).1 x
    · intro n
      exact integral_averagedIncrement_le_of_mem_closure μ T (hr n).1 (hr n).2
        (fun a => hb a (r n) (hr n).1 (hr n).2) hν
  let F : ℕ → D E → ℝ≥0∞ := fun n x => ENNReal.ofReal (averagedIncrement T (r n) x)
  have hF (n : ℕ) : Measurable (F n) :=
    ENNReal.measurable_ofReal.comp (measurable_averagedIncrement T (hr n).1 (hr n).2)
  have he' : Tendsto (fun n => ∫⁻ x, F n x ∂(ν : Measure (D E))) atTop (𝓝 0) := by
    have hconv := ENNReal.tendsto_ofReal he
    simp only [ENNReal.ofReal_zero] at hconv
    convert hconv using 1
    ext n
    exact (ofReal_integral_eq_lintegral_ofReal (hi n)
      (Eventually.of_forall fun x => averagedIncrement_nonneg T (hr n).1 x)).symm
  have hz : (∫⁻ x, liminf (fun n => F n x) atTop ∂(ν : Measure (D E))) = 0 := by
    apply le_antisymm _ bot_le
    exact (lintegral_liminf_le hF).trans_eq he'.liminf_eq
  have hae := (lintegral_eq_zero_iff (Measurable.liminf hF)).mp hz
  apply measure_mono_null (t := {x | liminf (fun n => F n x) atTop ≠ 0}) _
    (ae_iff.mp hae)
  intro x hx
  obtain ⟨c, hc, hcx⟩ := exists_pos_eventually_le_averagedIncrement T hT x hx
  have hlower : ENNReal.ofReal c ≤ liminf (fun n => F n x) atTop := by
    apply le_liminf_of_le (by isBoundedDefault)
    filter_upwards [hr0.eventually hcx] with n hn
    exact ENNReal.ofReal_le_ofReal hn
  exact ne_of_gt ((ENNReal.ofReal_pos.mpr hc).trans_le hlower)

end

end LatticeProb.Cadlag.HalfLine
