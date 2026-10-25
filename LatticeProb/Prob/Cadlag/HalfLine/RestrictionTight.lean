import LatticeProb.Prob.Cadlag.HalfLine.TerminalJump
import LatticeProb.Prob.Cadlag.HalfLine.RestrictionMeasurable
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.MetricSpace.Polish

/-!
# Tightness of finite-horizon restrictions

Evaluation is jointly measurable in time and path, so expected averaged increments are
controlled by deterministic-time increments. A measurable map continuous almost everywhere
under the limit law preserves weak convergence. Hence restriction to a finite horizon is
continuous on every compact set of half-line laws without a fixed jump at the horizon, and in a
Polish finite-horizon space the restricted laws are tight.
-/

namespace LatticeProb.Cadlag.HalfLine

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology NNReal ENNReal

noncomputable section

/-- The first grid point of mesh `1/(n+1)` strictly to the right of a time. -/
def gridAbove (n : ℕ) (t : Time) : Time :=
  ((⌊t * (n + 1)⌋₊ + 1 : ℕ) : ℝ≥0) / (n + 1)

/-- The grid point lies strictly to the right of the time. -/
theorem lt_gridAbove (n : ℕ) (t : Time) : t < gridAbove n t := by
  rw [gridAbove, lt_div_iff₀ (by positivity)]
  push_cast
  exact Nat.lt_floor_add_one _

/-- The grid point lies within one mesh of the time. -/
theorem gridAbove_le (n : ℕ) (t : Time) : gridAbove n t ≤ t + 1 / (n + 1) := by
  rw [gridAbove, div_le_iff₀ (by positivity), add_mul,
    div_mul_cancel₀ (1 : ℝ≥0) (by positivity : ((n : ℝ≥0) + 1) ≠ 0)]
  push_cast
  exact add_le_add (Nat.floor_le zero_le) le_rfl

/-- The grid points converge to the time from the right. -/
theorem tendsto_gridAbove (t : Time) :
    Tendsto (fun n => gridAbove n t) atTop (𝓝[Ici t] t) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, Eventually.of_forall fun n => (lt_gridAbove n t).le⟩
  rw [← NNReal.tendsto_coe]
  have hup : Tendsto (fun n : ℕ => (t : ℝ) + 1 / ((n : ℝ) + 1)) atTop (𝓝 (t : ℝ)) := by
    simpa only [add_zero] using
      tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun n => NNReal.coe_le_coe.mpr (lt_gridAbove n t).le) (fun n => ?_)
  have h := NNReal.coe_le_coe.mpr (gridAbove_le n t)
  push_cast at h
  exact h

variable {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]

/-- Evaluation is jointly measurable in the time and the path. -/
theorem measurable_eval_uncurry : Measurable (fun p : Time × D E => p.2.1 p.1) := by
  have hstep (n : ℕ) : Measurable (fun p : Time × D E => p.2.1 (gridAbove n p.1)) := by
    have hG : Measurable (fun q : D E × ℕ => q.1.1 (((q.2 + 1 : ℕ) : ℝ≥0) / (n + 1))) :=
      measurable_from_prod_countable_left (fun k => by
        exact measurable_eval (E := E) (((k + 1 : ℕ) : ℝ≥0) / (n + 1)))
    have hk : Measurable (fun p : Time × D E => (p.2, ⌊p.1 * (n + 1)⌋₊)) :=
      measurable_snd.prodMk ((measurable_fst.mul_const _).nat_floor)
    exact hG.comp hk
  apply measurable_of_tendsto_metrizable hstep
  apply tendsto_pi_nhds.mpr
  intro p
  exact (p.2.2.1 p.1).tendsto.comp (tendsto_gridAbove p.1)

variable [SecondCountableTopology E]

/-- The bounded increment between two real times is jointly measurable with the path. -/
theorem measurable_boundedDistance_uncurry :
    Measurable (fun p : (ℝ × ℝ) × D E =>
      boundedDistance (p.2.1 p.1.1.toNNReal) (p.2.1 p.1.2.toNNReal)) := by
  have he : Measurable (fun q : ℝ × D E => q.2.1 q.1.toNNReal) :=
    measurable_eval_uncurry.comp
      ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd)
  exact continuous_boundedDistance.measurable.comp
    ((he.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).prodMk
      (he.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))

/-- Expected averaged increments are bounded by any uniform bound on the expected increments
between the two averaging windows. -/
theorem integral_averagedIncrement_le (μ : Measure (D E)) [IsProbabilityMeasure μ]
    (T : Time) {h c : ℝ} (hh : 0 < h)
    (hb : ∀ s t : ℝ, (T : ℝ) - h < s → s ≤ T → (T : ℝ) < t → t ≤ T + h →
      ∫ x, boundedDistance (x.1 s.toNNReal) (x.1 t.toNNReal) ∂μ ≤ c) :
    ∫ x, averagedIncrement T h x ∂μ ≤ c := by
  let S := Ioc ((T : ℝ) - h) T
  let S' := Ioc (T : ℝ) (T + h)
  let ρ : Measure (ℝ × ℝ) := (volume.restrict S).prod (volume.restrict S')
  haveI : IsFiniteMeasure (volume.restrict S) :=
    isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
  haveI : IsFiniteMeasure (volume.restrict S') :=
    isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
  let F : (ℝ × ℝ) → D E → ℝ := fun p x => boundedDistance (x.1 p.1.toNNReal) (x.1 p.2.toNNReal)
  have hF : Measurable (fun q : (ℝ × ℝ) × D E => F q.1 q.2) := measurable_boundedDistance_uncurry
  have hFb (p : ℝ × ℝ) (x : D E) : ‖F p x‖ ≤ 1 := norm_boundedDistance_le_one _ _
  have hFp (x : D E) : Integrable (fun p => F p x) ρ :=
    Integrable.of_bound (hF.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable 1
      (ae_of_all _ fun p => hFb p x)
  have hFxp : Integrable (fun q : D E × (ℝ × ℝ) => F q.2 q.1) (μ.prod ρ) :=
    Integrable.of_bound (hF.comp measurable_swap).aestronglyMeasurable 1
      (ae_of_all _ fun q => hFb q.2 q.1)
  have hΨ (x : D E) : averagedIncrement T h x = (h ^ 2)⁻¹ * ∫ p, F p x ∂ρ := by
    rw [averagedIncrement, intervalIntegral.integral_of_le (by linarith : (T : ℝ) - h ≤ T)]
    simp only [intervalIntegral.integral_of_le (by linarith : (T : ℝ) ≤ T + h)]
    rw [integral_prod _ (hFp x)]
  have hρ : ρ = (volume.prod volume).restrict (S ×ˢ S') := Measure.prod_restrict S S'
  have hmass : ρ.real univ = h * h := by
    show ((volume.restrict S).prod (volume.restrict S') univ).toReal = h * h
    rw [← univ_prod_univ, Measure.prod_prod, Measure.restrict_apply_univ,
      Measure.restrict_apply_univ, Real.volume_Ioc, Real.volume_Ioc, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith)]
    ring_nf
  have hmem : ∀ᵐ p ∂ρ, p ∈ S ×ˢ S' := by
    rw [hρ]
    exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
  calc
    ∫ x, averagedIncrement T h x ∂μ = (h ^ 2)⁻¹ * ∫ x, ∫ p, F p x ∂ρ ∂μ := by
      simp only [hΨ, integral_const_mul]
    _ = (h ^ 2)⁻¹ * ∫ p, ∫ x, F p x ∂μ ∂ρ := by
      rw [integral_integral_swap hFxp]
    _ ≤ (h ^ 2)⁻¹ * ∫ _p, c ∂ρ := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (sq_nonneg h))
      apply integral_mono_ae hFxp.integral_prod_right (integrable_const c)
      filter_upwards [hmem] with p hp
      exact hb p.1 p.2 hp.1.1 hp.1.2 hp.2.1 hp.2.2
    _ = c := by
      rw [integral_const, smul_eq_mul, hmass]
      field_simp

/-- Weak convergence is preserved by a measurable map continuous almost everywhere under the
limit law (Billingsley, Theorem 2.7). -/
theorem _root_.MeasureTheory.ProbabilityMeasure.tendsto_map_of_ae_continuousAt
    {X Y ι : Type*} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
    [HasOuterApproxClosed X] [MeasurableSpace Y] [TopologicalSpace Y] [OpensMeasurableSpace Y]
    {L : Filter ι} [L.IsCountablyGenerated] {μs : ι → ProbabilityMeasure X}
    {μ : ProbabilityMeasure X} (hμ : Tendsto μs L (𝓝 μ)) {f : X → Y} (hf : Measurable f)
    (hc : ∀ᵐ x ∂(μ : Measure X), ContinuousAt f x) :
    Tendsto (fun i => (μs i).map hf.aemeasurable) L (𝓝 (μ.map hf.aemeasurable)) := by
  apply tendsto_of_forall_isClosed_limsup_le'
  intro F hF
  simp only [ProbabilityMeasure.toMeasure_map, Measure.map_apply hf hF.measurableSet]
  have hsub : closure (f ⁻¹' F) ⊆ f ⁻¹' F ∪ {x | ¬ ContinuousAt f x} := by
    intro x hx
    by_cases hcx : ContinuousAt f x
    · exact Or.inl (hF.closure_subset (closure_mono (image_preimage_subset f F)
        (hcx.continuousWithinAt.mem_closure_image hx)))
    · exact Or.inr hcx
  have hD : (μ : Measure X) {x | ¬ ContinuousAt f x} = 0 := ae_iff.mp hc
  calc
    limsup (fun i => (μs i : Measure X) (f ⁻¹' F)) L
        ≤ limsup (fun i => (μs i : Measure X) (closure (f ⁻¹' F))) L :=
      limsup_le_limsup (Eventually.of_forall fun i => measure_mono subset_closure)
    _ ≤ (μ : Measure X) (closure (f ⁻¹' F)) :=
      ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμ isClosed_closure
    _ ≤ (μ : Measure X) (f ⁻¹' F ∪ {x | ¬ ContinuousAt f x}) := measure_mono hsub
    _ ≤ (μ : Measure X) (f ⁻¹' F) + (μ : Measure X) {x | ¬ ContinuousAt f x} :=
      measure_union_le _ _
    _ = (μ : Measure X) (f ⁻¹' F) := by rw [hD, add_zero]

/-- In a Polish space, a set of probability laws with compact closure is tight
(Prokhorov's converse, through a compatible complete metric). -/
theorem _root_.MeasureTheory.isTightMeasureSet_of_isCompact_closure_of_polishSpace
    {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {S : Set (ProbabilityMeasure X)} (hS : IsCompact (closure S)) :
    IsTightMeasureSet {((μ : ProbabilityMeasure X) : Measure X) | μ ∈ S} := by
  letI := upgradeIsCompletelyMetrizable X
  exact isTightMeasureSet_of_isCompact_closure hS

end

section Restriction

variable {E : Type*} [NormedAddCommGroup E] [SeparableSpace E] [MeasurableSpace E]
  [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- Restriction maps a compact set of half-line laws without a fixed jump at the horizon
continuously, so the restricted laws of the family have compact closure. -/
theorem isCompact_closure_range_restrict {A : Type*} {T : ℝ} (hT : 0 < T)
    (μ : A → ProbabilityMeasure (D E)) (hcompact : IsCompact (closure (range μ)))
    (hjump : ∀ ν ∈ closure (range μ),
      (ν : Measure (D E)) {x | ¬ ContinuousAt x.1 ⟨T, hT.le⟩} = 0) :
    IsCompact (closure (range (fun a =>
      (μ a).map (measurable_restrict (E := E) T).aemeasurable))) := by
  let Φ : ProbabilityMeasure (D E) → ProbabilityMeasure (Cadlag.D T E) :=
    fun ν => ν.map (measurable_restrict (E := E) T).aemeasurable
  have hcont : ContinuousOn Φ (closure (range μ)) := by
    intro ν hν
    have hc : ∀ᵐ x ∂(ν : Measure (D E)), ContinuousAt (restrict (E := E) T) x :=
      (ae_iff.mpr (hjump ν hν)).mono fun x hx => continuousAt_restrict hT hx
    exact ProbabilityMeasure.tendsto_map_of_ae_continuousAt (μs := id)
      (L := 𝓝[closure (range μ)] ν) nhdsWithin_le_nhds (measurable_restrict T) hc
  have hK := hcompact.image_of_continuousOn hcont
  have hsub : range (fun a => Φ (μ a)) ⊆ Φ '' closure (range μ) := by
    rintro _ ⟨a, rfl⟩
    exact ⟨μ a, subset_closure ⟨a, rfl⟩, rfl⟩
  exact hK.of_isClosed_subset isClosed_closure (closure_minimal hsub hK.isClosed)

omit [MeasurableSpace E] [BorelSpace E] in
/-- In a Polish finite-horizon space, the restricted laws of a relatively compact family of
half-line laws without a fixed jump at the horizon are tight. -/
theorem isTightMeasureSet_restrict {A : Type*} {T : ℝ} (hT : 0 < T)
    (hsep : SeparableSpace (Cadlag.D T E)) (hcm : IsCompletelyMetrizableSpace (Cadlag.D T E))
    (μ : A → ProbabilityMeasure (D E)) (hcompact : IsCompact (closure (range μ)))
    (hjump : ∀ ν ∈ closure (range μ),
      (ν : Measure (D E)) {x | ¬ ContinuousAt x.1 ⟨T, hT.le⟩} = 0) :
    IsTightMeasureSet {(((μ a).map (measurable_restrict (E := E) T).aemeasurable :
      ProbabilityMeasure (Cadlag.D T E)) : Measure (Cadlag.D T E)) | a} := by
  letI := hsep
  letI := hcm
  have h := isTightMeasureSet_of_isCompact_closure_of_polishSpace
    (isCompact_closure_range_restrict hT μ hcompact hjump)
  convert h using 1
  ext m
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨_, ⟨a, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, rfl⟩

/-- Uniformly vanishing averaged increments across the horizon and relative compactness of
the half-line laws give tightness of the restricted laws in a Polish finite-horizon space. -/
theorem isTightMeasureSet_restrict_of_averagedIncrement {A : Type*} (T : Time) (hT : 0 < T)
    (hsep : SeparableSpace (Cadlag.D T E)) (hcm : IsCompletelyMetrizableSpace (Cadlag.D T E))
    (μ : A → ProbabilityMeasure (D E)) (hcompact : IsCompact (closure (range μ)))
    (g : ℝ → ℝ) (hg : Tendsto g (𝓝[>] 0) (𝓝 0))
    (hb : ∀ a h, 0 < h → h < (T : ℝ) →
      ∫ x, averagedIncrement T h x ∂(μ a : Measure (D E)) ≤ g h) :
    IsTightMeasureSet {(((μ a).map (measurable_restrict (E := E) T).aemeasurable :
      ProbabilityMeasure (Cadlag.D T E)) : Measure (Cadlag.D T E)) | a} :=
  isTightMeasureSet_restrict (T := (T : ℝ)) hT hsep hcm μ hcompact
    (fun _ hν => measure_jump_at_T_eq_zero μ T hT g hg hb hν)

end Restriction

end LatticeProb.Cadlag.HalfLine
