import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Lévy–Prokhorov distance controlled by finitely many integrals

For finite measures carried by a compact set `K` of a pseudometric space, the Lévy–Prokhorov
distance `MeasureTheory.levyProkhorovDist` is controlled by the integrals of a finite family of
continuous test functions with values in `[0, 1]`.

* `exists_testFamily_levyProkhorovDist_le`: for `ε > 0` there is a finite family `T` of continuous
  functions `g S` with values in `[0, 1]` such that, for finite measures `ν`, `ν'` with
  `ν Kᶜ = ν' Kᶜ = 0`, if `|∫ g S dν - ∫ g S dν'| ≤ ε` for every `S ∈ T` then
  `levyProkhorovDist ν ν' ≤ ε`. The test functions are thickened indicators of unions of balls
  of radius `ε / 4` centred at the points of a finite `ε / 4`-net of `K`.
* `tendstoInMeasure_levyProkhorovDist_of_forall_integral`: random finite measures carried by `K`
  whose integrals against every continuous test function with values in `[0, 1]` converge in
  probability converge in the Lévy–Prokhorov distance, in probability. No measurability of the
  random measures is assumed: the event that the distance is large is covered by finitely many
  events on which one integral is far from its limit.

The total mass enters through the test function equal to `1` on `K` (the family contains it), so
no separate mass condition is needed.
-/

open MeasureTheory Filter Metric Set Topology
open scoped ENNReal NNReal

namespace LatticeProb

section TestFamily

variable {X : Type*} [PseudoMetricSpace X]

/-- The `δ`-thickened indicator of the union of the balls of radius `δ` centred at the points
of `S`, as a real-valued function. -/
private noncomputable def ballUnionTest {δ : ℝ} (hδ : 0 < δ) (S : Finset X) (x : X) : ℝ :=
  (thickenedIndicator hδ (⋃ y ∈ S, ball y δ) x : ℝ)

variable [MeasurableSpace X] [OpensMeasurableSpace X]

/-- A thickened indicator, cast to `ℝ`, is integrable for a finite measure. -/
private lemma integrable_coe_thickenedIndicator {δ : ℝ} (hδ : 0 < δ) (E : Set X)
    (ρ : Measure X) [IsFiniteMeasure ρ] :
    Integrable (fun x => (thickenedIndicator hδ E x : ℝ)) ρ := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (NNReal.continuous_coe.comp (thickenedIndicator hδ E).continuous).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]
  exact (NNReal.coe_le_coe.2 (thickenedIndicator_le_one hδ E x)).trans_eq NNReal.coe_one

/-- The mass of a measurable set is at most the integral of its thickened indicator. -/
private lemma measureReal_le_integral_thickenedIndicator {δ : ℝ} (hδ : 0 < δ) {E : Set X}
    (hE : MeasurableSet E) (ρ : Measure X) [IsFiniteMeasure ρ] :
    ρ.real E ≤ ∫ x, (thickenedIndicator hδ E x : ℝ) ∂ρ := by
  rw [← integral_indicator_one hE]
  refine integral_mono ((integrable_const (1 : ℝ)).indicator hE)
    (integrable_coe_thickenedIndicator hδ E ρ) fun x => ?_
  by_cases hx : x ∈ E
  · rw [thickenedIndicator_one hδ E hx]
    simp [hx]
  · simp [hx]

/-- The integral of a thickened indicator is at most the mass of the thickening. -/
private lemma integral_thickenedIndicator_le_measureReal {δ : ℝ} (hδ : 0 < δ) (E : Set X)
    (ρ : Measure X) [IsFiniteMeasure ρ] :
    ∫ x, (thickenedIndicator hδ E x : ℝ) ∂ρ ≤ ρ.real (thickening δ E) := by
  rw [← integral_indicator_one isOpen_thickening.measurableSet]
  refine integral_mono (integrable_coe_thickenedIndicator hδ E ρ)
    ((integrable_const (1 : ℝ)).indicator isOpen_thickening.measurableSet) fun x => ?_
  by_cases hx : x ∈ thickening δ E
  · rw [indicator_of_mem hx, Pi.one_apply]
    exact (NNReal.coe_le_coe.2 (thickenedIndicator_le_one hδ E x)).trans_eq NNReal.coe_one
  · simp [hx, thickenedIndicator_zero hδ E hx]

end TestFamily

/-- **Lévy–Prokhorov distance from finitely many integrals.** Let `K` be a compact subset of a
pseudometric space and `ε > 0`. There is a finite family `T` of continuous test functions `g S`
with values in `[0, 1]` such that two finite measures carried by `K` whose integrals against
every `g S`, `S ∈ T`, differ by at most `ε` are at Lévy–Prokhorov distance at most `ε`.

The family consists of the `ε / 4`-thickened indicators of the unions of the balls of radius
`ε / 4` centred at the points of a subset of a finite `ε / 4`-net of `K`. -/
theorem exists_testFamily_levyProkhorovDist_le {X : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {K : Set X} (hK : IsCompact K) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ (T : Finset (Finset X)) (g : Finset X → X → ℝ), (∀ S, Continuous (g S)) ∧
      (∀ S x, 0 ≤ g S x ∧ g S x ≤ 1) ∧
      ∀ ν ν' : Measure X, IsFiniteMeasure ν → IsFiniteMeasure ν' → ν Kᶜ = 0 → ν' Kᶜ = 0 →
        (∀ S ∈ T, |∫ x, g S x ∂ν - ∫ x, g S x ∂ν'| ≤ ε) → levyProkhorovDist ν ν' ≤ ε := by
  classical
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨t, -, htK⟩ :=
    hK.elim_nhds_subcover (fun y => ball y (ε / 4)) fun y _ => ball_mem_nhds y hε4
  refine ⟨t.powerset, ballUnionTest hε4,
    fun S => NNReal.continuous_coe.comp (thickenedIndicator hε4 _).continuous,
    fun S x => ⟨NNReal.coe_nonneg _,
      (NNReal.coe_le_coe.2 (thickenedIndicator_le_one hε4 _ x)).trans_eq NNReal.coe_one⟩, ?_⟩
  intro ν ν' hν hν' hνK hν'K hT
  -- One-sided bound: `ρ B ≤ ρ' (thickening ε B) + ε` for every set `B`.
  have key : ∀ (ρ ρ' : Measure X) [IsFiniteMeasure ρ] [IsFiniteMeasure ρ'], ρ Kᶜ = 0 →
      (∀ S ∈ t.powerset, ∫ x, ballUnionTest hε4 S x ∂ρ ≤ ∫ x, ballUnionTest hε4 S x ∂ρ' + ε) →
      ∀ B : Set X, ρ B ≤ ρ' (thickening ε B) + ENNReal.ofReal ε := by
    intro ρ ρ' _ _ hρK hρ B
    set S := t.filter (fun y => (ball y (ε / 4) ∩ B).Nonempty) with hS_def
    set U := ⋃ y ∈ S, ball y (ε / 4) with hU_def
    have hU : MeasurableSet U := (isOpen_biUnion fun y _ => isOpen_ball).measurableSet
    have hBU : B ⊆ U ∪ Kᶜ := by
      intro z hz
      by_cases hzK : z ∈ K
      · obtain ⟨y, hyt, hzy⟩ := mem_iUnion₂.1 (htK hzK)
        exact Or.inl (mem_iUnion₂.2 ⟨y, Finset.mem_filter.2 ⟨hyt, z, hzy, hz⟩, hzy⟩)
      · exact Or.inr hzK
    have hthick : thickening (ε / 4) U ⊆ thickening ε B := by
      intro x hx
      obtain ⟨u, hu, hxu⟩ := mem_thickening_iff.1 hx
      obtain ⟨y, hyS, huy⟩ := mem_iUnion₂.1 hu
      obtain ⟨-, b, hby, hbB⟩ := Finset.mem_filter.1 hyS
      refine mem_thickening_iff.2 ⟨b, hbB, ?_⟩
      have h1 : dist u y < ε / 4 := huy
      have h2 : dist b y < ε / 4 := hby
      calc dist x b ≤ dist x u + dist u y + dist y b := dist_triangle4 x u y b
        _ < ε := by rw [dist_comm y b]; linarith
    have hS : ∫ x, ballUnionTest hε4 S x ∂ρ ≤ ∫ x, ballUnionTest hε4 S x ∂ρ' + ε :=
      hρ S (Finset.mem_powerset.2 (Finset.filter_subset _ _))
    have h4 : ρ.real U ≤ ∫ x, ballUnionTest hε4 S x ∂ρ :=
      measureReal_le_integral_thickenedIndicator hε4 hU ρ
    have h5 : ∫ x, ballUnionTest hε4 S x ∂ρ' ≤ ρ'.real (thickening (ε / 4) U) :=
      integral_thickenedIndicator_le_measureReal hε4 U ρ'
    have h6 : ρ'.real (thickening (ε / 4) U) ≤ ρ'.real (thickening ε B) :=
      measureReal_mono hthick
    have h3 : ρ.real U ≤ ρ'.real (thickening ε B) + ε := by linarith
    calc ρ B ≤ ρ (U ∪ Kᶜ) := measure_mono hBU
      _ ≤ ρ U + ρ Kᶜ := measure_union_le _ _
      _ = ENNReal.ofReal (ρ.real U) := by
          rw [hρK, add_zero, ofReal_measureReal (measure_ne_top ρ U)]
      _ ≤ ENNReal.ofReal (ρ'.real (thickening ε B) + ε) := ENNReal.ofReal_le_ofReal h3
      _ = ρ' (thickening ε B) + ENNReal.ofReal ε := by
          rw [ENNReal.ofReal_add measureReal_nonneg hε.le,
            ofReal_measureReal (measure_ne_top ρ' (thickening ε B))]
  have hle : levyProkhorovEDist ν ν' ≤ ENNReal.ofReal ε := by
    apply levyProkhorovEDist_le_of_forall
    intro ε' B hε' hε'top _
    have hε'r : ε < ε'.toReal := (ENNReal.ofReal_lt_iff_lt_toReal hε.le hε'top.ne).1 hε'
    have hmono : thickening ε B ⊆ thickening ε'.toReal B := thickening_mono hε'r.le B
    constructor
    · calc ν B ≤ ν' (thickening ε B) + ENNReal.ofReal ε :=
            key ν ν' hνK (fun S hS => by linarith [(abs_le.1 (hT S hS)).2]) B
        _ ≤ ν' (thickening ε'.toReal B) + ε' := add_le_add (measure_mono hmono) hε'.le
    · calc ν' B ≤ ν (thickening ε B) + ENNReal.ofReal ε :=
            key ν' ν hν'K (fun S hS => by linarith [(abs_le.1 (hT S hS)).1]) B
        _ ≤ ν (thickening ε'.toReal B) + ε' := add_le_add (measure_mono hmono) hε'.le
  exact ENNReal.toReal_le_of_le_ofReal hε.le hle

/-- **Lévy–Prokhorov convergence in probability from integrals.** Let `μ i ω` and `μ₀ ω` be
random finite measures carried by a compact set `K`. If for every continuous test function `g`
with values in `[0, 1]` the integrals `∫ g d(μ i ω)` converge in probability to `∫ g d(μ₀ ω)`
along `l`, then `levyProkhorovDist (μ i ω) (μ₀ ω)` converges to `0` in probability along `l`.

No measurability in `ω` is assumed: by `exists_testFamily_levyProkhorovDist_le`, the event that
the distance exceeds `δ` lies in a finite union of events on which one integral is off by more
than `δ / 2`, and the outer measure is finitely subadditive. -/
theorem tendstoInMeasure_levyProkhorovDist_of_forall_integral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {ι : Type*} {l : Filter ι} {K : Set X} (hK : IsCompact K)
    {μ : ι → Ω → FiniteMeasure X} {μ₀ : Ω → FiniteMeasure X}
    (hsupp : ∀ i ω, (μ i ω : Measure X) Kᶜ = 0) (hsupp₀ : ∀ ω, (μ₀ ω : Measure X) Kᶜ = 0)
    (hint : ∀ g : X → ℝ, Continuous g → (∀ x, 0 ≤ g x ∧ g x ≤ 1) → ∀ δ : ℝ, 0 < δ →
      Tendsto (fun i => P {ω | δ < |∫ x, g x ∂(μ i ω : Measure X) -
        ∫ x, g x ∂(μ₀ ω : Measure X)|}) l (𝓝 0)) :
    TendstoInMeasure P (fun i ω => levyProkhorovDist (μ i ω : Measure X) (μ₀ ω : Measure X))
      l 0 := by
  rw [tendstoInMeasure_iff_dist]
  intro δ hδ
  obtain ⟨T, g, hgc, hg01, hD⟩ := exists_testFamily_levyProkhorovDist_le hK (half_pos hδ)
  have hsub : ∀ i, {ω | δ ≤ dist (levyProkhorovDist (μ i ω : Measure X) (μ₀ ω : Measure X))
      ((0 : Ω → ℝ) ω)} ⊆ ⋃ S ∈ T, {ω | δ / 2 < |∫ x, g S x ∂(μ i ω : Measure X) -
        ∫ x, g S x ∂(μ₀ ω : Measure X)|} := by
    intro i ω hω
    simp only [mem_ofPred_eq, Pi.zero_apply, Real.dist_eq, sub_zero] at hω
    by_contra hnot
    simp only [mem_iUnion, mem_ofPred_eq, not_exists, not_lt] at hnot
    have hle := hD _ _ inferInstance inferInstance (hsupp i ω) (hsupp₀ ω) hnot
    have h0 : 0 ≤ levyProkhorovDist (μ i ω : Measure X) (μ₀ ω : Measure X) :=
      ENNReal.toReal_nonneg
    rw [abs_of_nonneg h0] at hω
    linarith
  have hsum := tendsto_finsetSum T
    (fun S _ => hint (g S) (hgc S) (hg01 S) (δ / 2) (half_pos hδ))
  simp only [Finset.sum_const_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun i => zero_le)
    fun i => ?_
  exact (measure_mono (hsub i)).trans (measure_biUnion_finset_le T _)

end LatticeProb
