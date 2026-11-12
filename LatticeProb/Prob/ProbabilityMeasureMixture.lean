import Mathlib

/-!
# Countable mixtures of probability measures

For a family `Q k` of probability measures and weights `c k : ℝ≥0` with `∑ c k = 1`, the mixture
`∑ c k • Q k` is a probability measure.

* Its integral against a bounded continuous function is `∑' k, c k * ∫ f dQ k`.
* **Quasi-convexity of the Lévy–Prokhorov distance.** If every `Q k` with a non-zero weight is
  within `L` of a probability measure `ν`, then so is the mixture.
* **Continuity in the weights.** If the weights depend continuously on a parameter, with locally
  finite support, then the mixture, as a map into `ProbabilityMeasure E`, is continuous.
  In particular the normalized weights `w k z / ∑' j, w j z` of a locally finite family of
  continuous functions give a continuous interpolation `z ↦ ∑ k, (w k z / W z) • Q k`.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BoundedContinuousFunction

namespace LatticeProb

section Mixture

variable {E : Type*} [MeasurableSpace E] {ι : Type*}

/-- The mixture `∑' k, c k • Q k` of a family of measures with `ℝ≥0` weights. -/
noncomputable def weightedMixture (c : ι → ℝ≥0) (Q : ι → Measure E) : Measure E :=
  Measure.sum fun k => (c k : ℝ≥0∞) • Q k

theorem weightedMixture_apply (c : ι → ℝ≥0) (Q : ι → Measure E) {s : Set E}
    (hs : MeasurableSet s) :
    weightedMixture c Q s = ∑' k, (c k : ℝ≥0∞) * Q k s := by
  simp [weightedMixture, Measure.sum_apply _ hs]

theorem isProbabilityMeasure_weightedMixture {c : ι → ℝ≥0} (hc : HasSum c 1)
    (Q : ι → Measure E) [∀ k, IsProbabilityMeasure (Q k)] :
    IsProbabilityMeasure (weightedMixture c Q) := by
  refine ⟨?_⟩
  rw [weightedMixture_apply c Q MeasurableSet.univ]
  have h := ENNReal.coe_tsum hc.summable
  rw [hc.tsum_eq] at h
  simpa [measure_univ] using h.symm

/-- The mixture of probability measures with weights summing to one, as a probability measure. -/
noncomputable def weightedMixturePM {c : ι → ℝ≥0} (hc : HasSum c 1)
    (Q : ι → ProbabilityMeasure E) : ProbabilityMeasure E :=
  ⟨weightedMixture c (fun k => (Q k : Measure E)),
    isProbabilityMeasure_weightedMixture hc (fun k => (Q k : Measure E))⟩

theorem coe_weightedMixturePM {c : ι → ℝ≥0} (hc : HasSum c 1) (Q : ι → ProbabilityMeasure E) :
    ((weightedMixturePM hc Q : ProbabilityMeasure E) : Measure E)
      = weightedMixture c (fun k => (Q k : Measure E)) := rfl

theorem integral_weightedMixturePM [TopologicalSpace E] [OpensMeasurableSpace E] {c : ι → ℝ≥0}
    (hc : HasSum c 1) (Q : ι → ProbabilityMeasure E) (f : E →ᵇ ℝ) :
    ∫ x, f x ∂(weightedMixturePM hc Q : Measure E)
      = ∑' k, (c k : ℝ) * ∫ x, f x ∂(Q k : Measure E) := by
  rw [coe_weightedMixturePM]
  have hprob := isProbabilityMeasure_weightedMixture hc (fun k => (Q k : Measure E))
  have hint : Integrable f (weightedMixture c (fun k => (Q k : Measure E))) := f.integrable _
  unfold weightedMixture at hint ⊢
  rw [integral_sum_measure hint]
  refine tsum_congr (fun k => ?_)
  rw [integral_smul_measure, ENNReal.coe_toReal, smul_eq_mul]

/-- Quasi-convexity of the Lévy–Prokhorov distance: a probability measure `ν` that is within `L`
of every component of positive weight is within `L` of the mixture. -/
theorem levyProkhorovEDist_weightedMixture_le [PseudoEMetricSpace E] [OpensMeasurableSpace E]
    {c : ι → ℝ≥0} (hc : HasSum c 1) (ν : Measure E) [IsProbabilityMeasure ν]
    (Q : ι → Measure E) [∀ k, IsProbabilityMeasure (Q k)] (L : ℝ≥0∞)
    (hL : ∀ k, c k ≠ 0 → levyProkhorovEDist ν (Q k) ≤ L) :
    levyProkhorovEDist ν (weightedMixture c Q) ≤ L := by
  have := isProbabilityMeasure_weightedMixture hc Q
  have hsum1 : ∑' k, (c k : ℝ≥0∞) = 1 := by
    have h := ENNReal.coe_tsum hc.summable
    rw [hc.tsum_eq] at h
    simpa using h.symm
  refine levyProkhorovEDist_le_of_forall _ _ L (fun ε B hLε hεtop hB => ?_)
  have hth : MeasurableSet (thickening ε.toReal B) := isOpen_thickening.measurableSet
  constructor
  · calc ν B = ∑' k, (c k : ℝ≥0∞) * ν B := by
          rw [ENNReal.tsum_mul_right, hsum1, one_mul]
      _ ≤ ∑' k, ((c k : ℝ≥0∞) * Q k (thickening ε.toReal B) + (c k : ℝ≥0∞) * ε) := by
          refine ENNReal.tsum_le_tsum (fun k => ?_)
          by_cases hk : c k = 0
          · simp [hk]
          · have h1 := left_measure_le_of_levyProkhorovEDist_lt
              (lt_of_le_of_lt (hL k hk) hLε) hB
            calc (c k : ℝ≥0∞) * ν B
                ≤ (c k : ℝ≥0∞) * (Q k (thickening ε.toReal B) + ε) := mul_le_mul_right h1 _
              _ = _ := mul_add _ _ _
      _ = weightedMixture c Q (thickening ε.toReal B) + ε := by
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, hsum1, one_mul,
            weightedMixture_apply c Q hth]
  · calc weightedMixture c Q B = ∑' k, (c k : ℝ≥0∞) * Q k B := weightedMixture_apply c Q hB
      _ ≤ ∑' k, ((c k : ℝ≥0∞) * ν (thickening ε.toReal B) + (c k : ℝ≥0∞) * ε) := by
          refine ENNReal.tsum_le_tsum (fun k => ?_)
          by_cases hk : c k = 0
          · simp [hk]
          · have h1 := right_measure_le_of_levyProkhorovEDist_lt
              (lt_of_le_of_lt (hL k hk) hLε) hB
            calc (c k : ℝ≥0∞) * Q k B
                ≤ (c k : ℝ≥0∞) * (ν (thickening ε.toReal B) + ε) := mul_le_mul_right h1 _
              _ = _ := mul_add _ _ _
      _ = ν (thickening ε.toReal B) + ε := by
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, ENNReal.tsum_mul_right, hsum1, one_mul,
            one_mul]

/-- The real-valued form of the quasi-convexity of the Lévy–Prokhorov distance. -/
theorem levyProkhorovDist_weightedMixture_le [PseudoMetricSpace E] [OpensMeasurableSpace E]
    {c : ι → ℝ≥0} (hc : HasSum c 1) (ν : Measure E) [IsProbabilityMeasure ν]
    (Q : ι → Measure E) [∀ k, IsProbabilityMeasure (Q k)] {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ k, c k ≠ 0 → levyProkhorovDist ν (Q k) ≤ L) :
    levyProkhorovDist ν (weightedMixture c Q) ≤ L := by
  have := isProbabilityMeasure_weightedMixture hc Q
  have h := levyProkhorovEDist_weightedMixture_le hc ν Q (ENNReal.ofReal L) (fun k hk => by
    rw [ENNReal.le_ofReal_iff_toReal_le (levyProkhorovEDist_ne_top _ _) hL0]
    exact hL k hk)
  exact (ENNReal.le_ofReal_iff_toReal_le (levyProkhorovEDist_ne_top _ _) hL0).1 h

end Mixture

section Continuity

variable {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [OpensMeasurableSpace E]
  {ι Z : Type*} [TopologicalSpace Z]

/-- Continuity of the mixture as a function of continuously varying weights with locally finite
support. -/
theorem continuous_weightedMixturePM {c : ι → Z → ℝ≥0} (hc : ∀ z, HasSum (fun k => c k z) 1)
    (hcont : ∀ k, Continuous (c k))
    (hloc : ∀ z, ∃ U ∈ 𝓝 z, {k | ∃ y ∈ U, c k y ≠ 0}.Finite) (Q : ι → ProbabilityMeasure E) :
    Continuous fun z => weightedMixturePM (hc z) Q := by
  rw [ProbabilityMeasure.continuous_iff_forall_continuous_integral]
  intro f
  simp only [integral_weightedMixturePM]
  rw [continuous_iff_continuousAt]
  intro z
  obtain ⟨U, hU, hfin⟩ := hloc z
  have hev : (fun y => ∑' k, (c k y : ℝ) * ∫ x, f x ∂(Q k : Measure E))
      =ᶠ[𝓝 z] fun y => ∑ k ∈ hfin.toFinset, (c k y : ℝ) * ∫ x, f x ∂(Q k : Measure E) := by
    filter_upwards [hU] with y hy
    refine tsum_eq_sum (fun k hk => ?_)
    have : c k y = 0 := by
      by_contra hne
      exact hk (hfin.mem_toFinset.2 ⟨y, hy, hne⟩)
    simp [this]
  refine ContinuousAt.congr ?_ hev.symm
  refine (continuous_finsetSum _ (fun k _ => ?_)).continuousAt
  exact ((NNReal.continuous_coe.comp (hcont k))).mul continuous_const

/-- The normalization `w k z / ∑' j, w j z` of a family of nonnegative weights. -/
noncomputable def normalizedWeight (w : ι → Z → ℝ≥0) (k : ι) (z : Z) : ℝ≥0 :=
  w k z / ∑' j, w j z

theorem summable_of_locallyFinite {w : ι → Z → ℝ≥0}
    (hloc : ∀ z, ∃ U ∈ 𝓝 z, {k | ∃ y ∈ U, w k y ≠ 0}.Finite) (z : Z) :
    Summable fun k => w k z := by
  obtain ⟨U, hU, hfin⟩ := hloc z
  refine summable_of_ne_finset_zero (s := hfin.toFinset) (fun k hk => ?_)
  by_contra hne
  exact hk (hfin.mem_toFinset.2 ⟨z, mem_of_mem_nhds hU, hne⟩)

theorem continuous_tsum_of_locallyFinite {w : ι → Z → ℝ≥0} (hw : ∀ k, Continuous (w k))
    (hloc : ∀ z, ∃ U ∈ 𝓝 z, {k | ∃ y ∈ U, w k y ≠ 0}.Finite) :
    Continuous fun z => ∑' k, w k z := by
  rw [continuous_iff_continuousAt]
  intro z
  obtain ⟨U, hU, hfin⟩ := hloc z
  have hev : (fun y => ∑' k, w k y) =ᶠ[𝓝 z] fun y => ∑ k ∈ hfin.toFinset, w k y := by
    filter_upwards [hU] with y hy
    exact tsum_eq_sum (fun k hk => by
      by_contra hne
      exact hk (hfin.mem_toFinset.2 ⟨y, hy, hne⟩))
  exact ContinuousAt.congr (continuous_finsetSum _ (fun k _ => hw k)).continuousAt hev.symm

theorem hasSum_normalizedWeight {w : ι → Z → ℝ≥0}
    (hloc : ∀ z, ∃ U ∈ 𝓝 z, {k | ∃ y ∈ U, w k y ≠ 0}.Finite) (hpos : ∀ z, ∃ k, w k z ≠ 0)
    (z : Z) : HasSum (fun k => normalizedWeight w k z) 1 := by
  have hs : Summable fun k => w k z := summable_of_locallyFinite hloc z
  have hW : (∑' j, w j z) ≠ 0 := by
    obtain ⟨k, hk⟩ := hpos z
    exact ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.2 hk) (hs.le_tsum k (fun j _ => zero_le)))
  have := hs.hasSum.mul_right (∑' j, w j z)⁻¹
  simpa [normalizedWeight, div_eq_mul_inv, mul_inv_cancel₀ hW] using this

theorem continuous_normalizedWeight {w : ι → Z → ℝ≥0} (hw : ∀ k, Continuous (w k))
    (hloc : ∀ z, ∃ U ∈ 𝓝 z, {k | ∃ y ∈ U, w k y ≠ 0}.Finite) (hpos : ∀ z, ∃ k, w k z ≠ 0)
    (k : ι) : Continuous (normalizedWeight w k) := by
  refine (hw k).div (continuous_tsum_of_locallyFinite hw hloc) (fun z => ?_)
  have hs : Summable fun k => w k z := summable_of_locallyFinite hloc z
  obtain ⟨j, hj⟩ := hpos z
  exact ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.2 hj) (hs.le_tsum j (fun i _ => zero_le)))

/-- Interpolation of a family of probability measures `Q k` by a locally finite family of
continuous nonnegative weights `w k` that do not vanish simultaneously: the mixture with
normalized weights depends continuously on the parameter. -/
theorem continuous_normalizedMixturePM {w : ι → Z → ℝ≥0} (hw : ∀ k, Continuous (w k))
    (hloc : ∀ z, ∃ U ∈ 𝓝 z, {k | ∃ y ∈ U, w k y ≠ 0}.Finite) (hpos : ∀ z, ∃ k, w k z ≠ 0)
    (Q : ι → ProbabilityMeasure E) :
    Continuous fun z => weightedMixturePM (hasSum_normalizedWeight hloc hpos z) Q := by
  refine continuous_weightedMixturePM (c := normalizedWeight w)
    (fun z => hasSum_normalizedWeight hloc hpos z) (continuous_normalizedWeight hw hloc hpos)
    (fun z => ?_) Q
  obtain ⟨U, hU, hfin⟩ := hloc z
  refine ⟨U, hU, hfin.subset ?_⟩
  rintro k ⟨y, hy, hne⟩
  refine ⟨y, hy, fun h0 => hne ?_⟩
  simp [normalizedWeight, h0]

end Continuity

end LatticeProb
