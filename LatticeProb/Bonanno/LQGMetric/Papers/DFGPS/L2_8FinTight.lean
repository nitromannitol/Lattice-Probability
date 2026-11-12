/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_8FinTight at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffTightEv

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Tightness transfer with `η`-dependent index thresholds (DFGPS L2.8, T:887–888)

Variant of `isTightMeasureSet_of_le_mul_ev` (`L2_8GffTightEv.lean`, same proof): for every `η` the
domination `B_i ≤ M · A_i` on events of probability `≥ 1 − η` is only required for `i` in a subset
`J_η ⊆ I` (in the application: `ε` below an `η`-dependent threshold), the remaining laws
`{B_i : i ∈ I \ J_η}` being tight by themselves (the far range, `lem2_8_tight_far'`).
Own elementary argument.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS

lemma isTightMeasureSet_union' {𝓧 : Type*} [TopologicalSpace 𝓧] [MeasurableSpace 𝓧]
    {S T : Set (Measure 𝓧)} (hS : IsTightMeasureSet S) (hT : IsTightMeasureSet T) :
    IsTightMeasureSet (S ∪ T) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at hS hT ⊢
  intro ε hε
  obtain ⟨K₁, hK₁, h₁⟩ := hS ε hε
  obtain ⟨K₂, hK₂, h₂⟩ := hT ε hε
  refine ⟨K₁ ∪ K₂, hK₁.union hK₂, fun μ hμ => ?_⟩
  rcases hμ with hμ | hμ
  · exact (measure_mono (compl_subset_compl.2 subset_union_left)).trans (h₁ μ hμ)
  · exact (measure_mono (compl_subset_compl.2 subset_union_right)).trans (h₂ μ hμ)

/-- **Tightness transfer with domination on events below `η`-dependent thresholds.** -/
theorem isTightMeasureSet_of_le_mul_ev' {X : Type*} [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ι : Type*} (I : Set ι) (A B : ι → Ω → C(X × X, ℝ))
    (hA : IsTightMeasureSet {μ | ∃ i ∈ I, μ = P.map (A i)})
    (hAm : ∀ i ∈ I, AEMeasurable (A i) P) (hBm : ∀ i ∈ I, AEMeasurable (B i) P)
    (hAd : ∀ i ∈ I, ∀ᵐ ω ∂P, ∀ x, A i ω (x, x) = 0)
    (hAn : ∀ i ∈ I, ∀ᵐ ω ∂P, ∀ p, 0 ≤ A i ω p)
    (hBp : ∀ i ∈ I, ∀ᵐ ω ∂P, B i ω ∈ pmetSet X)
    (hle : ∀ η : ℝ≥0∞, 0 < η → ∃ M : ℝ, 0 ≤ M ∧ ∃ J ⊆ I,
      IsTightMeasureSet {μ | ∃ i ∈ I \ J, μ = P.map (B i)} ∧
      ∀ i ∈ J, ∃ E : Set Ω, P Eᶜ ≤ η ∧ ∀ᵐ ω ∂P, ω ∈ E → ∀ p, B i ω p ≤ M * A i ω p) :
    IsTightMeasureSet {μ | ∃ i ∈ I, μ = P.map (B i)} := by
  classical
  refine isTightMeasureSet_of_approx fun η hη => ?_
  obtain ⟨M, hM0, J, hJI, hT2, hdom⟩ := hle η hη
  choose! E hPE hdomE using hdom
  -- measurable shrinkings of the events
  set F : ι → Set Ω := fun i => (toMeasurable P (E i)ᶜ)ᶜ with hF
  have hFm : ∀ i, MeasurableSet (F i) := fun i => (measurableSet_toMeasurable _ _).compl
  have hFE : ∀ i, F i ⊆ E i := fun i ω hω => by
    by_contra h
    exact hω (subset_toMeasurable P _ h)
  have hPF : ∀ i ∈ J, P (F i)ᶜ ≤ η := fun i hi => by
    rw [hF, compl_compl, measure_toMeasurable]; exact hPE i hi
  set B' : ι → Ω → C(X × X, ℝ) := fun i => (F i).piecewise (B i) fun _ => 0 with hB'
  have hB'm : ∀ i ∈ J, AEMeasurable (B' i) P := fun i hi =>
    ⟨(F i).piecewise (hBm i (hJI hi)).mk fun _ => 0,
      (hBm i (hJI hi)).measurable_mk.piecewise (hFm i) measurable_const, by
        filter_upwards [(hBm i (hJI hi)).ae_eq_mk] with ω hω
        by_cases h : ω ∈ F i <;> simp [hB', Set.piecewise, h, hω]⟩
  have hT := isTightMeasureSet_of_le_mul J A B' (fun _ => M) measurable_const (hA.subset (by rintro _ ⟨i, hi, rfl⟩; exact ⟨i, hJI hi, rfl⟩))
    (fun i hi => hAm i (hJI hi)) hB'm (fun i hi => hAd i (hJI hi))
    (fun i hi => (hBp i (hJI hi)).mono fun ω hω => by
      by_cases h : ω ∈ F i
      · simpa [hB', Set.piecewise, h] using hω
      · simp only [hB', Set.piecewise, h, ite_false]
        exact ⟨fun _ => rfl, fun _ _ _ => by simp⟩)
    (fun i hi => by
      filter_upwards [hdomE i hi, hAn i (hJI hi)] with ω hω hn p
      by_cases h : ω ∈ F i
      · simpa [hB', Set.piecewise, h] using hω (hFE i h) p
      · simp only [hB', Set.piecewise, h, ite_false, ContinuousMap.zero_apply]
        exact mul_nonneg hM0 (hn p))
  refine ⟨_, isTightMeasureSet_union' hT hT2, ?_⟩
  rintro μ ⟨i, hi, rfl⟩
  by_cases hiJ : i ∈ J
  · refine ⟨P.map (B' i), Or.inl ⟨i, hiJ, rfl⟩, fun C hC => ?_⟩
    have hCm : MeasurableSet Cᶜ := hC.isClosed.isOpen_compl.measurableSet
    rw [Measure.map_apply_of_aemeasurable (hBm i hi) hCm,
      Measure.map_apply_of_aemeasurable (hB'm i hiJ) hCm]
    refine (measure_mono ?_).trans ((measure_union_le _ _).trans
      (add_le_add_right (hPF i hiJ) _))
    intro ω hω
    by_cases h : ω ∈ F i
    · left; simpa [hB', Set.piecewise, h] using hω
    · exact Or.inr h
  · exact ⟨P.map (B i), Or.inr ⟨i, ⟨hi, hiJ⟩, rfl⟩, fun C _ => le_self_add⟩

end LQGMetric.DFGPS
