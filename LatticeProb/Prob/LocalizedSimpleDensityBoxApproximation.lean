import LatticeProb.Prob.TVMarkedBoxFiniteSum
import LatticeProb.Prob.SimpleDensityLevelSets

/-! Marked-box approximation of localized simple densities. -/

open Set MeasureTheory
open scoped ENNReal BigOperators

namespace LatticeProb

/-- A finite-valued simple density over a finite-measure restriction can be
approximated in total variation by finite sums of marked-box restrictions. -/
theorem exists_finset_marked_Ico_boxes_tv_localized_simple_density_lt
    {E ι : Type*} [MeasurableSpace E] [Finite ι]
    (ρ : Measure (E × (ι → ℝ))) (B : Set (E × (ι → ℝ)))
    (hB : ρ B < ⊤) (f : SimpleFunc (E × (ι → ℝ)) ℝ≥0∞)
    (hf : ∀ c ∈ f.range, c ≠ ⊤) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ F : ℝ≥0∞ → Finset (Set (E × (ι → ℝ))),
      (∀ c ∈ f.range, (↑(F c) : Set (Set (E × (ι → ℝ)))) ⊆
        Set.image2 (· ×ˢ ·) {s : Set E | MeasurableSet s}
          (Set.univ.pi '' Set.univ.pi (fun _ : ι =>
            {s : Set ℝ | ∃ u v : ℝ, s = Ico u v}))) ∧
      (∀ c ∈ f.range, (↑(F c) : Set (Set (E × (ι → ℝ)))).PairwiseDisjoint id) ∧
      QuantumZipper.TV.tvDist
        (∑ c ∈ f.range, (c • ρ.restrict B).restrict (⋃ t ∈ F c, t))
        ((ρ.restrict B).withDensity f) < ε := by
  classical
  let μ : Measure (E × (ι → ℝ)) := ρ.restrict B
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hB.ne
  let ν : ℝ≥0∞ → Measure (E × (ι → ℝ)) := fun c =>
    if c = ⊤ then 0 else c • μ
  let : ∀ c, IsFiniteMeasure (ν c) := fun c => by
    by_cases hc : c = ⊤
    · simp only [ν, hc, ite_true]
      infer_instance
    · simp only [ν, hc, ite_false]
      exact μ.smul_finite hc
  obtain ⟨F, hF, hd, ht⟩ :=
    exists_finset_marked_Ico_boxes_tv_sum_restrict_lt ν
      (fun c => f ⁻¹' {c}) (fun c => f.measurableSet_fiber c) f.range hε
  refine ⟨F, hF, hd, ?_⟩
  have heq (c : ℝ≥0∞) (hc : c ∈ f.range) : ν c = c • μ := by
    simp only [ν, hf c hc, ite_false]
  have hsum : (∑ c ∈ f.range, (ν c).restrict (f ⁻¹' {c})) =
      μ.withDensity f := by
    rw [withDensity_simpleFunc_eq_sum_restrict]
    apply Finset.sum_congr rfl
    intro c hc
    rw [heq c hc, Measure.restrict_smul]
  rw [hsum] at ht
  have hsum' : (∑ c ∈ f.range, (ν c).restrict (⋃ t ∈ F c, t)) =
      ∑ c ∈ f.range, (c • ρ.restrict B).restrict (⋃ t ∈ F c, t) := by
    apply Finset.sum_congr rfl
    intro c hc
    rw [heq c hc]
  rw [hsum'] at ht
  exact ht

end LatticeProb
