import LatticeProb.Prob.LocalizedSimpleDensityPhase

/-! Finite box approximants for localized simple densities. -/

open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace LatticeProb

/-- A finite sum of finite scalar restrictions is a finite measure. -/
theorem isFiniteMeasure_sum_finite_restrictions {α κ : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (s : Finset κ) (c : κ → ℝ≥0∞)
    (hc : ∀ k ∈ s, c k ≠ ⊤) (A : κ → Set α) :
    IsFiniteMeasure (∑ k ∈ s, c k • μ.restrict (A k)) := by
  classical
  let ν : κ → Measure α := fun k => if c k = ⊤ then 0 else c k • μ.restrict (A k)
  let : ∀ k, IsFiniteMeasure (ν k) := fun k => by
    by_cases h : c k = ⊤
    · simp only [ν, h, ite_true]; infer_instance
    · simp only [ν, h, ite_false]
      exact (μ.restrict (A k)).smul_finite h
  have heq : (∑ k ∈ s, ν k) = ∑ k ∈ s, c k • μ.restrict (A k) := by
    apply Finset.sum_congr rfl
    intro k hk
    simp only [ν, hc k hk, ite_false]
  rw [← heq]
  infer_instance

/-- Finite simple densities on finite-measure restrictions admit finite
marked-box approximants in total variation. -/
theorem exists_finite_marked_box_approx_localized_simple_density
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
      IsFiniteMeasure (∑ c ∈ f.range, c • (ρ.restrict B).restrict (⋃ t ∈ F c, t)) ∧
      QuantumZipper.TV.tvDist ((ρ.restrict B).withDensity f)
        (∑ c ∈ f.range, c • (ρ.restrict B).restrict (⋃ t ∈ F c, t)) < ε := by
  classical
  let μ : Measure (E × (ι → ℝ)) := ρ.restrict B
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hB.ne
  obtain ⟨F, hF, hd, ht⟩ :=
    exists_finset_marked_Ico_boxes_tv_localized_simple_density_lt ρ B hB f hf hε
  refine ⟨F, hF, hd, ?_, ?_⟩
  · exact isFiniteMeasure_sum_finite_restrictions μ f.range id hf (fun c => ⋃ t ∈ F c, t)
  · rw [QuantumZipper.TV.tvDist_comm]
    simpa only [Measure.restrict_smul] using ht

end LatticeProb
