import LatticeProb.Prob.RandomRootExitSegment

/-! # Nested exit segments at almost surely equal roots -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Metric Filter
open scoped NNReal ENNReal Topology

namespace LatticeProb

/-- If two random roots agree almost surely, the nested-exit segment event for one has
    a representative measurable at the outer exit of the process rooted at the other. -/
theorem exists_measurableSet_ball_subset_ae_equal_root_exit_segment
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
    {f : Ω → C(ℝ, EuclideanSpace ℝ (Fin d))} {S T : Ω → ℝ}
    (hf : Measurable f) (hS : Measurable S) (hST : T =ᵐ[μ] S)
    (hproper : ∀ᵐ ω ∂μ, Tendsto (f ω) (cocompact ℝ) (cocompact _))
    (z : EuclideanSpace ℝ (Fin d)) {r R a : ℝ} (hr : r ≤ R) (ha : 0 < a) :
    ∃ s : Set Ω,
      MeasurableSet[(isStoppingTime_openExitTime
        (show ∀ t, StronglyMeasurable (randomRootProcess f S t) from by
          intro t
          exact ((continuous_eval : Continuous (fun p : C(ℝ, EuclideanSpace ℝ (Fin d)) × ℝ => p.1 p.2)).measurable.comp
            (hf.prodMk (hS.add measurable_const))).stronglyMeasurable)
        (fun ω => (f ω).continuous.comp (continuous_const.add NNReal.continuous_coe))
        (isOpen_ball : IsOpen (ball z R))).measurableSpace] s ∧
      ∀ᵐ ω ∂μ, (ω ∈ s ↔ ∃ w, ball w a ⊆
        (fun t : ℝ => randomRootProcess f T t.toNNReal ω) '' Icc
        ((openExitTime (randomRootProcess f T) (ball z r) ω).toNNReal : ℝ)
        ((openExitTime (randomRootProcess f T) (ball z R) ω).toNNReal : ℝ)) := by
  obtain ⟨s, hs, he⟩ :=
    exists_measurableSet_ball_subset_randomRoot_exit_segment hf hS hproper z hr ha
  refine ⟨s, hs, ?_⟩
  filter_upwards [he, hST] with ω heω hω
  have hX (t : ℝ≥0) : randomRootProcess f T t ω = randomRootProcess f S t ω := by
    simp only [randomRootProcess, hω]
  have hclock (U : Set (EuclideanSpace ℝ (Fin d))) :
      openExitTime (randomRootProcess f T) U ω = openExitTime (randomRootProcess f S) U ω := by
    change (⨅ t : {t : ℝ≥0 // f ω (T ω + (t : ℝ)) ∉ U}, (t.val : ℝ≥0∞)) =
      (⨅ t : {t : ℝ≥0 // f ω (S ω + (t : ℝ)) ∉ U}, (t.val : ℝ≥0∞))
    rw [hω]
  simpa only [hclock, hX] using heω

end LatticeProb
