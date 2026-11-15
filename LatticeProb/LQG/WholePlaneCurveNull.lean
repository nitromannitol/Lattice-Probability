import LatticeProb.LQG.WholePlaneIndependentNull
import LatticeProb.LQG.MatingOfTreesCouplingPathwise

/-! # Independent curve traces and whole-plane quantum area -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Metric

namespace LatticeProb.Gauss

/-- A compact-time trace which is Lebesgue-null and independent of whole-plane
quantum area has zero quantum area inside the unit disk. -/
theorem IsWholePlaneGFF.ae_lqgMeasure_trace_inter_unitBall_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {μ : Ω → Measure ℂ} (hμ : LQG.IsLQGMeasure P γ hcirc μ)
    (hμm : AEMeasurable μ P) {g : Ω → C(ℝ, ℂ)} (hgm : Measurable g)
    (hind : IndepFun g μ P) {T : Set ℝ} (hT : IsCompact T)
    (hnull : ∀ᵐ ω ∂P, volume (g ω '' T) = 0) :
    ∀ᵐ ω ∂P, μ ω ((g ω '' T) ∩ ball (0 : ℂ) 1) = 0 := by
  let S : Set (C(ℝ, ℂ) × ℂ) := {p | p.2 ∈ p.1 '' T}
  have hS : MeasurableSet S := (ContinuousMap.isClosed_setOf_mem_image hT).measurableSet
  have hcomp : ∀ q : {q : ℚ // (q : ℝ) < 1},
      ∀ᵐ ω ∂P, μ ω ((g ω '' T) ∩ closedBall (0 : ℂ) q.1) = 0 := by
    intro q
    have h := hh.ae_lqgMeasure_inter_compact_eq_zero_of_indepFun hγ0 hγ2 hμ hμm hgm hind hS
      (by exact hnull) (isCompact_closedBall (0 : ℂ) (q : ℝ))
      (closedBall_subset_ball q.2)
    exact h
  filter_upwards [ae_all_iff.mpr hcomp] with ω hω
  have hcover : (g ω '' T) ∩ ball (0 : ℂ) 1 ⊆
      ⋃ q : {q : ℚ // (q : ℝ) < 1}, (g ω '' T) ∩ closedBall (0 : ℂ) q.1 := by
    rintro z ⟨hz, hzball⟩
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (mem_ball.mp hzball)
    exact mem_iUnion.mpr ⟨⟨q, hq2⟩, hz, mem_closedBall.mpr hq1.le⟩
  exact measure_mono_null hcover (measure_iUnion_null hω)

end LatticeProb.Gauss
