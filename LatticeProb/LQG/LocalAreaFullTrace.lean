import LatticeProb.LQG.LocalAreaIndependentTrace

/-! # Independent full traces for locally identified quantum areas -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Metric
open LQGMetric MatedCRTHarmonic LatticeProb.Gauss
open LatticeProb.LQG.LQGMeasureNonatomicMass

namespace LatticeProb.LQG

/-- A locally identified quantum area does not charge the part of an
independent Lebesgue-null full trace contained in the unit disk. -/
theorem ae_localArea_range_eq_zero_of_indep_field
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → DistC} (hX : LQGMetric.IsWholePlaneGFF X P)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc)
    (hcircle : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ᵐ z ∂volume,
      hcirc ω (dyadicScale k) z = circleAvg (X ω) (dyadicScale k) z)
    {γ α : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {g : Ω → C(ℝ, ℂ)} (hgm : Measurable g) (hind : IndepFun g X P)
    (hnull : ∀ᵐ ω ∂P, volume (range (g ω)) = 0)
    {ν : Ω → Measure ℂ}
    (hloc : ∀ᵐ ω ∂P, (ν ω).restrict (ball (0 : ℂ) 1) =
      (CellScaling.lqgArea γ (GMSCase.addLogSing α (X ω))).restrict (ball 0 1)) :
    ∀ᵐ ω ∂P, ν ω (range (g ω) ∩ ball (0 : ℂ) 1) = 0 := by
  have heach : ∀ n : ℕ, ∀ᵐ ω ∂P,
      ν ω ((g ω '' Icc (-(n : ℝ)) n) ∩ ball (0 : ℂ) 1) = 0 := by
    intro n
    apply ae_localArea_trace_eq_zero_of_indep_field hX hh hcircle hγ0 hγ2 hα
      hgm hind isCompact_Icc _ hloc
    filter_upwards [hnull] with ω hω
    exact measure_mono_null (image_subset_range _ _) hω
  filter_upwards [ae_all_iff.mpr heach] with ω hω
  have hrange : range (g ω) = ⋃ n : ℕ, g ω '' Icc (-(n : ℝ)) n := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      obtain ⟨n, hn⟩ := exists_nat_gt |t|
      refine mem_iUnion.mpr ⟨n, t, ⟨?_, ?_⟩, rfl⟩
      · linarith [neg_abs_le t]
      · linarith [le_abs_self t]
    · intro hz
      obtain ⟨n, t, ht, rfl⟩ := mem_iUnion.mp hz
      exact ⟨t, rfl⟩
  rw [hrange, iUnion_inter]
  exact measure_iUnion_null hω

end LatticeProb.LQG
