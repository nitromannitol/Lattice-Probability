import LatticeProb.LQG.WholePlaneCurveNull
import LatticeProb.LQG.LQGMeasureNonatomicUpper

/-! # Independent curve traces and logarithmically inserted quantum area -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Metric
open LatticeProb.Gauss LatticeProb.LQG.LQGMeasureNonatomicMass
open scoped ENNReal

namespace LatticeProb.LQG

/-- A Lebesgue-null compact-time trace independent of the uninserted area has
zero inserted quantum area in the unit disk. -/
theorem ae_inserted_lqgMeasure_trace_inter_unitBall_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ α : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hα : α < lqgQ γ) {μ μ₀ : Ω → Measure ℂ}
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hμ₀ : IsLQGMeasureOfField P γ 0 hcirc μ₀)
    (hμ₀m : AEMeasurable μ₀ P) {g : Ω → C(ℝ, ℂ)} (hgm : Measurable g)
    (hind : IndepFun g μ₀ P) {T : Set ℝ} (hT : IsCompact T)
    (hnull : ∀ᵐ ω ∂P, volume (g ω '' T) = 0) :
    ∀ᵐ ω ∂P, μ ω ((g ω '' T) ∩ ball (0 : ℂ) 1) = 0 := by
  have hμ₀' : IsLQGMeasure P γ hcirc μ₀ := by
    simpa only [IsLQGMeasureOfField, fieldCircleAverage_zero_lp] using hμ₀
  have htrace := hh.ae_lqgMeasure_trace_inter_unitBall_eq_zero hγ0 hγ2 hμ₀' hμ₀m hgm hind hT hnull
  have hweight := singularWeightStep_lp γ α hγ0 hγ2 hα Ω P hC hcirc μ μ₀ hh hμ hμ₀
  have hno := LQGMeasureNonatomicUpper.lqgMeasureNonatomicLP_holds P γ α hC hcirc
    hh hγ0 hγ2 hα μ hμ
  filter_upwards [htrace, hweight, hno] with ω htraceω hweightω hnoω
  let A := (g ω '' T) ∩ ball (0 : ℂ) 1
  have hA : MeasurableSet A := ((hT.image (g ω).continuous).isClosed.measurableSet).inter isOpen_ball.measurableSet
  have hp : μ ω (A ∩ ({0} : Set ℂ)ᶜ) = 0 := by
    have heq := congrArg (fun ν : Measure ℂ => ν A) hweightω
    rw [Measure.restrict_apply hA, Measure.restrict_apply hA] at heq
    rw [heq]
    exact (withDensity_absolutelyContinuous (μ₀ ω) _) (measure_mono_null inter_subset_left htraceω)
  have hz : μ ω ({0} : Set ℂ) = 0 := hnoω 0
  have hsub : A ⊆ (A ∩ ({0} : Set ℂ)ᶜ) ∪ {0} := by
    intro z hz'
    by_cases hz0 : z = 0
    · exact Or.inr (by simpa using hz0)
    · exact Or.inl ⟨hz', by simpa using hz0⟩
  exact measure_mono_null hsub (measure_union_null hp hz)

end LatticeProb.LQG
