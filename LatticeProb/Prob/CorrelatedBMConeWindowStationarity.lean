import LatticeProb.Prob.CorrelatedBMRecenter
import LatticeProb.Prob.ConeWindowShiftLaw
import LatticeProb.Bonanno.MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2Unique

/-! # Stationarity of correlated Brownian cone-window coverage -/

set_option autoImplicit false

open MeasureTheory Set
open MatedCRTHarmonic.MatedCRT

namespace LatticeProb.CorrelatedBM

/-- The two real coordinate paths of a continuous pair-valued path. -/
def coordinatePaths (z : Path2) : C(ℝ, ℝ) × C(ℝ, ℝ) :=
  (⟨fun t => (z t).1, by fun_prop⟩, ⟨fun t => (z t).2, by fun_prop⟩)

/-- Coordinate paths vary continuously in the compact-open topology. -/
theorem continuous_coordinatePaths : Continuous coordinatePaths := by
  apply Continuous.prodMk
  · refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
    show Continuous (fun p : Path2 × ℝ => (p.1 p.2).1)
    fun_prop
  · refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
    show Continuous (fun p : Path2 × ℝ => (p.1 p.2).2)
    fun_prop

/-- A centered time shift preserves the joint law of the coordinate paths. -/
theorem map_coordinatePaths_recenter_eq {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) (d : ℝ) :
    μ.map (fun z => coordinatePaths (recenterPath d 1 z)) = μ.map coordinatePaths := by
  change μ.map (coordinatePaths ∘ recenterPath d 1) = μ.map coordinatePaths
  rw [← Measure.map_map continuous_coordinatePaths.measurable
    (continuous_recenterPath d 1).measurable]
  rw [MatedCRTHarmonic.isCorrelatedBM2_unique_holds γ _ _
    (isCorrelatedBM2_map_recenterPath hμ d 1 (by norm_num)) hμ]

/-- Almost-every-time cone-window coverage for a correlated Brownian pair
implies coverage at any fixed interior time. -/
theorem ae_coneWindowCoverage_fixedTime_of_correlatedBM
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (B : Ω → Path2) (hB : Measurable B) {γ : ℝ}
    (hLaw : IsCorrelatedBM2 γ (P.map B))
    (hcoverage : ∀ l r : ℝ, l < r → ∀ᵐ ω ∂P,
      ∀ᵐ t ∂volume.restrict (Ioo l r),
        (coordinatePaths (B ω), t) ∈ Prod.fst '' coneWindowWitness l r)
    {a u b : ℝ} (hau : a < u) (hub : u < b) :
    ∀ᵐ ω ∂P, (coordinatePaths (B ω), u) ∈ Prod.fst '' coneWindowWitness a b := by
  let : IsProbabilityMeasure P := (Measure.isProbabilityMeasure_map_iff hB.aemeasurable).mp hLaw.isProbabilityMeasure
  let Z := fun ω => coordinatePaths (B ω)
  let Y := fun d ω => coordinatePaths (recenterPath d 1 (B ω))
  have hZ : Measurable Z := continuous_coordinatePaths.measurable.comp hB
  have hY (d : ℝ) : Measurable (Y d) :=
    continuous_coordinatePaths.measurable.comp ((continuous_recenterPath d 1).measurable.comp hB)
  have hlaw (d : ℝ) : P.map (Y d) = P.map Z := by
    change P.map ((coordinatePaths ∘ recenterPath d 1) ∘ B) = P.map (coordinatePaths ∘ B)
    rw [← Measure.map_map (continuous_coordinatePaths.measurable.comp
      (continuous_recenterPath d 1).measurable) hB, ← Measure.map_map continuous_coordinatePaths.measurable hB]
    exact map_coordinatePaths_recenter_eq hLaw d
  apply ae_coneWindowCoverage_fixedTime_of_shift_law P Z hZ Y hY hlaw
  · intro d
    filter_upwards with ω
    refine ⟨(B ω d).1, (B ω d).2, ?_, ?_⟩ <;> intro s <;>
      simp [Z, Y, coordinatePaths, recenterPath, add_comm]
  · exact hcoverage
  · exact hau
  · exact hub

end LatticeProb.CorrelatedBM
