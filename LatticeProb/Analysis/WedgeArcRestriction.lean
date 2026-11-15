import LatticeProb.Analysis.WedgeArcIntegral

/-! # Restriction of angular circle measure to a symmetric arc -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- Restricting the full angular measure to an open symmetric arc gives the
angular measure of that arc. This includes the circle with one point removed. -/
theorem wedgeArcMeasure_eq_restrict_full {θ : ℝ} (hθ' : θ ≤ 2 * Real.pi) :
    wedgeArcMeasure θ = (wedgeArcMeasure (2 * Real.pi)).restrict
      {z : ℂ | z.arg ∈ Ioo (-θ / 2) (θ / 2)} := by
  have harg : MeasurableSet {z : ℂ | z.arg ∈ Ioo (-θ / 2) (θ / 2)} :=
    Complex.measurable_arg measurableSet_Ioo
  have hpre : (circleMap 0 1) ⁻¹' {z : ℂ | z.arg ∈ Ioo (-θ / 2) (θ / 2)} ∩
      Ioc (-(2 * Real.pi) / 2) ((2 * Real.pi) / 2) = Ioo (-θ / 2) (θ / 2) := by
    ext x
    constructor
    · rintro ⟨hx, hfull⟩
      change (circleMap 0 1 x).arg ∈ Ioo (-θ / 2) (θ / 2) at hx
      rw [arg_circleMap_mem_wedge le_rfl hfull] at hx
      exact hx
    · intro hx
      have hfull : x ∈ Ioc (-(2 * Real.pi) / 2) ((2 * Real.pi) / 2) := by
        constructor <;> linarith [hx.1, hx.2]
      exact ⟨by simpa only [mem_preimage, mem_ofPred_eq,
        arg_circleMap_mem_wedge le_rfl hfull] using hx, hfull⟩
  unfold wedgeArcMeasure
  rw [Measure.restrict_map (by fun_prop) harg, Measure.restrict_restrict
    (harg.preimage (by fun_prop)), hpre, restrict_Ioo_eq_restrict_Ioc]

end LatticeProb
