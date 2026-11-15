import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.JointMeasurable
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.Window
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Measurable paths rooted at a first hit -/

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped Topology

namespace LatticeProb

/-- Express a complex path in Euclidean coordinates relative to a given point. -/
noncomputable def centeredEuclideanCurve (c : C(ℝ, ℂ)) (z : ℂ) :
    C(ℝ, EuclideanSpace ℝ (Fin 2)) :=
  ⟨fun t => Complex.orthonormalBasisOneI.repr (c t - z), by fun_prop⟩

/-- The Euclidean-coordinate curve, shifted to its first hit of `z` and centered at `z`. -/
noncomputable def firstHitCenteredCurve (c : C(ℝ, ℂ)) (z : ℂ) :
    C(ℝ, EuclideanSpace ℝ (Fin 2)) :=
  centeredEuclideanCurve
    (MatedCRTHarmonic.GMS4b.curveShift c (MatedCRTHarmonic.GMS4b.hitTime c z)) z

/-- The first-hit time is measurable jointly in a random continuous curve and a random point. -/
theorem measurable_firstHitTime {Ω : Type*} [MeasurableSpace Ω]
    {c : Ω → C(ℝ, ℂ)} {z : Ω → ℂ} (hc : Measurable c) (hz : Measurable z) :
    Measurable fun ω => MatedCRTHarmonic.GMS4b.hitTime (c ω) (z ω) :=
  MatedCRTHarmonic.GMS4b.measurable_hitTime.comp (hc.prodMk hz)

/-- The centered, first-hit shifted curve is jointly measurable in the curve and point. -/
theorem measurable_firstHitCenteredCurve :
    Measurable fun p : C(ℝ, ℂ) × ℂ => firstHitCenteredCurve p.1 p.2 := by
  have hcenter : Continuous (fun p : C(ℝ, ℂ) × ℂ => centeredEuclideanCurve p.1 p.2) := by
    refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
    exact Complex.orthonormalBasisOneI.repr.continuous.comp
      ((continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)).sub
        (continuous_snd.comp continuous_fst))
  have hshift : Measurable (fun p : C(ℝ, ℂ) × ℂ =>
      (MatedCRTHarmonic.GMS4b.curveShift p.1
        (MatedCRTHarmonic.GMS4b.hitTime p.1 p.2), p.2)) :=
    MatedCRTHarmonic.GMS4b.measurable_shiftAtHit.prodMk measurable_snd
  change Measurable ((fun p : C(ℝ, ℂ) × ℂ => centeredEuclideanCurve p.1 p.2) ∘
    (fun p : C(ℝ, ℂ) × ℂ => (MatedCRTHarmonic.GMS4b.curveShift p.1
      (MatedCRTHarmonic.GMS4b.hitTime p.1 p.2), p.2)))
  exact hcenter.measurable.comp hshift

/-- A proper curve rooted at a point it visits starts at zero after centering. -/
theorem firstHitCenteredCurve_zero {c : C(ℝ, ℂ)} {z : ℂ}
    (hproper : Tendsto c (cocompact ℝ) (cocompact ℂ)) (hz : z ∈ range c) :
    firstHitCenteredCurve c z 0 = 0 := by
  change Complex.orthonormalBasisOneI.repr
    (c (MatedCRTHarmonic.GMS4b.hitTime c z + 0) - z) = 0
  rw [add_zero, MatedCRTHarmonic.GMS4b.hitTime_spec c.continuous hproper hz, sub_self, map_zero]

end LatticeProb
