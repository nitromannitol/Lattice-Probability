/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.ConeScaling.AreaScalingHolds at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeScaling.AreaScaling
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.Main

/-!
# `AreaScalingLaw` unconditionally

The named input `ConeAreaRandomDilation D` of `areaScalingLaw_of_randomDilation` is the instance
`A = B_1(0)`, `R = R_b` simultaneous coordinate change
`LQGCoord.ae_lqgArea_coneRescaleField_holds` ([SW] Thm 1.1/1.4). Hence the
`AreaScalingLaw D` holds for every cone realization `D` (`areaScalingLaw_holds`). This file is kept
separate so that the conditional theorem does not depend on the coordinate-covariance modules.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace MatedCRTHarmonic.ConeScaling

open MatedCRTHarmonic.CellScaling

/-- `(R ·) '' B_1(0) = B_R(0)` for `R > 0`. -/
lemma image_mul_ball_one {R : ℝ} (hR : 0 < R) :
    (fun z : ℂ => (R : ℂ) * z) '' ball 0 1 = ball 0 R := by
  ext z
  simp only [mem_image, mem_ball, dist_zero_right]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    exact mul_lt_of_lt_one_right hR hw
  · intro hz
    refine ⟨z / (R : ℂ), ?_, ?_⟩
    · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, div_lt_one hR]
      exact hz
    · have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
      rw [mul_div_cancel₀ z hR']

/-- The random-dilation covariance at the cone scale holds. -/
theorem coneAreaRandomDilation_holds {γ : ℝ} {M : MesoModel.MatedCRTUnitMesoModel γ}
    (D : ConeRealization M) : ConeAreaRandomDilation D := by
  intro b hb
  filter_upwards [LQGCoord.ae_lqgArea_coneRescaleField_holds M.hγ.1 M.hγ.2 D.gff D.brownian
    D.brownian'] with ω h
  have hR : 0 < D.scale b ω := Real.exp_pos _
  rw [show D.field ω = coneFieldOf γ (D.X ω) (fun t => D.B t ω) (fun t => D.B' t ω) from rfl,
    h (D.scale b ω) hR b hb (ball 0 1), image_mul_ball_one hR]
  rfl

/-- **`AreaScalingLaw` holds** for every cone realization of the unit-mesh model (the SLE-free
input; DMS Prop 4.13(i) + [SW]). -/
theorem areaScalingLaw_holds {γ : ℝ} {M : MesoModel.MatedCRTUnitMesoModel γ}
    (D : ConeRealization M) : AreaScalingLaw D :=
  areaScalingLaw_of_randomDilation D (coneAreaRandomDilation_holds D)

end MatedCRTHarmonic.ConeScaling
