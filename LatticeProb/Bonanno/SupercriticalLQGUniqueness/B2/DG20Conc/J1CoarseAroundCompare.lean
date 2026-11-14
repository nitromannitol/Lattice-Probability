/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1CoarseAroundCompare at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBAroundCompare

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.WhiteNoise

theorem j1_aroundDist_le_of_field_bound
    (ξ : ℝ) {f g : ℂ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (U E F : Set ℂ) {a : ℝ}
    (hfg : ∀ z ∈ U, ξ * f z ≤ ξ * g z + a) :
    (lfppContMetric ξ f hf).aroundDist U E F ≤
      ENNReal.ofReal (Real.exp a) *
        (lfppContMetric ξ g hg).aroundDist U E F := by
  let e : ℝ≥0∞ := ENNReal.ofReal (Real.exp a)
  have he0 : e ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have heTop : e ≠ ⊤ := ENNReal.ofReal_ne_top
  have hbound : ∀ z ∈ U, ξ * (f z - g z) ≤ a := by
    intro z hz
    linarith [hfg z hz]
  unfold ContMetric.aroundDist
  rw [ENNReal.mul_iInf_of_ne he0 heTop]
  refine iInf_mono fun l => ?_
  rw [ENNReal.mul_iInf_of_ne he0 heTop]
  refine iInf_mono fun r => ?_
  rw [ENNReal.mul_iInf_of_ne he0 heTop]
  refine iInf_mono fun P => ?_
  rw [ENNReal.mul_iInf_of_ne he0 heTop]
  refine iInf_mono fun hlr => ?_
  rw [ENNReal.mul_iInf_of_ne he0 heTop]
  refine iInf_mono fun hP => ?_
  rw [ENNReal.mul_iInf_of_ne he0 heTop]
  refine iInf_mono fun hPU => ?_
  rw [ENNReal.mul_iInf_of_ne he0 heTop]
  refine iInf_mono fun _hsep => ?_
  let ψ : C(ℂ, ℝ) := ⟨fun z => f z - g z, hf.sub hg⟩
  have hW : ∀ x y : ℂ,
      ENNReal.ofReal ((lfppContMetric ξ f hf).1 (x, y)) =
        weylScale ξ ψ (lfppContMetric ξ g hg) x y := by
    intro x y
    rw [lfppContMetric_apply, ENNReal.ofReal_toReal (lfppD_ne_top hf x y)]
    convert lfppD_add_eq_weylScale hg ψ x y using 1
    congr 1
    funext z
    simp [ψ]
  exact curveLength_weyl_le (lfppContMetric ξ f hf) hW hlr
    ((lfppContMetric ξ g hg).continuous_pt.comp_continuousOn hP)
    (fun t ht => hPU ⟨t, ht, rfl⟩) (fun z hz => hbound z hz)

end SupercriticalLQGUniqueness.B2.DG20Conc
