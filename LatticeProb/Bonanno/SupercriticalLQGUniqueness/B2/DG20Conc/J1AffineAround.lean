/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1AffineAround at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1AffineAroundLen
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.AnnularRecursion.Families

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.LFPP LQGMetric.MetricGeometry
open SupercriticalLQGUniqueness.Exponent.AnnularRecursion

theorem j1_aroundDist_image_affine_le (ξ : ℝ) (g : ℂ → ℝ)
    (hg : Continuous g) (U E F : Set ℂ) {r : ℝ} (hr : 0 < r) (c : ℂ) :
    (lfppContMetric ξ g hg).aroundDist
      ((fun z => c + (r : ℂ) * z) '' U)
      ((fun z => c + (r : ℂ) * z) '' E)
      ((fun z => c + (r : ℂ) * z) '' F) ≤
      ENNReal.ofReal r *
        (lfppContMetric ξ (fun z => g (c + (r : ℂ) * z))
          (hg.comp (by fun_prop : Continuous
            (fun z : ℂ => c + (r : ℂ) * z)))).aroundDist U E F := by
  let h0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.mpr hr).ne'
  let htop : ENNReal.ofReal r ≠ ∞ := ENNReal.ofReal_ne_top
  unfold ContMetric.aroundDist
  rw [ENNReal.mul_iInf_of_ne h0 htop]
  refine le_iInf fun a => ?_
  rw [ENNReal.mul_iInf_of_ne h0 htop]
  refine le_iInf fun b => ?_
  rw [ENNReal.mul_iInf_of_ne h0 htop]
  refine le_iInf fun P => ?_
  rw [ENNReal.mul_iInf_of_ne h0 htop]
  refine le_iInf fun hab => ?_
  rw [ENNReal.mul_iInf_of_ne h0 htop]
  refine le_iInf fun hcont => ?_
  rw [ENNReal.mul_iInf_of_ne h0 htop]
  refine le_iInf fun hcar => ?_
  rw [ENNReal.mul_iInf_of_ne h0 htop]
  refine le_iInf fun hsep => ?_
  let Q : ℝ → ℂ := fun t => c + (r : ℂ) * P t
  have hqc : ContinuousOn Q (Set.Icc a b) :=
    (by fun_prop : Continuous (fun z : ℂ => c + (r : ℂ) * z)).comp_continuousOn hcont
  have hqcar : Q '' Set.Icc a b ⊆
      (fun z => c + (r : ℂ) * z) '' U := by
    simpa only [Q, ← Set.image_image, Function.comp_def] using
      (Set.image_mono hcar :
        (fun z => c + (r : ℂ) * z) '' (P '' Set.Icc a b) ⊆ _)
  have hqsep : LQGMetric.Disconnects (Q '' Set.Icc a b)
      ((fun z => c + (r : ℂ) * z) '' E)
      ((fun z => c + (r : ℂ) * z) '' F) := by
    have hh := disconnects_affine (r : ℂ) c
      (Complex.ofReal_ne_zero.mpr hr.ne') hsep
    simpa only [Q, ← Set.image_image, Function.comp_def, add_comm] using hh
  have hle : (lfppContMetric ξ g hg).aroundDist
      ((fun z => c + (r : ℂ) * z) '' U)
      ((fun z => c + (r : ℂ) * z) '' E)
      ((fun z => c + (r : ℂ) * z) '' F) ≤
      (lfppContMetric ξ g hg).len Q a b := by
    unfold ContMetric.aroundDist
    exact iInf_le_of_le a (iInf_le_of_le b
      (iInf_le_of_le Q (iInf_le_of_le hab
        (iInf_le_of_le hqc (iInf_le_of_le hqcar
          (iInf_le_of_le hqsep le_rfl))))))
  exact hle.trans_eq (j1_lfpp_len_image_affine ξ g hg hr c P a b)

end SupercriticalLQGUniqueness.B2.DG20Conc
