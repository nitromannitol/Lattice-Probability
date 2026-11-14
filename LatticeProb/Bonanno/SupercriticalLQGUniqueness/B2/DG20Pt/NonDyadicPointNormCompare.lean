/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicPointNormCompare at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistProbTransfer

 

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_point_norm_compare_of_high_band
    (lam C r : ℝ) (hlam : 0 < lam) (hC : 0 ≤ C)
    (hr1 : 1 ≤ r) (hr2 : r ≤ 2)
    (F H D : ℝ≥0∞)
    (hFH : F ≤ ENNReal.ofReal C * H)
    (hHF : H ≤ ENNReal.ofReal C * F)
    (hD : D = ENNReal.ofReal r * H) :
    ENNReal.ofReal lam⁻¹ * F ≤
        ENNReal.ofReal (2 * C) * (ENNReal.ofReal lam⁻¹ * D) ∧
      ENNReal.ofReal lam⁻¹ * D ≤
        ENNReal.ofReal (2 * C) * (ENNReal.ofReal lam⁻¹ * F) := by
  have hr0 : 0 ≤ r := by linarith
  have hOne : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr1
  have hTwo : ENNReal.ofReal r ≤ (2 : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_ofNat]
    exact ENNReal.ofReal_le_ofReal hr2
  have hC2 : ENNReal.ofReal C ≤ ENNReal.ofReal (2 * C) := by
    apply ENNReal.ofReal_le_ofReal
    nlinarith
  have hprod : ENNReal.ofReal (2 * C) =
      (2 : ℝ≥0∞) * ENNReal.ofReal C := by
    rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num)]
  have hHD : H ≤ D := by
    rw [hD]
    calc H = 1 * H := (one_mul H).symm
      _ ≤ ENNReal.ofReal r * H := by gcongr
  have hFD : F ≤ ENNReal.ofReal (2 * C) * D := by
    calc F ≤ ENNReal.ofReal C * H := hFH
      _ ≤ ENNReal.ofReal C * D := by gcongr
      _ ≤ ENNReal.ofReal (2 * C) * D := by gcongr
  have hDF : D ≤ ENNReal.ofReal (2 * C) * F := by
    rw [hD, hprod]
    calc ENNReal.ofReal r * H ≤ 2 * H := by gcongr
      _ ≤ 2 * (ENNReal.ofReal C * F) := by gcongr
      _ = 2 * ENNReal.ofReal C * F := by ac_rfl
  constructor
  · calc
      ENNReal.ofReal lam⁻¹ * F ≤
          ENNReal.ofReal lam⁻¹ *
            (ENNReal.ofReal (2 * C) * D) :=
          by gcongr
      _ = ENNReal.ofReal (2 * C) *
          (ENNReal.ofReal lam⁻¹ * D) := by ac_rfl
  · calc
      ENNReal.ofReal lam⁻¹ * D ≤
          ENNReal.ofReal lam⁻¹ *
            (ENNReal.ofReal (2 * C) * F) :=
          by gcongr
      _ = ENNReal.ofReal (2 * C) *
          (ENNReal.ofReal lam⁻¹ * F) := by ac_rfl

end SupercriticalLQGUniqueness.B2.DG20Pt
