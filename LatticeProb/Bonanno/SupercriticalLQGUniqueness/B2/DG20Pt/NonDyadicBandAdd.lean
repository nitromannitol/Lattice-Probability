/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicBandAdd at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistScaleArithmetic
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Sup
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseVersion

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 

theorem dg20_phi_real_band_add_ae
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (n : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    ∀ᵐ ω ∂P, ∀ x : ℂ,
      phiVer W P ((2 : ℝ) ^ (-((n : ℝ) + s))) 1 x ω =
        phiVer W P ((2 : ℝ) ^ (-((n : ℝ) + s)))
          ((2 : ℝ) ^ (-s)) x ω +
        phiVer W P ((2 : ℝ) ^ (-s)) 1 x ω := by
  have ha : 0 < (2 : ℝ) ^ (-((n : ℝ) + s)) := by positivity
  have hab : (2 : ℝ) ^ (-((n : ℝ) + s)) ≤ (2 : ℝ) ^ (-s) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hbc : (2 : ℝ) ^ (-s) ≤ 1 := by
    simpa only [Real.rpow_zero] using
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by linarith : -s ≤ 0))
  have hHi := isPhiVersion_phiVer hW ha hab
  have hLo := isPhiVersion_phiVer hW (by positivity : 0 < (2 : ℝ) ^ (-s)) hbc
  have hFull := isPhiVersion_phiVer hW ha (hab.trans hbc)
  exact phi_version_add_ae hW ha hab hbc hHi.cont hLo.cont hFull.cont
    hHi.ae_eq hLo.ae_eq hFull.ae_eq

 

end SupercriticalLQGUniqueness.B2.DG20Pt
