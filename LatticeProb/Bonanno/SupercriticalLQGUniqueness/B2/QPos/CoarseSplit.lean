/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.CoarseSplit at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.CorridorScaling
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Step2

 

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.QPos

 

theorem ae_full_annulus_le_fine_of_coarse_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    {ξ : ℝ} (hξ : 0 < ξ) {n : ℕ} (hn : 3 ≤ n) (M : ℝ) :
    ∀ᵐ ω ∂P,
      (∀ x ∈ eastCorridor.toSet, |phiMN W P 0 3 x ω| ≤ M) →
        (crossLenIn ξ (fun x => phiMN W P 0 n x ω)
          upperAnnulus upperAnnulusInner upperAnnulusOuter).toReal ≤
        Real.exp (ξ * M) *
          T20B.mrectLen ξ (fun x => phiMN W P 3 n x ω) 3 1 eastShift 3 1 := by
  have hfull := isPhiVersion_phiMN hW (Nat.zero_le n)
  have hfine := isPhiVersion_phiMN hW hn
  filter_upwards [ae_phiMN_add hW hn] with ω hadd hM
  apply upperAnnulus_crossReal_le_of_field_cmp ξ (hfull.cont ω) (hfine.cont ω)
  intro x hx
  rw [hadd x]
  have hcoarse := (abs_le.mp (hM x hx)).2
  nlinarith [mul_nonneg hξ.le (sub_nonneg.mpr hcoarse)]

end SupercriticalLQGUniqueness.B2.QPos
