/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.FiniteUpperTail at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.FineTail
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.CoarseTight

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.QPos

theorem full_annulus_tail_le_coarse_add_fine
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    {ξ : ℝ} (hξ : 0 < ξ) {n : ℕ} (hn : 3 ≤ n)
    (M a : ℝ) :
    P {ω | Real.exp (ξ * M) * a <
      (crossLenIn ξ (fun x => phiMN W P 0 n x ω)
        upperAnnulus upperAnnulusInner upperAnnulusOuter).toReal} ≤
      P {ω | M < coarseCorridorSup P W ω} +
      P {ω | a ≤ T20B.mrectLen ξ (fun x => phiMN W P 3 n x ω)
        3 1 eastShift 3 1} := by
  have hae := ae_full_annulus_le_fine_of_coarse_bound hW hξ hn M
  have hsub : ∀ᵐ ω ∂P,
      ω ∈ {ω | Real.exp (ξ * M) * a <
        (crossLenIn ξ (fun x => phiMN W P 0 n x ω)
          upperAnnulus upperAnnulusInner upperAnnulusOuter).toReal} →
      ω ∈ {ω | M < coarseCorridorSup P W ω} ∪
        {ω | a ≤ T20B.mrectLen ξ (fun x => phiMN W P 3 n x ω)
          3 1 eastShift 3 1} := by
    filter_upwards [hae] with ω hcmp hbad
    by_cases hM : coarseCorridorSup P W ω ≤ M
    · right
      by_contra hfine
      have hgood : ∀ x ∈ eastCorridor.toSet, |phiMN W P 0 3 x ω| ≤ M := by
        intro x hx
        exact (coarseCorridorSup_bounds hW ω x hx).trans hM
      have hfull := hcmp hgood
      have hlt : T20B.mrectLen ξ (fun x => phiMN W P 3 n x ω)
          3 1 eastShift 3 1 < a := lt_of_not_ge hfine
      exact (not_le_of_gt hbad) (hfull.trans
        (mul_le_mul_of_nonneg_left hlt.le (Real.exp_pos _).le))
    · left
      exact lt_of_not_ge hM
  exact (measure_mono_ae hsub).trans (measure_union_le _ _)

end SupercriticalLQGUniqueness.B2.QPos
