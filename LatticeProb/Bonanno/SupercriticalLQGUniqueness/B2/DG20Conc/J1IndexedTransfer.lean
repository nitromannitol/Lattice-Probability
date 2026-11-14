/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1IndexedTransfer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBProbabilityTransfer

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

theorem j1_indexed_tail_transfer_of_ae_compare
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (J : Finset ι) (fineCross fullCross fineAround fullAround :
      ι → Ω → ℝ≥0∞) (Bad : Set Ω)
    (e tLow tHigh : ℝ≥0∞) (he0 : e ≠ 0) (heTop : e ≠ ∞)
    (hcmp : ∀ᵐ ω ∂P, ω ∉ Bad → ∀ i ∈ J,
      fineCross i ω ≤ e * fullCross i ω ∧
      fullAround i ω ≤ e * fineAround i ω) :
    P {ω | ∃ i ∈ J, fullCross i ω < tLow} ≤
      P {ω | ∃ i ∈ J, fineCross i ω < e * tLow} + P Bad ∧
    P {ω | ∃ i ∈ J, e * tHigh < fullAround i ω} ≤
      P {ω | ∃ i ∈ J, tHigh < fineAround i ω} + P Bad := by
  constructor
  · apply laneB_measure_le_of_ae_good_imp P _ _ Bad
    filter_upwards [hcmp] with ω hω
    rintro ⟨i, hi, hbad⟩ hnBad
    refine ⟨i, hi, ?_⟩
    exact (hω hnBad i hi).1.trans_lt
      (by simpa only [mul_comm] using
        ENNReal.mul_lt_mul_left he0 heTop hbad)
  · apply laneB_measure_le_of_ae_good_imp P _ _ Bad
    filter_upwards [hcmp] with ω hω
    rintro ⟨i, hi, hbad⟩ hnBad
    refine ⟨i, hi, ?_⟩
    exact (ENNReal.mul_lt_mul_iff_left he0 heTop).mp
      (by simpa only [mul_comm] using
        hbad.trans_le (hω hnBad i hi).2)

end SupercriticalLQGUniqueness.B2.DG20Conc
