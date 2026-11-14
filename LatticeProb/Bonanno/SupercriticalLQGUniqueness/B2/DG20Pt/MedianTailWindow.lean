/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.MedianTailWindow at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatPhiSquareCrossing

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_median_between_strict_half_tails
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : Ω → ℝ≥0∞) (m L H : ℝ≥0∞)
    (hm : IsMedian P Y m)
    (hlo : P {ω | Y ω < L} < 2⁻¹)
    (hhi : P {ω | H < Y ω} < 2⁻¹) :
    L ≤ m ∧ m ≤ H := by
  constructor
  · by_contra h
    have hml : m < L := lt_of_not_ge h
    have hsub : {ω | Y ω ≤ m} ⊆ {ω | Y ω < L} := by
      intro ω hω
      exact hω.trans_lt hml
    exact (not_lt_of_ge (hm.2.1.trans (measure_mono hsub))) hlo
  · by_contra h
    have hmh : H < m := lt_of_not_ge h
    have hsub : {ω | m ≤ Y ω} ⊆ {ω | H < Y ω} := by
      intro ω hω
      exact hmh.trans_le hω
    exact (not_lt_of_ge (hm.2.2.trans (measure_mono hsub))) hhi

end SupercriticalLQGUniqueness.B2.DG20Pt
