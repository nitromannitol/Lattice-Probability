/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.CouplingCostTails at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.MedianTailWindow

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_coupling_cost_tails
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (Q : Measure E) (R : Measure (Ω × E))
    (hfst : R.map Prod.fst = P) (hsnd : R.map Prod.snd = Q)
    (A : Ω → ℝ≥0∞) (B : E → ℝ≥0∞)
    (hA : AEMeasurable A P) (hB : Measurable B)
    (C bLo bHi L H η : ℝ≥0∞)
    (hCL : C * L ≤ bLo) (hCH : C * bHi ≤ H)
    (hbad : R {p | ¬ (A p.1 ≤ C * B p.2 ∧
      B p.2 ≤ C * A p.1)} ≤ η)
    (hlo : Q {e | B e ≤ bLo} ≤ η)
    (hhi : Q {e | bHi < B e} ≤ η) :
    P {ω | A ω < L} ≤ η + η ∧
      P {ω | H < A ω} ≤ η + η := by
  have hloP : P {ω | A ω < L} = R {p | A p.1 < L} := by
    rw [← hfst]
    change (R.map Prod.fst) (A ⁻¹' Iio L) = R {p | A p.1 < L}
    rw [Measure.map_apply₀ measurable_fst.aemeasurable
      (by simpa only [hfst] using hA.nullMeasurable measurableSet_Iio)]
    rfl
  have hhiP : P {ω | H < A ω} = R {p | H < A p.1} := by
    rw [← hfst]
    change (R.map Prod.fst) (A ⁻¹' Ioi H) = R {p | H < A p.1}
    rw [Measure.map_apply₀ measurable_fst.aemeasurable
      (by simpa only [hfst] using hA.nullMeasurable measurableSet_Ioi)]
    rfl
  have hloQ : R {p | B p.2 ≤ bLo} = Q {e | B e ≤ bLo} := by
    rw [← hsnd]
    change R {p | B p.2 ≤ bLo} = (R.map Prod.snd) (B ⁻¹' Iic bLo)
    rw [Measure.map_apply measurable_snd (hB measurableSet_Iic)]
    rfl
  have hhiQ : R {p | bHi < B p.2} = Q {e | bHi < B e} := by
    rw [← hsnd]
    change R {p | bHi < B p.2} = (R.map Prod.snd) (B ⁻¹' Ioi bHi)
    rw [Measure.map_apply measurable_snd (hB measurableSet_Ioi)]
    rfl
  have hsubLo : {p : Ω × E | A p.1 < L} ⊆
      {p | ¬ (A p.1 ≤ C * B p.2 ∧ B p.2 ≤ C * A p.1)} ∪
      {p | B p.2 ≤ bLo} := by
    intro p hp
    by_cases hg : A p.1 ≤ C * B p.2 ∧ B p.2 ≤ C * A p.1
    · right
      exact hg.2.trans ((mul_le_mul_of_nonneg_left hp.le bot_le).trans hCL)
    · exact Or.inl hg
  have hsubHi : {p : Ω × E | H < A p.1} ⊆
      {p | ¬ (A p.1 ≤ C * B p.2 ∧ B p.2 ≤ C * A p.1)} ∪
      {p | bHi < B p.2} := by
    intro p hp
    by_cases hg : A p.1 ≤ C * B p.2 ∧ B p.2 ≤ C * A p.1
    · right
      by_contra h
      have hB : B p.2 ≤ bHi := le_of_not_gt h
      exact (not_le_of_gt hp) (hg.1.trans ((mul_le_mul_of_nonneg_left hB bot_le).trans hCH))
    · exact Or.inl hg
  constructor
  · rw [hloP]
    calc
      R {p | A p.1 < L} ≤ R ({p | ¬ (A p.1 ≤ C * B p.2 ∧
        B p.2 ≤ C * A p.1)} ∪ {p | B p.2 ≤ bLo}) := measure_mono hsubLo
      _ ≤ R {p | ¬ (A p.1 ≤ C * B p.2 ∧ B p.2 ≤ C * A p.1)} +
        R {p | B p.2 ≤ bLo} := measure_union_le _ _
      _ ≤ η + η := by rw [hloQ]; exact add_le_add hbad hlo
  · rw [hhiP]
    calc
      R {p | H < A p.1} ≤ R ({p | ¬ (A p.1 ≤ C * B p.2 ∧
        B p.2 ≤ C * A p.1)} ∪ {p | bHi < B p.2}) := measure_mono hsubHi
      _ ≤ R {p | ¬ (A p.1 ≤ C * B p.2 ∧ B p.2 ≤ C * A p.1)} +
        R {p | bHi < B p.2} := measure_union_le _ _
      _ ≤ η + η := by rw [hhiQ]; exact add_le_add hbad hhi

end SupercriticalLQGUniqueness.B2.DG20Pt
