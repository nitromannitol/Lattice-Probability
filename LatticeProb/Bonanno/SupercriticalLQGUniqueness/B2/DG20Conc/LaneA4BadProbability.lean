/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4BadProbability at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4BadMax
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCCondKernelMean

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 

theorem laneA4_conditional_bad_probability
    {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hm : m ≤ mΩ) (E : Set Ω) (hE : MeasurableSet E) :
    let q : Ω → ℝ≥0∞ := fun ω => (condExpKernel P m ω) Eᶜ
    Measurable q ∧ (∀ ω, q ω ≤ 1) ∧
      (∫⁻ ω, q ω ∂P) = P Eᶜ := by
  let κ := condExpKernel P m
  let q : Ω → ℝ≥0∞ := fun ω => (κ ω) Eᶜ
  have hq : Measurable[m] q := Kernel.measurable_coe κ hE.compl
  have hqM : Measurable q := hq.mono hm le_rfl
  have hq1 : ∀ ω, q ω ≤ 1 := by
    intro ω
    exact (measure_mono (Set.subset_univ Eᶜ)).trans_eq (by simp)
  have hmean : (∫⁻ ω, q ω ∂P) = P Eᶜ := by
    calc
      (∫⁻ ω, q ω ∂P) = ∫⁻ ω, q ω ∂(P.trim hm) :=
        (lintegral_trim hm hq).symm
      _ = (κ ∘ₘ P.trim hm) Eᶜ := by
        exact (Measure.bind_apply hE.compl (Kernel.aemeasurable κ)).symm
      _ = P Eᶜ := by
        rw [show κ ∘ₘ P.trim hm = P from condExpKernel_comp_trim hm]
  exact ⟨hqM, hq1, hmean⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
