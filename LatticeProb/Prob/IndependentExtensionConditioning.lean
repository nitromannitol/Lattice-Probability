import LatticeProb.Prob.EfronSteinSigma
import LatticeProb.Prob.CondIndepEvChain

/-! # Conditioning and independent extensions -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory MeasurableSpace

namespace LatticeProb

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Adding the conditioning information to an independent extension leaves it
conditionally independent of the original σ-algebra. -/
theorem condIndepEv_sup_of_indep [IsProbabilityMeasure μ]
    {G H B : MeasurableSpace Ω} (hGH : G ≤ H) (hH : H ≤ mΩ) (hB : B ≤ mΩ)
    (h : Indep H B μ) : CondIndepEv G H (B ⊔ G) μ := by
  refine condIndepEv_of_condExp_sup_eq (hGH.trans hH) hH (sup_le hB (hGH.trans hH)) ?_
  intro a ha
  have hi : Integrable (a.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator (hH a ha)
  have hm : StronglyMeasurable[H] (a.indicator (fun _ => (1 : ℝ))) :=
    stronglyMeasurable_const.indicator ha
  simpa only [sup_assoc, sup_idem] using
    (condExp_sup_indep_eq hGH hH hB h.symm hm hi)

end LatticeProb
