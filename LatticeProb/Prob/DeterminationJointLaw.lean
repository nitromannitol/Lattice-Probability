import LatticeProb.Prob.AEDetermined
import Mathlib.Probability.IdentDistrib

/-! # Almost-sure determination and joint laws -/

open MeasureTheory ProbabilityTheory

namespace LatticeProb

/-- Almost-sure measurable determination is preserved by the joint law of the determining and
    determined variables. -/
theorem AEDeterminedBy.of_identDistrib_joint
    {Ω Ω' α β : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableEq β]
    {μ : Measure Ω} {ν : Measure Ω'} {X : Ω → α} {Y : Ω → β}
    {X' : Ω' → α} {Y' : Ω' → β}
    (h : IdentDistrib (fun ω => (X ω, Y ω)) (fun ω => (X' ω, Y' ω)) μ ν)
    (hdet : AEDeterminedBy Y X μ) : AEDeterminedBy Y' X' ν := by
  obtain ⟨F, hF, hF_eq⟩ := hdet
  refine ⟨F, hF, ?_⟩
  have hgraph : MeasurableSet {p : α × β | p.2 = F p.1} :=
    measurableSet_eq_fun measurable_snd (hF.comp measurable_fst)
  exact h.ae_snd hgraph hF_eq

end LatticeProb
