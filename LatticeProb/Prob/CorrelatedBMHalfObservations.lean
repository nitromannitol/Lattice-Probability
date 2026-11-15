import LatticeProb.Prob.CorrelatedBMSeparatedHalves
import LatticeProb.Prob.AEDetermined

/-! # Independent observations of correlated Brownian half-paths -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace LatticeProb.CorrelatedBM

open MatedCRTHarmonic.MatedCRT

/-- Observations almost surely determined by opposite centered half-paths are independent. -/
theorem indepFun_of_aeDeterminedBy_opposite_halves
    {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    {d : ℝ} (hd : |d| = 1) (c : ℝ)
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {Y : Path2 → α} {W : Path2 → β}
    (hY : AEDeterminedBy Y
      (fun ω (p : Fin 2 × ℝ≥0) => coneIncr p.1 (c + -d * (p.2 : ℝ)) c ω) μ)
    (hW : AEDeterminedBy W
      (fun ω (p : Fin 2 × ℝ≥0) => coneIncr p.1 (c + d * (p.2 : ℝ)) c ω) μ) :
    IndepFun Y W μ := by
  obtain ⟨F, hF, hY⟩ := hY
  obtain ⟨G, hG, hW⟩ := hW
  exact ((indepFun_centered_opposite_halves hμ hd c).comp hF hG).congr hY.symm hW.symm

end LatticeProb.CorrelatedBM
