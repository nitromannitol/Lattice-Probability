/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.DGFFDistanceMeasurable at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.DGFFDistance
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

 

set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.QPos

theorem measurable_dgffPathCost (n : ℕ) (ξ : ℝ) (p : List (DGFFSite n)) :
    Measurable (fun h : EuclideanSpace ℝ (DGFFSite n) => dgffPathCost n ξ h p) := by
  induction p with
  | nil => simp [dgffPathCost, inclusivePathCost]
  | cons z zs ih =>
      have hz : Measurable (fun h : EuclideanSpace ℝ (DGFFSite n) =>
          Real.exp (ξ * h z)) := by
        exact ((PiLp.continuous_apply (p := 2)
          (β := fun _ : DGFFSite n => ℝ) z).measurable.const_mul ξ).exp
      convert hz.add ih using 1
      ext h
      simp [dgffPathCost, inclusivePathCost]

theorem measurable_dgffAnnulusDistance (n : ℕ) (ξ : ℝ) :
    Measurable (dgffAnnulusDistance n ξ) := by
  unfold dgffAnnulusDistance
  exact Measurable.iInf (fun p : {p : List (DGFFSite n) // IsDGFFAnnulusPath n p} =>
    measurable_dgffPathCost n ξ p.1)

end SupercriticalLQGUniqueness.B2.QPos
