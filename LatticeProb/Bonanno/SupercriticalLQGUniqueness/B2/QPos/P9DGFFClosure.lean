/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P9DGFFClosure at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.InputsDGFF
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.VaryingContradiction

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.QPos

theorem dgff_exponent_positive_of_upper_window
    (hlower : Inputs.DGFFInductionLowerWindow)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (hupper : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => boxDGFF n
        {h | dgffAnnulusDistance n (ξ : ℝ) h ≤
          (2 : ℝ) ^ (((ξ : ℝ) * Q + ε) * (n : ℝ))})
        atTop (𝓝 1)) :
    0 < Q := by
  obtain ⟨K, hK, hlo⟩ := hlower ξ
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hlo' : ∀ᶠ n : ℕ in atTop,
      (1 / 2 : ℝ≥0∞) ≤ boxDGFF n
        {h | (2 : ℝ) ^ ((1 / (K : ℝ)) * (n : ℝ)) ≤
          dgffAnnulusDistance n (ξ : ℝ) h} := by
    filter_upwards [eventually_ge_atTop (K + 3)] with n hn
    have heq : (1 / (K : ℝ)) * (n : ℝ) = (n : ℝ) / (K : ℝ) := by ring
    simpa only [heq] using hlo n hn
  exact exponent_positive_varying_laws
    (fun n => EuclideanSpace ℝ (DGFFSite n))
    (fun n => boxDGFF n) (fun n => inferInstance)
    (fun n => dgffAnnulusDistance n (ξ : ℝ))
    (fun n => measurable_dgffAnnulusDistance n (ξ : ℝ))
    (ξ : ℝ) Q (1 / (K : ℝ)) ξ.property (one_div_pos.mpr hKpos)
    hlo' hupper

end SupercriticalLQGUniqueness.B2.QPos
