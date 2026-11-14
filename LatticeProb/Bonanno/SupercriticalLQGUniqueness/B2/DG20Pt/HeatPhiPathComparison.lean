/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatPhiPathComparison at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenBasic

 


set_option autoImplicit false
noncomputable section

open Set LQGMetric LQGMetric.DDDF
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 




theorem dg20_heat_phi_lfppLen_compare_on_compact
    (ξ : ℝ) (X Φ : ℂ → ℝ) (K : Set ℂ) (γ : ℝ → ℂ) (a : ℝ)
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ K)
    (hcomp : ∀ z ∈ K, |X z - Φ z| ≤ a) :
    lfppLen ξ X γ ≤ ENNReal.ofReal (Real.exp (|ξ| * a)) * lfppLen ξ Φ γ ∧
    lfppLen ξ Φ γ ≤ ENNReal.ofReal (Real.exp (|ξ| * a)) * lfppLen ξ X γ := by
  constructor
  · exact lfppLen_le_of_abs_sub_le (fun t ht => hcomp _ (hγ t ht))
  · exact lfppLen_le_of_abs_sub_le (fun t ht => by
      rw [abs_sub_comm]
      exact hcomp _ (hγ t ht))

end SupercriticalLQGUniqueness.B2.DG20Pt
