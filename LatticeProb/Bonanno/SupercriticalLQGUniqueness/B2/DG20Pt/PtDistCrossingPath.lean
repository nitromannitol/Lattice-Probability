/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistCrossingPath at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenBasic

 





set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 


theorem exists_crossing_of_crossLenIn_lt {ξ : ℝ} {f : ℂ → ℝ}
    {U A B : Set ℂ} {C : ℝ≥0∞}
    (h : crossLenIn ξ f U A B < C) :
    ∃ γ : ℝ → ℂ, AdmPath U A B γ ∧ lfppLen ξ f γ < C := by
  rw [crossLenIn_eq_biInf] at h
  simp only [iInf_lt_iff] at h
  obtain ⟨γ, hγ, hγC⟩ := h
  exact ⟨γ, hγ, hγC⟩

end SupercriticalLQGUniqueness.B2.DG20Pt
