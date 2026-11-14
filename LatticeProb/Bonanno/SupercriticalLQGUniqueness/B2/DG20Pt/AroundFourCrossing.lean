/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.AroundFourCrossing at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.AroundFourPath
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistCrossingPath

 




set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 


theorem around_loop_of_four_crossLen
    (A : EuclideanAnnulus) (ξ : ℝ) (φ : ℂ → ℝ)
    (a₀ a₁ a₂ a₃ L : ℝ≥0∞)
    (h₀ : crossLenIn ξ φ (Strong.cfgOpens A 0 : Set ℂ)
      (Strong.cfgSet₁ A 0) (Strong.cfgSet₂ A 0) < a₀)
    (h₁ : crossLenIn ξ φ (Strong.cfgOpens A 1 : Set ℂ)
      (Strong.cfgSet₁ A 1) (Strong.cfgSet₂ A 1) < a₁)
    (h₂ : crossLenIn ξ φ (Strong.cfgOpens A 2 : Set ℂ)
      (Strong.cfgSet₁ A 2) (Strong.cfgSet₂ A 2) < a₂)
    (h₃ : crossLenIn ξ φ (Strong.cfgOpens A 3 : Set ℂ)
      (Strong.cfgSet₁ A 3) (Strong.cfgSet₂ A 3) < a₃)
    (hbudget : a₀ + a₁ + a₂ + a₃ < L) :
    ∃ (γ : ℝ → ℂ) (a b : ℂ), IsPiecewiseC1Path γ a b ∧
      (∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ A.toSet) ∧
      LQGMetric.Disconnects (γ '' Icc (0 : ℝ) 1)
        A.innerBoundary A.outerBoundary ∧
      lfppLen ξ φ γ < L := by
  obtain ⟨f₀, hf₀, hc₀⟩ := exists_crossing_of_crossLenIn_lt h₀
  obtain ⟨f₁, hf₁, hc₁⟩ := exists_crossing_of_crossLenIn_lt h₁
  obtain ⟨f₂, hf₂, hc₂⟩ := exists_crossing_of_crossLenIn_lt h₂
  obtain ⟨f₃, hf₃, hc₃⟩ := exists_crossing_of_crossLenIn_lt h₃
  apply around_loop_of_four_admPaths A ξ φ f₀ f₁ f₂ f₃ L hf₀ hf₁ hf₂ hf₃
  exact (add_le_add (add_le_add (add_le_add hc₀.le hc₁.le) hc₂.le) hc₃.le).trans_lt
    hbudget

end SupercriticalLQGUniqueness.B2.DG20Pt
