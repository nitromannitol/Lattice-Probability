import LatticeProb.Prob.Percolation.GreenColumn

/-! # Harmonicity of differences of Green columns -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Classical

namespace LatticeProb.Percolation

noncomputable section

/-- The component Laplacian respects subtraction and annihilates constants. -/
theorem componentLaplacian_sub_sub_const {d : ℕ} {ω : Configuration d}
    (C : OpenComponent ω) (g h : C → ℝ) (c : ℝ) (v : C) :
    componentLaplacian C (fun z => g z - h z - c) v =
      componentLaplacian C g v - componentLaplacian C h v := by
  simp only [componentLaplacian, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  ring

/-- The difference of two Green columns, shifted by a constant, is harmonic away from both poles. -/
theorem greenColumn_sub_sub_const_harmonic {d : ℕ} (hd : 2 ≤ d) {ω : Configuration d}
    (C : OpenComponent ω) (p q : C) (g h : C → ℝ) (c : ℝ)
    (hg : IsGreenColumn d hd C p g) (hh : IsGreenColumn d hd C q h)
    (x : Vertex d) (R : ℝ) (hp : p ∉ componentEuclideanBall C x R)
    (hq : q ∉ componentEuclideanBall C x R) :
    ∀ v ∈ componentEuclideanBall C x R,
      componentLaplacian C (fun z => g z - h z - c) v = 0 := by
  intro v hv
  have hvp : v ≠ p := by
    intro e
    exact hp (e ▸ hv)
  have hvq : v ≠ q := by
    intro e
    exact hq (e ▸ hv)
  have hgv := hg.1 v
  have hhv := hh.1 v
  simp only [if_neg hvp] at hgv
  simp only [if_neg hvq] at hhv
  rw [componentLaplacian_sub_sub_const]
  linarith

end
end LatticeProb.Percolation
