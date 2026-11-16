import LatticeProb.Analysis.Schauder.IBPTwice
import LatticeProb.Analysis.Schauder.KernelL1
import LatticeProb.Analysis.Schauder.KernelIntegral

/-!
# The second derivatives of the heat kernel have mean zero

Constants have bounded derivatives of every order. Applying the twice-integrated-by-parts
identity of `IBPTwice` to the constant function `1` against the heat kernel `p_t` gives
`∫ ∂_a ∂_b p_t = ∫ p_t · ∂_b ∂_a 1 = 0`, since every derivative of a constant vanishes.
-/

namespace LatticeProb.Analysis.Schauder

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- A constant function has bounded derivatives of every order. -/
theorem boundedDerivs_const (n : ℕ) (c : ℝ) : BoundedDerivs n (fun _ : Euc d => c) := by
  refine ⟨contDiff_const, fun k _ => ⟨|c|, fun y => ?_⟩⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [norm_iteratedFDeriv_zero]
    exact le_of_eq (Real.norm_eq_abs c)
  · rw [iteratedFDeriv_const_of_ne hk.ne']
    simp

/-- The second derivatives of the heat kernel have integral zero. -/
theorem integral_dirDeriv_dirDeriv_heatKernel {t : ℝ} (ht : 0 < t) (a b : Euc d) :
    ∫ y, dirDeriv a (dirDeriv b (heatKernel d t)) y = 0 := by
  have h := integral_mul_dirDeriv_dirDeriv_comp_sub (K := heatKernel d t)
    (v := fun _ : Euc d => (1 : ℝ)) ((contDiff_heatKernel t).of_le le_top)
    (integrable_heatKernel ht) (integrable_dirDeriv_heatKernel ht)
    (fun e e' => integrable_dirDeriv_dirDeriv_heatKernel ht e e')
    (boundedDerivs_const 2 1) 0 b a
  have h1 : dirDeriv a (fun _ : Euc d => (1 : ℝ)) = fun _ => 0 := by
    funext z
    simp [dirDeriv]
  have h0 : ∀ y : Euc d, dirDeriv b (dirDeriv a fun _ : Euc d => (1 : ℝ)) (0 - y) = 0 := by
    intro y
    rw [h1]
    simp [dirDeriv]
  simp only [h0, mul_zero, integral_zero, mul_one] at h
  exact h.symm

end

end LatticeProb.Analysis.Schauder
