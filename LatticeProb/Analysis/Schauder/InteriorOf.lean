import LatticeProb.Analysis.Schauder.Statement
import LatticeProb.Analysis.Schauder.BilinearEntryBound
import LatticeProb.Analysis.Schauder.DirDerivComm

/-!
# The interior Schauder estimate from a bound on the second derivatives

The interior Schauder estimate at unit scale bounds the operator norm of the Hessian of `u` on
`B₁(x₀)` by `C (K₀ + K₁)`, where `K₀` bounds `|u|` and `K₁` bounds the Laplacian of `u` together
with its Hölder seminorm on `B₂(x₀)`.  It suffices to bound each second directional derivative
`∂_a ∂_b u (x)` in unit directions `a`, `b` by `A K₀ + B (K₀ + K₁)`: the operator norm of the
Hessian is dominated by the sum of the absolute values of its `d²` entries in the standard basis,
each of which is a second directional derivative in the unit directions `e_j`, `e_k`.
-/

namespace LatticeProb.Analysis.Schauder

noncomputable section

variable {d : ℕ}

/-- **The interior Schauder estimate from an entry bound.** If, for every Hölder exponent
`α ∈ (0, 1)`, the second directional derivatives `∂_a ∂_b u (x)` in unit directions of a `C²`
function are bounded at points `x ∈ B₁(x₀)` by `A K₀ + B (K₀ + K₁)`, where `K₀` bounds `|u|` and
`K₁` bounds the Laplacian of `u` and its `α`-Hölder seminorm on `B₂(x₀)`, then the interior
Schauder estimate holds with the constant `d² (|A| + |B|)`. -/
theorem schauderInterior_of_entryBound
    (h : ∀ α : ℝ, 0 < α → α < 1 → ∃ A B : ℝ, ∀ (u : Euc d → ℝ) (x₀ x : Euc d) (K₀ K₁ : ℝ),
      ContDiff ℝ 2 u → x ∈ Metric.closedBall x₀ 1 →
      (∀ z ∈ Metric.closedBall x₀ 2, |u z| ≤ K₀) →
      (∀ z ∈ Metric.closedBall x₀ 2, ∀ z' ∈ Metric.closedBall x₀ 2,
        |laplacianSum u z| ≤ K₁ ∧
          |laplacianSum u z - laplacianSum u z'| ≤ K₁ * dist z z' ^ α) →
      ∀ a b : Euc d, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
        |dirDeriv a (dirDeriv b u) x| ≤ A * K₀ + B * (K₀ + K₁)) :
    LatticeProb.Analysis.Schauder.SchauderInterior d := by
  intro α hα0 hα1
  obtain ⟨A, B, hAB⟩ := h α hα0 hα1
  refine ⟨(d : ℝ) ^ 2 * (|A| + |B|), ?_⟩
  intro u x₀ K₀ K₁ hu hu0 hu1 x hx
  have hK₀ : 0 ≤ K₀ :=
    (abs_nonneg _).trans (hu0 x₀ (Metric.mem_closedBall_self (by norm_num)))
  have hK₁ : 0 ≤ K₁ :=
    (abs_nonneg _).trans
      (hu1 x₀ (Metric.mem_closedBall_self (by norm_num)) x₀
        (Metric.mem_closedBall_self (by norm_num))).1
  have hentry : ∀ j k : Fin d,
      |iteratedFDeriv ℝ 2 u x ![EuclideanSpace.single j 1, EuclideanSpace.single k 1]| ≤
        (|A| + |B|) * (K₀ + K₁) := by
    intro j k
    rw [iteratedFDeriv_two_apply_eq_dirDeriv hu]
    refine (hAB u x₀ x K₀ K₁ hu hx hu0 hu1 (EuclideanSpace.single j 1)
      (EuclideanSpace.single k 1) (by simp) (by simp)).trans ?_
    nlinarith [mul_nonneg (abs_nonneg A) hK₁, mul_le_mul_of_nonneg_right (le_abs_self A) hK₀,
      mul_le_mul_of_nonneg_right (le_abs_self B) (add_nonneg hK₀ hK₁)]
  calc ‖iteratedFDeriv ℝ 2 u x‖
      ≤ ∑ j : Fin d, ∑ k : Fin d,
        |iteratedFDeriv ℝ 2 u x ![EuclideanSpace.single j 1, EuclideanSpace.single k 1]| :=
        norm_le_sum_abs_apply_single _
    _ ≤ ∑ _j : Fin d, ∑ _k : Fin d, (|A| + |B|) * (K₀ + K₁) :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hentry j k
    _ = (d : ℝ) ^ 2 * (|A| + |B|) * (K₀ + K₁) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end

end LatticeProb.Analysis.Schauder
