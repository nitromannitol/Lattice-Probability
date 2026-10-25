import LatticeProb.Prob.Percolation.LatticeClusterBall

/-!
# Cardinality-normalized L² on component balls

The squared values are summed over the actual finite component ball and divided by its
actual cardinality before taking the square root. On an empty ball the real division
convention `0 / 0 = 0` gives zero; constant norms require a nonempty ball explicitly.
-/

namespace LatticeProb.Percolation

open scoped BigOperators

noncomputable section

variable {d : ℕ} {ω : Configuration d}

/-- The source normalized L² expression on the literal finite component ball. -/
def componentBallL2 (C : OpenComponent ω) (z : Vertex d) (r : ℝ) (u : C → ℝ) : ℝ :=
  Real.sqrt ((∑ x ∈ componentEuclideanBall C z r, (u x) ^ 2) /
    ((componentEuclideanBall C z r).card : ℝ))

/-- The normalized L² expression is always nonnegative. -/
theorem componentBallL2_nonneg (C : OpenComponent ω) (z : Vertex d) (r : ℝ)
    (u : C → ℝ) : 0 ≤ componentBallL2 C z r u :=
  Real.sqrt_nonneg _

/-- The empty-ball value is explicitly the real `0 / 0` convention under the square root. -/
theorem componentBallL2_of_empty (C : OpenComponent ω) (z : Vertex d) (r : ℝ)
    (u : C → ℝ) (h : componentEuclideanBall C z r = ∅) :
    componentBallL2 C z r u = 0 := by
  simp only [componentBallL2, h, Finset.sum_empty, Finset.card_empty, Nat.cast_zero,
    div_zero, Real.sqrt_zero]

/-- Every nonpositive-radius ball has normalized L² value zero. -/
theorem componentBallL2_of_nonpos (C : OpenComponent ω) (z : Vertex d) {r : ℝ}
    (u : C → ℝ) (hr : r ≤ 0) : componentBallL2 C z r u = 0 :=
  componentBallL2_of_empty C z r u (componentEuclideanBall_eq_empty C z hr)

/-- The zero function has zero normalized L² value, with no nonemptiness requirement. -/
theorem componentBallL2_zero (C : OpenComponent ω) (z : Vertex d) (r : ℝ) :
    componentBallL2 C z r (fun _ => 0) = 0 := by
  simp only [componentBallL2, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero,
    zero_div, Real.sqrt_zero]

/-- The denominator is positive exactly when an actual component vertex lies in the ball. -/
theorem componentBallL2_card_pos_iff (C : OpenComponent ω) (z : Vertex d) (r : ℝ) :
    0 < ((componentEuclideanBall C z r).card : ℝ) ↔
      ∃ x : Vertex d, x ∈ C.supp ∧
        dist (latticeEuclideanEmbedding x) (latticeEuclideanEmbedding z) < r := by
  rw [Nat.cast_pos, Finset.card_pos, componentEuclideanBall_nonempty_iff]

/-- On a nonempty ball the constant function has norm equal to its absolute value. -/
theorem componentBallL2_const (C : OpenComponent ω) (z : Vertex d) (r c : ℝ)
    (h : (componentEuclideanBall C z r).Nonempty) :
    componentBallL2 C z r (fun _ => c) = |c| := by
  have hc : ((componentEuclideanBall C z r).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr h)
  simp only [componentBallL2, Finset.sum_const, nsmul_eq_mul]
  rw [mul_div_cancel_left₀ (c ^ 2) hc, Real.sqrt_sq_eq_abs]

/-- Vanishing normalized L² is exactly pointwise vanishing on the actual ball. -/
theorem componentBallL2_eq_zero_iff (C : OpenComponent ω) (z : Vertex d) (r : ℝ)
    (u : C → ℝ) :
    componentBallL2 C z r u = 0 ↔ ∀ x ∈ componentEuclideanBall C z r, u x = 0 := by
  classical
  by_cases h : (componentEuclideanBall C z r).Nonempty
  · have hc : ((componentEuclideanBall C z r).card : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.card_ne_zero.mpr h)
    have hs : 0 ≤ ∑ x ∈ componentEuclideanBall C z r, (u x) ^ 2 :=
      Finset.sum_nonneg (fun x _ => sq_nonneg (u x))
    rw [componentBallL2, Real.sqrt_eq_zero (div_nonneg hs (Nat.cast_nonneg _)),
      div_eq_zero_iff, or_iff_left hc,
      Finset.sum_eq_zero_iff_of_nonneg (fun x _ => sq_nonneg (u x))]
    simp only [sq_eq_zero_iff]
  · have he : componentEuclideanBall C z r = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    rw [componentBallL2_of_empty C z r u he]
    simp only [he, Finset.notMem_empty, false_implies, implies_true]

/-- On the actual singleton all-closed component, the norm is the absolute center value. -/
theorem allClosed_componentBallL2 (z : Vertex d) {r : ℝ} (hr : 0 < r)
    (u : (openGraph (allClosed d)).connectedComponentMk z → ℝ) :
    componentBallL2 ((openGraph (allClosed d)).connectedComponentMk z) z r u =
      |u ⟨z, rfl⟩| := by
  classical
  simp only [componentBallL2, allClosed_componentEuclideanBall z hr,
    Finset.sum_singleton, Finset.card_singleton, Nat.cast_one, div_one,
    Real.sqrt_sq_eq_abs]

end

end LatticeProb.Percolation
