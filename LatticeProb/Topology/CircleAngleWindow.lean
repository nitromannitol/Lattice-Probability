/-
# Distinct circle points in one angular turn

The angles are arbitrary real representatives. Only their strict ordering and
the final wraparound bound are used.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith



namespace LatticeProb.Topology

/-- Strictly ordered angles separated by less than one turn have distinct circle points. -/
theorem circle_point_ne_of_lt_lt_add_two_pi {a b : ℝ} (hab : a < b)
    (hba : b < a + 2 * Real.pi) :
    ((Real.cos a, Real.sin a) : ℝ × ℝ) ≠ (Real.cos b, Real.sin b) := by
  intro h
  have hc : Real.cos a = Real.cos b := congrArg Prod.fst h
  have hs : Real.sin a = Real.sin b := congrArg Prod.snd h
  have hone : Real.cos (b - a) = 1 := by
    rw [Real.cos_sub, ← hc, ← hs]
    simpa only [pow_two] using Real.cos_sq_add_sin_sq a
  have hzero : b - a = 0 :=
    (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [Real.pi_pos]) (by linarith)).mp hone
  linarith

/-- **Distinct cyclic endpoints.** All six pairs of an alternating boundary quadruple are distinct. -/
theorem circle_points_pairwise_ne_of_cyclic_order {θ₁ θ₂ θ₃ θ₄ : ℝ}
    (h₁₂ : θ₁ < θ₂) (h₂₃ : θ₂ < θ₃) (h₃₄ : θ₃ < θ₄)
    (h₄₁ : θ₄ < θ₁ + 2 * Real.pi) :
    ((Real.cos θ₁, Real.sin θ₁) : ℝ × ℝ) ≠ (Real.cos θ₂, Real.sin θ₂) ∧
    ((Real.cos θ₁, Real.sin θ₁) : ℝ × ℝ) ≠ (Real.cos θ₃, Real.sin θ₃) ∧
    ((Real.cos θ₁, Real.sin θ₁) : ℝ × ℝ) ≠ (Real.cos θ₄, Real.sin θ₄) ∧
    ((Real.cos θ₂, Real.sin θ₂) : ℝ × ℝ) ≠ (Real.cos θ₃, Real.sin θ₃) ∧
    ((Real.cos θ₂, Real.sin θ₂) : ℝ × ℝ) ≠ (Real.cos θ₄, Real.sin θ₄) ∧
    ((Real.cos θ₃, Real.sin θ₃) : ℝ × ℝ) ≠ (Real.cos θ₄, Real.sin θ₄) := by
  exact ⟨circle_point_ne_of_lt_lt_add_two_pi h₁₂ (by linarith),
    circle_point_ne_of_lt_lt_add_two_pi (h₁₂.trans h₂₃) (by linarith),
    circle_point_ne_of_lt_lt_add_two_pi ((h₁₂.trans h₂₃).trans h₃₄) h₄₁,
    circle_point_ne_of_lt_lt_add_two_pi h₂₃ (by linarith),
    circle_point_ne_of_lt_lt_add_two_pi (h₂₃.trans h₃₄) (by linarith),
    circle_point_ne_of_lt_lt_add_two_pi h₃₄ (by linarith)⟩

end LatticeProb.Topology
