import LatticeProb.Prob.Percolation.LatticeHarmonicGrowth
import LatticeProb.Prob.Percolation.LatticeUniqueCluster

/-!
# Harmonic planes with prescribed asymptotic slope

The slope is an actual real coordinate vector and the domain is an actual open component.
Sublinearity is uniform on the accepted Euclidean balls, at every sufficiently large real
radius. The predicate makes no selection and asserts no existence or uniqueness theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

open scoped BigOperators

noncomputable section

variable {d : ℕ} {ω : Configuration d}

/-- The literal Euclidean affine linear part restricted to component vertices. -/
def componentSlope (C : OpenComponent ω) (p : Fin d → ℝ) (x : C) : ℝ :=
  ∑ i, p i * (x.val i : ℝ)

/-- Uniform sublinear error from a prescribed slope on actual open Euclidean balls. -/
def componentSlopeAsymptotics (C : OpenComponent ω) (p : Fin d → ℝ)
    (u : C → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
    ∀ x ∈ componentEuclideanBall C 0 R, |u x - componentSlope C p x| ≤ ε * R

/-- A source corrected plane is harmonic in A₁ and has the stated slope at infinity.
Uniqueness modulo constants is a separate literature assertion, absent from this predicate. -/
def IsCorrectedPlane (C : OpenComponent ω) (p : Fin d → ℝ) (u : C → ℝ) : Prop :=
  u ∈ harmonicGrowthSpace C 1 ∧ componentSlopeAsymptotics C p u

/-- Every constant is a genuine zero-slope corrected plane on any actual component. -/
theorem isCorrectedPlane_const (C : OpenComponent ω) (c : ℝ) :
    IsCorrectedPlane C 0 (fun _ => c) := by
  refine ⟨const_mem_harmonicGrowthSpace C 1 c, ?_⟩
  intro ε hε
  refine ⟨(|c| + 1) / ε, div_pos (by positivity) hε, ?_⟩
  intro R hR x _
  have hb : |c| + 1 ≤ ε * R := by
    have := (div_le_iff₀ hε).mp hR
    linarith
  simpa only [componentSlope, Pi.zero_apply, zero_mul, Finset.sum_const_zero, sub_zero]
    using (show |c| ≤ ε * R by linarith)

end

end LatticeProb.Percolation
