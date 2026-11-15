import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-! # Classical Dirichlet extension on an interval -/

set_option autoImplicit false

namespace LatticeProb

/-- Arbitrary endpoint values on a nondegenerate interval have a continuous
extension whose second derivative vanishes. -/
theorem exists_interval_dirichlet_extension {a b : ℝ} (hab : a < b) (u v : ℝ) :
    ∃ f : ℝ → ℝ, Continuous f ∧ f a = u ∧ f b = v ∧
      ∀ x, HasDerivAt (deriv f) 0 x := by
  let c := (v - u) / (b - a)
  let f : ℝ → ℝ := fun x => u + c * (x - a)
  have hf (x : ℝ) : HasDerivAt f c x := by
    dsimp [f]
    have hx : HasDerivAt (fun y : ℝ => y - a) 1 x :=
      (hasDerivAt_id' x).sub_const a
    simpa only [mul_one] using
      (hasDerivAt_const_add_iff u).2 (HasDerivAt.const_mul c hx)
  have hderiv : deriv f = fun _ => c := by
    funext x
    exact (hf x).deriv
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · exact continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  · simp [f]
  · dsimp [f, c]
    have hne : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
    field_simp
    ring
  · intro x
    rw [hderiv]
    exact hasDerivAt_const x c

end LatticeProb
