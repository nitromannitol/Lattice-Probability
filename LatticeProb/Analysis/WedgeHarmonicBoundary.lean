import LatticeProb.Analysis.WedgeHarmonicPower
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # Boundary continuity of a harmonic wedge profile -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- A positive real complex power is continuous on the closed right half-plane. -/
theorem continuousAt_re_cpow_of_nonneg_re {p : ℝ} (hp : 0 < p) {z : ℂ}
    (hz : 0 ≤ z.re) : ContinuousAt (fun w : ℂ => (w ^ (p : ℂ)).re) z := by
  exact Complex.continuous_re.continuousAt.comp
    (Complex.continuousAt_cpow_const_of_re_pos (Or.inl hz) (by simpa using hp))

/-- The wedge profile is continuous and nonnegative on the closure of the wedge. -/
theorem wedge_re_cpow_continuousOn_nonneg_closure {θ : ℝ} (hθ0 : 0 < θ)
    (hθπ : θ < Real.pi) :
    let W : Set ℂ := (fun z : ℂ => (z.re, z.im)) ⁻¹'
      CorrelatedBM.openSymmetricWedge (Real.sin (θ / 2)) (Real.cos (θ / 2))
    ContinuousOn (fun z : ℂ => (z ^ ((Real.pi / θ : ℝ) : ℂ)).re) (closure W) ∧
      ∀ z ∈ closure W, 0 ≤ (z ^ ((Real.pi / θ : ℝ) : ℂ)).re := by
  dsimp only
  let W : Set ℂ := (fun z : ℂ => (z.re, z.im)) ⁻¹'
    CorrelatedBM.openSymmetricWedge (Real.sin (θ / 2)) (Real.cos (θ / 2))
  have hp : 0 < Real.pi / θ := div_pos Real.pi_pos hθ0
  have hs : 0 < Real.sin (θ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hW : ∀ z ∈ W, 0 < z.re := by
    intro z hz
    change |Real.cos (θ / 2) * z.im| < Real.sin (θ / 2) * z.re at hz
    exact (mul_pos_iff_of_pos_left hs).1 (lt_of_le_of_lt (abs_nonneg _) hz)
  have hclose : ∀ z ∈ closure W, 0 ≤ z.re := by
    apply closure_minimal (fun z hz => (hW z hz).le)
    exact isClosed_le continuous_const Complex.continuous_re
  have hcont : ContinuousOn (fun z : ℂ => (z ^ ((Real.pi / θ : ℝ) : ℂ)).re)
      (closure W) := fun z hz => (continuousAt_re_cpow_of_nonneg_re hp (hclose z hz)).continuousWithinAt
  constructor
  · exact hcont
  · intro z hz
    have hsub : W ⊆ {z : ℂ | 0 ≤ (z ^ ((Real.pi / θ : ℝ) : ℂ)).re} := by
      intro w hw
      exact (wedge_re_cpow_harmonic_pos hθ0 hθπ hw).2.le
    exact le_on_closure (s := W) (f := fun _ : ℂ => (0 : ℝ))
      (g := fun w : ℂ => (w ^ ((Real.pi / θ : ℝ) : ℂ)).re)
      (fun w hw => hsub hw) continuousOn_const hcont hz

end LatticeProb
