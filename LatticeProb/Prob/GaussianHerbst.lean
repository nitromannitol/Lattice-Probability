/-
The Chernoff step of Gaussian concentration, from the cited Herbst exponential
moment bound.

`LatticeProb.gaussian_lipschitz_concentration` is the concentration inequality
of Tsirelson–Ibragimov–Sudakov for a Lipschitz functional of `n` independent
standard Gaussians: it is one application of
`LatticeProb.measure_ge_le_of_mgf_bound` to the cited bound
`LatticeProb.GaussianHerbstBound n`.
-/

import LatticeProb.Prob.GaussianConcentration
import LatticeProb.External.GaussianLogSobolev

noncomputable section
open MeasureTheory ProbabilityTheory

namespace LatticeProb

/-- **Gaussian concentration for a Lipschitz functional of `n` independent
standard Gaussians** (Borell; Tsirelson–Ibragimov–Sudakov), from the cited
Herbst exponential moment bound. -/
theorem gaussian_lipschitz_concentration (n : ℕ) (hHerbst : GaussianHerbstBound n)
    (f : (Fin n → ℝ) → ℝ) (L : ℝ) (hL : 0 < L)
    (hf : LipschitzWith ⟨L, hL.le⟩ f) (t : ℝ) (ht : 0 ≤ t) :
    (Measure.pi fun _ : Fin n => gaussianReal 0 1).real
        {x | t ≤ f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)}
      ≤ Real.exp (-(t ^ 2) / (2 * L ^ 2)) := by
  rcases eq_or_lt_of_le ht with h | ht'
  · subst h
    have : Real.exp (-(0:ℝ)^2 / (2*L^2)) = 1 := by
      simp [Real.exp_zero]
    rw [this]
    exact MeasureTheory.measureReal_le_one
  · exact LatticeProb.measure_ge_le_of_mgf_bound _ f _ L t hL ht'
      (fun lam hlam => LatticeProb.integrable_exp_lipschitz_gaussian n f L hL hf lam)
      (fun lam hlam => hHerbst f L hL hf lam hlam)

end LatticeProb
