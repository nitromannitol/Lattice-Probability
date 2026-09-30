/-
A telescoping sum over `ℕ` for an arbitrary real sequence `f : ℕ → ℝ`, telescoping
`∑_{k<t} (f(k+1) - f(k))` down to `f(t) - f(0)`. Useful for a martingale second-moment bound
built from consecutive differences of a mean process.

Moved from Parking-Sharpness.
-/
import Mathlib

noncomputable section
namespace LatticeProb.Scaling.Telescope

/-- **A telescoping sum over `ℕ`.** `∑_{k<t} (f(k+1) - f(k)) = f(t) - f(0)`, for an arbitrary
real sequence `f`. -/
theorem sum_range_sub_telescope (f : ℕ → ℝ) (t : ℕ) :
    ∑ k ∈ Finset.range t, (f (k + 1) - f k) = f t - f 0 := by
  induction t with
  | zero => simp
  | succ t ih => rw [Finset.sum_range_succ, ih]; ring

end LatticeProb.Scaling.Telescope
end
