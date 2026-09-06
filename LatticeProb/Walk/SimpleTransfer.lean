/-
The Green function of the simple walk, and the transfer of a gradient bound to
it from the lazy walk.

For `d \u2265 3` both walks have a finite Green function and they differ by the
factor two of `LatticeProb/Walk/GreenIdentity.lean`, so any bound proved for
the truncated lazy Green function, uniformly in the horizon, passes to the
limit and halves.
-/
import Mathlib
import LatticeProb.Walk.Green
import LatticeProb.Walk.SRWGreenSup
import LatticeProb.Walk.GreenIdentity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb

open Finset Filter Topology

variable {d : ℕ}

/-- The Green function of the simple random walk, in the transient case. -/
noncomputable def srwGreenInf (d : ℕ) (x : Site d) : ℝ := ∑' j : ℕ, srwHeat d j x

/-- The truncated lazy Green functions converge to the lazy Green function. -/
theorem tendsto_gR (hsum : ∀ x : Site d, Summable fun r : ℕ => Q^[r] (delta0 : Site d → ℝ) x)
    (x : Site d) :
    Tendsto (fun R : ℕ => gR R x) atTop (𝓝 (∑' r : ℕ, Q^[r] (delta0 : Site d → ℝ) x)) := by
  have h := (hsum x).hasSum
  simpa [gR] using h.tendsto_sum_nat

/-- The gradient bound transfers from the truncated lazy Green function to the
Green function of the simple walk, through the identity between them. -/
theorem srwGreenInf_gradient_of {C : ℝ}
    (hsum : ∀ x : Site d, Summable fun r : ℕ => Q^[r] (delta0 : Site d → ℝ) x)
    (hid : ∀ x : Site d, ∑' r : ℕ, Q^[r] (delta0 : Site d → ℝ) x = 2 * srwGreenInf d x)
    (hgrad : ∀ (R : ℕ) (y z : Site d), z ∈ nbrFinset y →
      |gR R y - gR R z| ≤ C * (1 + (graphNorm y : ℝ)) ^ (1 - (d : ℝ)))
    (y z : Site d) (hz : z ∈ nbrFinset y) :
    |srwGreenInf d y - srwGreenInf d z|
      ≤ C / 2 * (1 + (graphNorm y : ℝ)) ^ (1 - (d : ℝ)) := by
  have hlim : Tendsto (fun R : ℕ => |gR R y - gR R z|) atTop
      (𝓝 |2 * srwGreenInf d y - 2 * srwGreenInf d z|) := by
    have h1 := tendsto_gR hsum y
    have h2 := tendsto_gR hsum z
    rw [hid y] at h1
    rw [hid z] at h2
    exact (h1.sub h2).abs
  have hle : |2 * srwGreenInf d y - 2 * srwGreenInf d z|
      ≤ C * (1 + (graphNorm y : ℝ)) ^ (1 - (d : ℝ)) :=
    le_of_tendsto' hlim fun R => hgrad R y z hz
  have hexp : (2 : ℝ) * |srwGreenInf d y - srwGreenInf d z|
      = |2 * srwGreenInf d y - 2 * srwGreenInf d z| := by
    rw [← abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ)), ← abs_mul]
    congr 1
    ring
  linarith [hexp, hle]

end LatticeProb
