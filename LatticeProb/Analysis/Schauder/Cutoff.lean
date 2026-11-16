import LatticeProb.Analysis.Schauder.DirDerivComm

/-!
# A smooth cutoff for the localization of interior estimates

Interior estimates on a ball are obtained by multiplying the function with a smooth cutoff. The
cutoff at `x` is a `C^∞` bump function that equals `1` on the closed ball of radius `3/4` around
`x` and is supported in the ball of radius `1`. This file records the properties of the localized
function `z ↦ cutoffBump x z * u z` that the localization uses: it is as smooth as `u`, it is
bounded by the bound of `u` on a neighbouring ball, and on the ball of radius `3/4` around `x` it
agrees with `u` near every point, so that all of its derivatives there (the iterated derivatives,
the Laplacian and the nested directional derivatives) are those of `u`.
-/

namespace LatticeProb.Analysis.Schauder

noncomputable section

variable {d : ℕ}

/-- The cutoff at `x`: `1` on the closed ball of radius `3/4`, supported in the ball of radius 1. -/
def cutoffBump (x : Euc d) : ContDiffBump x := ⟨3 / 4, 1, by norm_num, by norm_num⟩

/-- The localization of a `Cⁿ` function by the cutoff is `Cⁿ`. -/
theorem contDiff_cutoffBump_mul {n : ℕ} (x : Euc d) {u : Euc d → ℝ} (hu : ContDiff ℝ n u) :
    ContDiff ℝ n (fun z => cutoffBump x z * u z) :=
  (cutoffBump x).contDiff.mul hu

/-- The localized function is bounded by the bound of `u` on the ball of radius 2. -/
theorem abs_cutoffBump_mul_le {u : Euc d → ℝ} {x x₀ : Euc d} {K₀ : ℝ}
    (hx : x ∈ Metric.closedBall x₀ 1) (hu : ∀ z ∈ Metric.closedBall x₀ 2, |u z| ≤ K₀)
    (z : Euc d) : |cutoffBump x z * u z| ≤ K₀ := by
  have hK₀ : 0 ≤ K₀ := (abs_nonneg _).trans (hu x₀ (Metric.mem_closedBall_self (by norm_num)))
  by_cases hz : dist z x < 1
  · have hx' : dist x x₀ ≤ 1 := Metric.mem_closedBall.1 hx
    have hzx₀ : z ∈ Metric.closedBall x₀ 2 := by
      rw [Metric.mem_closedBall]
      calc dist z x₀ ≤ dist z x + dist x x₀ := dist_triangle _ _ _
        _ ≤ 2 := by linarith
    rw [abs_mul, abs_of_nonneg (cutoffBump x).nonneg]
    calc (cutoffBump x) z * |u z| ≤ 1 * |u z| :=
          mul_le_mul_of_nonneg_right (cutoffBump x).le_one (abs_nonneg _)
      _ ≤ K₀ := by rw [one_mul]; exact hu z hzx₀
  · have h0 : cutoffBump x z = 0 := (cutoffBump x).zero_of_le_dist (not_lt.1 hz)
    rw [h0, zero_mul, abs_zero]
    exact hK₀

/-- Near every point of the ball of radius `3/4` around `x`, the localized function is `u`. -/
theorem cutoffBump_mul_eventuallyEq {u : Euc d → ℝ} {x z : Euc d}
    (hz : z ∈ Metric.ball x (3 / 4)) : (fun y => cutoffBump x y * u y) =ᶠ[nhds z] u := by
  filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy
  rw [(cutoffBump x).one_of_mem_closedBall (Metric.ball_subset_closedBall hy), one_mul]

/-- The iterated derivatives of the localized function at a point of the ball of radius `3/4`
agree with those of `u`. -/
theorem iteratedFDeriv_cutoffBump_mul {u : Euc d → ℝ} {x z : Euc d}
    (hz : z ∈ Metric.ball x (3 / 4)) (k : ℕ) :
    iteratedFDeriv ℝ k (fun y => cutoffBump x y * u y) z = iteratedFDeriv ℝ k u z :=
  ((cutoffBump_mul_eventuallyEq hz).iteratedFDeriv ℝ k).eq_of_nhds

/-- The Laplacian of the localized function at a point of the ball of radius `3/4` is the
Laplacian of `u`. -/
theorem laplacianSum_cutoffBump_mul {u : Euc d → ℝ} {x z : Euc d}
    (hz : z ∈ Metric.ball x (3 / 4)) :
    laplacianSum (fun y => cutoffBump x y * u y) z = laplacianSum u z := by
  unfold laplacianSum
  rw [iteratedFDeriv_cutoffBump_mul hz 2]

/-- The nested directional derivatives of the localized function at a point of the ball of
radius `3/4` are those of `u`. -/
theorem dirDeriv_dirDeriv_cutoffBump_mul {u : Euc d → ℝ} (hu : ContDiff ℝ 2 u) {x z : Euc d}
    (hz : z ∈ Metric.ball x (3 / 4)) (a b : Euc d) :
    dirDeriv a (dirDeriv b (fun y => cutoffBump x y * u y)) z = dirDeriv a (dirDeriv b u) z := by
  rw [← iteratedFDeriv_two_apply_eq_dirDeriv (contDiff_cutoffBump_mul x hu),
    ← iteratedFDeriv_two_apply_eq_dirDeriv hu, iteratedFDeriv_cutoffBump_mul hz 2]

end

end LatticeProb.Analysis.Schauder
