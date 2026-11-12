/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.P4_3Aux at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Proposition 4.3: elementary steps of Step 2–3 (task P2-DFA10)

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`, "T"), proof of Proposition 4.3:
* Step 3, T:2724–2741: from `∑_{j<k} (σ_j − τ_j) ≤ C (σ_k − τ_k)` for all `k < K` the excursion
  times grow geometrically (`eqn-C-good-dist`), and with `σ_0 − τ_0 ≥ ε^A (σ_{K−1} − τ_{K−1})`
  (`eqn-holder-cont-bdy`) this bounds `K` (`excursion_count`);
* Step 2, T:2706–2708: the area of a union of `K` Euclidean balls of radius `r` is `≤ K π r²`
  (`volume_biUnion_ball_le`).
-/

noncomputable section

open MeasureTheory Set Metric Finset
open scoped ENNReal

namespace LQGMetric.DFGPS
namespace P43

/-- (`eqn-C-good-dist`, T:2724–2730): partial sums grow geometrically -/
theorem geom_growth {C : ℝ} (hC : 0 < C) (x : ℕ → ℝ) {K : ℕ}
    (h : ∀ k, k < K → ∑ j ∈ range k, x j ≤ C * x k) :
    ∀ k, 1 ≤ k → k ≤ K → (1 + C⁻¹) ^ (k - 1) * x 0 ≤ ∑ j ∈ range k, x j := by
  intro k hk1 hkK
  induction k with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have ih' := ih hn (by omega)
      have hxn : C⁻¹ * ∑ j ∈ range n, x j ≤ x n := by
        rw [inv_mul_le_iff₀ hC]; exact h n (by omega)
      rw [sum_range_succ, show n + 1 - 1 = (n - 1) + 1 by omega, pow_succ]
      have : 0 ≤ (1 + C⁻¹) := by positivity
      nlinarith [inv_pos.2 hC]

/-- **the excursion count** (T:2738–2741): if the `K ≥ 2` excursion durations `x_k > 0` satisfy
`∑_{j<k} x_j ≤ C x_k` (`k < K`) and `x_0 ≥ ε^A x_{K−1}`, then `(1 + C⁻¹)^{K−2} ≤ C ε^{-A}`,
i.e. `K ≤ 2 + log(C ε^{-A}) / log(1 + C⁻¹)` -/
theorem excursion_count {C ε A : ℝ} (hC : 0 < C) (hε : 0 < ε) (x : ℕ → ℝ) {K : ℕ} (hK : 2 ≤ K)
    (hpos : 0 < x 0) (h : ∀ k, k < K → ∑ j ∈ range k, x j ≤ C * x k)
    (hratio : ε ^ A * x (K - 1) ≤ x 0) :
    (1 + C⁻¹) ^ (K - 2) ≤ C * ε ^ (-A) := by
  have hg := geom_growth hC x h (K - 1) (by omega) (by omega)
  have hlast := h (K - 1) (by omega)
  rw [show K - 1 - 1 = K - 2 by omega] at hg
  have hεA : 0 < ε ^ A := Real.rpow_pos_of_pos hε A
  have h1 : (1 + C⁻¹) ^ (K - 2) * x 0 ≤ C * x (K - 1) := hg.trans hlast
  have h2 : C * x (K - 1) ≤ C * (ε ^ A)⁻¹ * x 0 := by
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hC.le
    rw [inv_mul_eq_div, le_div_iff₀ hεA, mul_comm]; exact hratio
  rw [Real.rpow_neg hε.le]
  exact le_of_mul_le_mul_right (h1.trans h2) hpos

end P43
end LQGMetric.DFGPS
