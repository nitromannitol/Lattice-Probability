import Mathlib
import LatticeProb.LQG.LengthMetricDerived
import LatticeProb.LQG.LQGMetricMeasurable

/-!
# Chain upper bound for the internal metric of a Weyl-scaled length metric

Let `D` be a Euclidean length metric on `ℂ` and `E = e^{ξ f} · D` its Weyl scaling (Gwynne-Miller,
arXiv:1905.00383, (1.7)-(1.8)), realized as a function `E ≥ 0` with `ENNReal.ofReal (E x y) = weylScaling D ξ f x y`.

* `internalMetric_le_of_weylScaling`: on any set `V` with `ξ f ≤ B` on `V`, the internal metric of `E` on `V` is at
  most `e^B` times the internal metric of `D` on `V`.
* `internalMetric_weylScaling_le_chain_sum`: if `E` is itself a Euclidean length metric and `U` is open, then for a chain
  `z₀, …, z_m` with `z₀ ∈ U` and sets `V_i ⊆ U` with `ξ f ≤ B_i` on `V_i`,
  `E(z₀, z_m; U) ≤ ∑_{i < m} e^{B_i} D(z_i, z_{i+1}; V_i)`.

The second statement is the upper half of the approximation of the internal metric of `E` on an open set by
weighted chain sums of local internal metrics of `D`: when the `V_i` are small balls on which the weight `e^{ξ f}`
is nearly constant, the chain sums are Riemann sums for the weighted length `∫ e^{ξ f} dℓ_D`.
-/

namespace LatticeProb.LQG

open Set
open scoped ENNReal

/-- Weyl comparison of internal metrics on an arbitrary set: if `ξ f ≤ B` on `V`, then the internal metric on `V` of
the Weyl scaling `E = e^{ξ f} · D` of a Euclidean length metric `D` is at most `e^B` times that of `D`. -/
theorem internalMetric_le_of_weylScaling {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {ξ B : ℝ}
    {f : ℂ → ℝ} (hscale : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y) {V : Set ℂ}
    (hweight : ∀ z ∈ V, ξ * f z ≤ B) (x y : ℂ) :
    internalMetric E V x y ≤ ENNReal.ofReal (Real.exp B) * internalMetric D V x y := by
  have hc0 : ENNReal.ofReal (Real.exp B) ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos B)).ne'
  have hctop : ENNReal.ofReal (Real.exp B) ≠ ⊤ := ENNReal.ofReal_ne_top
  unfold internalMetric
  rw [ENNReal.mul_iInf_of_ne hc0 hctop]
  refine le_iInf fun P => ?_
  rw [ENNReal.mul_iInf_of_ne hc0 hctop]
  exact le_iInf fun hP => (iInf₂_le P hP).trans (pathLength_le_of_weylScaling hD hscale hweight P hP)

/-- Chain upper bound: for a Euclidean length metric `D`, its Weyl scaling `E = e^{ξ f} · D` (assumed to be a
Euclidean length metric with nonnegative values), an open set `U`, a chain `z₀, …, z_m` with `z₀ ∈ U`, and sets
`V_i ⊆ U` with `ξ f ≤ B_i` on `V_i`, the internal metric of `E` on `U` satisfies
`E(z₀, z_m; U) ≤ ∑_{i < m} e^{B_i} D(z_i, z_{i+1}; V_i)`. -/
theorem internalMetric_weylScaling_le_chain_sum {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE : IsEuclideanLengthMetric E) (hE0 : ∀ x y, 0 ≤ E x y) {ξ : ℝ} {f : ℂ → ℝ}
    (hscale : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y) {U : Set ℂ} (hU : IsOpen U)
    (z : ℕ → ℂ) (hz0 : z 0 ∈ U) (V : ℕ → Set ℂ) (hVU : ∀ i, V i ⊆ U) (B : ℕ → ℝ)
    (hB : ∀ i, ∀ y ∈ V i, ξ * f y ≤ B i) (m : ℕ) :
    internalMetric E U (z 0) (z m) ≤
      ∑ i ∈ Finset.range m, ENNReal.ofReal (Real.exp (B i)) * internalMetric D (V i) (z i) (z (i + 1)) := by
  induction m with
  | zero =>
    rw [hE.internalMetric_self_of_mem_open hE0 hU hz0]
    exact zero_le
  | succ m ih =>
    rw [Finset.sum_range_succ]
    calc internalMetric E U (z 0) (z (m + 1))
        ≤ internalMetric E U (z 0) (z m) + internalMetric E U (z m) (z (m + 1)) :=
          hE.internalMetric_triangle U _ _ _
      _ ≤ _ := add_le_add ih ((internalMetric_anti E (hVU m) _ _).trans
          (internalMetric_le_of_weylScaling hD hscale (hB m) _ _))

end LatticeProb.LQG
