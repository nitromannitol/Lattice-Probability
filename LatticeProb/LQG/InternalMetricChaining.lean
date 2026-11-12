import LatticeProb.LQG.LengthMetricDerived
import LatticeProb.LQG.LQGMetricMeasurable

/-! # Chaining bounds for the internal metric along a convergent sequence

Let `D` be a Euclidean length metric on `ℂ` (`IsEuclideanLengthMetric`) and `x₀, x₁, ...` a sequence converging to `z`.
The internal metric `D(·, ·; U)` satisfies the chaining bound
  `D(x₀, z; U) ≤ ∑_{n ≥ 0} D(xₙ, xₙ₊₁; U)`
in two cases:
* `U` is open and `z ∈ U`: the finite chains give `D(x₀, z; U) ≤ ∑_{n < m} D(xₙ, xₙ₊₁; U) + D(xₘ, z; U)`, and
  `D(xₘ, z; U) → D(z, z; U) = 0` by continuity of the internal metric of an open set near the diagonal;
* `U = C` is closed and bounded, `x₀, z ∈ C`: the internal metric of `C` is the limit of the internal metrics of
  its open `δ`-neighbourhoods (`internalMetricClosedEqIInfThickening_derived`), to which the open case applies.
No path is concatenated infinitely often: the limit point `z` is reached through the continuity of the internal
metric, or, for closed sets, through the Arzelà-Ascoli argument behind the thickening formula.

This is the deterministic step of the multiscale bounds for internal diameters of the LQG metric (Ding, Dubédat,
Falconet, Gwynne and Pfeffer, arXiv:1905.00380, proof of Proposition 3.10, Step 2): points of nested dyadic squares
shrinking to `z`, joined at consecutive scales by paths whose lengths are summable, bound the internal distance to `z`
including when `z` lies on the boundary of a closed square.

Main results:
* `IsEuclideanLengthMetric.internalMetric_le_sum_add`: the finite chaining bound (any set `U`).
* `IsEuclideanLengthMetric.internalMetric_le_tsum_of_tendsto`: the chaining bound for an open set.
* `IsEuclideanLengthMetric.internalMetric_le_tsum_of_tendsto_of_isClosed`: the chaining bound for a closed bounded set.
* `IsEuclideanLengthMetric.internalMetric_le_tsum_of_tendsto_of_le`, `..._of_isClosed_of_le`: the same with a bound
  `D(xₙ, xₙ₊₁; U) ≤ Lₙ` on the increments.
-/

namespace LatticeProb.LQG

open Set Filter
open scoped ENNReal _root_.Topology

/-- **Finite chaining bound.** For a Euclidean length metric `D`, any set `U`, a sequence `x` and a point `z`,
`D(x₀, z; U) ≤ ∑_{n < m} D(xₙ, xₙ₊₁; U) + D(xₘ, z; U)` for every `m`. -/
theorem IsEuclideanLengthMetric.internalMetric_le_sum_add {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (U : Set ℂ) (x : ℕ → ℂ) (z : ℂ) (m : ℕ) :
    internalMetric D U (x 0) z ≤
      (∑ n ∈ Finset.range m, internalMetric D U (x n) (x (n + 1))) + internalMetric D U (x m) z := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc internalMetric D U (x 0) z
        ≤ (∑ n ∈ Finset.range m, internalMetric D U (x n) (x (n + 1))) + internalMetric D U (x m) z := ih
      _ ≤ (∑ n ∈ Finset.range m, internalMetric D U (x n) (x (n + 1))) +
            (internalMetric D U (x m) (x (m + 1)) + internalMetric D U (x (m + 1)) z) :=
          add_le_add le_rfl (hD.internalMetric_triangle U (x m) (x (m + 1)) z)
      _ = (∑ n ∈ Finset.range (m + 1), internalMetric D U (x n) (x (n + 1))) +
            internalMetric D U (x (m + 1)) z := by
          rw [Finset.sum_range_succ, add_assoc]

/-- **Chaining bound in an open set.** For a Euclidean length metric `D`, an open set `U`, a point `z ∈ U` and a
sequence `xₙ → z`: `D(x₀, z; U) ≤ ∑_{n ≥ 0} D(xₙ, xₙ₊₁; U)`. -/
theorem IsEuclideanLengthMetric.internalMetric_le_tsum_of_tendsto {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) {U : Set ℂ} (hU : IsOpen U) {x : ℕ → ℂ} {z : ℂ} (hz : z ∈ U)
    (hx : Tendsto x atTop (𝓝 z)) :
    internalMetric D U (x 0) z ≤ ∑' n, internalMetric D U (x n) (x (n + 1)) := by
  have hnn : ∀ a b, 0 ≤ D a b := fun a b => by
    have h := hD.triangle a b a
    rw [hD.self_eq_zero, hD.symm b a] at h
    linarith
  have hc := hD.continuousAt_internalMetric_self hnn hU hz
  have h0 : internalMetric D U z z = 0 := hD.internalMetric_self_of_mem_open hnn hU hz
  have hlim : Tendsto (fun m => internalMetric D U (x m) z) atTop (𝓝 0) := by
    have h := hc.tendsto.comp hx
    rw [h0] at h
    exact h.congr fun m => hD.internalMetric_symm U z (x m)
  set S := ∑' n, internalMetric D U (x n) (x (n + 1))
  have hbound : ∀ m, internalMetric D U (x 0) z ≤ S + internalMetric D U (x m) z := fun m =>
    (hD.internalMetric_le_sum_add U x z m).trans (add_le_add (ENNReal.sum_le_tsum _) le_rfl)
  have hlim2 : Tendsto (fun m => S + internalMetric D U (x m) z) atTop (𝓝 (S + 0)) :=
    tendsto_const_nhds.add hlim
  rw [add_zero] at hlim2
  exact ge_of_tendsto' hlim2 hbound

/-- **Chaining bound in a closed bounded set.** For a Euclidean length metric `D`, a closed bounded set `C`, points
`x₀, z ∈ C` and a sequence `xₙ → z`: `D(x₀, z; C) ≤ ∑_{n ≥ 0} D(xₙ, xₙ₊₁; C)`. The point `z` may lie on the frontier
of `C`. -/
theorem IsEuclideanLengthMetric.internalMetric_le_tsum_of_tendsto_of_isClosed {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) {C : Set ℂ} (hC : IsClosed C) (hCb : Bornology.IsBounded C)
    {x : ℕ → ℂ} (hx0 : x 0 ∈ C) {z : ℂ} (hz : z ∈ C) (hx : Tendsto x atTop (𝓝 z)) :
    internalMetric D C (x 0) z ≤ ∑' n, internalMetric D C (x n) (x (n + 1)) := by
  obtain ⟨r, hr⟩ := hCb.subset_closedBall 0
  obtain ⟨N, hN⟩ := exists_nat_ge r
  rw [internalMetricClosedEqIInfThickening_derived D C hC hD hx0 hz]
  refine iInf_le_of_le N (iSup_le fun k => ?_)
  have hsub : C ⊆ Metric.closedBall 0 ((N : ℝ) + 1) :=
    hr.trans (Metric.closedBall_subset_closedBall (by linarith))
  rw [inter_eq_left.mpr hsub]
  have hδ : (0 : ℝ) < ((k : ℝ) + 1)⁻¹ := by positivity
  have hWo : IsOpen (Metric.thickening (((k : ℝ) + 1)⁻¹) C) := Metric.isOpen_thickening
  have hCW : C ⊆ Metric.thickening (((k : ℝ) + 1)⁻¹) C := Metric.self_subset_thickening hδ C
  exact (hD.internalMetric_le_tsum_of_tendsto hWo (hCW hz) hx).trans
    (ENNReal.tsum_le_tsum fun n => internalMetric_anti D hCW _ _)

/-- The chaining bound in an open set with a bound `D(xₙ, xₙ₊₁; U) ≤ Lₙ` on the increments. -/
theorem IsEuclideanLengthMetric.internalMetric_le_tsum_of_tendsto_of_le {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) {U : Set ℂ} (hU : IsOpen U) {x : ℕ → ℂ} {z : ℂ} (hz : z ∈ U)
    (hx : Tendsto x atTop (𝓝 z)) {L : ℕ → ℝ≥0∞} (hL : ∀ n, internalMetric D U (x n) (x (n + 1)) ≤ L n) :
    internalMetric D U (x 0) z ≤ ∑' n, L n :=
  (hD.internalMetric_le_tsum_of_tendsto hU hz hx).trans (ENNReal.tsum_le_tsum hL)

/-- The chaining bound in a closed bounded set with a bound `D(xₙ, xₙ₊₁; C) ≤ Lₙ` on the increments. -/
theorem IsEuclideanLengthMetric.internalMetric_le_tsum_of_tendsto_of_isClosed_of_le {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) {C : Set ℂ} (hC : IsClosed C) (hCb : Bornology.IsBounded C)
    {x : ℕ → ℂ} (hx0 : x 0 ∈ C) {z : ℂ} (hz : z ∈ C) (hx : Tendsto x atTop (𝓝 z)) {L : ℕ → ℝ≥0∞}
    (hL : ∀ n, internalMetric D C (x n) (x (n + 1)) ≤ L n) :
    internalMetric D C (x 0) z ≤ ∑' n, L n :=
  (hD.internalMetric_le_tsum_of_tendsto_of_isClosed hC hCb hx0 hz hx).trans (ENNReal.tsum_le_tsum hL)

end LatticeProb.LQG
