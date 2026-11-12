import LatticeProb.LQG.ExpShellSquareCover
import LatticeProb.LQG.InternalDiamFinite
import LatticeProb.LQG.InternalMetricSquareBorelCantelli
import LatticeProb.Analysis.ExpWeightedTailSummable

/-!
# Summability of the weighted internal diameters of the exponential shells

Let `𝔇` be a γ-LQG metric and `h` a whole-plane GFF. For the exponential shells
`Aₖ = {e^{-(k+1)} ≤ |x| ≤ e^{-k}}`, we show that almost surely
`∑ₖ e^{ξ α₀ k} · diam(Aₖ; D_h restricted to the e^{-(k+2)}-neighbourhood of Aₖ) < ∞`.
This is the series that controls the metric `e^{ξ f} · D_h` for the log-singular function
`f = -α₀ log |·|` near the origin (Dubédat-Falconet-Gwynne-Pfeffer-Sun, arXiv:1905.00380, Proposition 3.17, last
paragraph of the proof).

Each shell is covered by the closed squares of the grid of mesh `tₖ = e^{-k} / 32` with indices in `[-33, 32]²`.
For each index `p`, the square Borel-Cantelli bound gives that almost surely the internal diameter of the `p`-th square
is eventually at most `e^{-η k + ε k}`. Its inputs are a summable tail for the unit square, uniform over whole-plane GFFs,
and summable tails for the events `-η k < ξ (h_{tₖ}(tₖ p) + Q log tₖ)`. Summing over the finitely many squares and
choosing `ξ α₀ + ε < η` gives a geometrically decaying bound, and every shell has finite internal diameter.

* `LatticeProb.LQG.isCompact_expShell`: the shells are compact.
* `LatticeProb.LQG.IsLQGMetric.ae_tsum_expShell_internalDiam_ne_top_of_tails`: the almost sure summability, given the
  unit-square tail and the circle-average tails at the grid corners.
-/

open MeasureTheory Filter Set LatticeProb.Gauss
open scoped ENNReal Topology

namespace LatticeProb.LQG

variable {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- The exponential shells `{e^{-(k+1)} ≤ |x| ≤ e^{-k}}` are compact. -/
theorem isCompact_expShell (k : ℕ) : IsCompact (expShell k) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
  · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := Real.exp (-(k : ℝ)))).subset fun x hx => ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hx.2

/-- **Almost sure summability of the weighted shell diameters, from tails.** Let `𝔇` be a γ-LQG metric and `h` a
whole-plane GFF. Let `ε > 0` and `ξ α₀ + ε < η`. Suppose that for every whole-plane GFF the internal diameter of the
closed unit square exceeds `e^{ε k}` with probability at most `ψₖ`, where `∑ ψₖ < ∞`. Suppose also that for every
grid index `p ∈ [-33, 32]²` the events `-η k < ξ (h_{tₖ}(tₖ p) + Q log tₖ)`, with `tₖ = e^{-k} / 32`, have summable
probabilities. Then almost surely `∑ₖ e^{ξ α₀ k} · diam(Aₖ; D_h on the e^{-(k+2)}-neighbourhood of Aₖ) < ∞`. -/
theorem IsLQGMetric.ae_tsum_expShell_internalDiam_ne_top_of_tails (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hG : IsWholePlaneGFF P hC hcirc) {α₀ η ε : ℝ} (hαη : ξ * α₀ + ε < η) {ψ : ℕ → ℝ≥0∞}
    (hψ : ∑' k, ψ k ≠ ⊤)
    (htail : ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC' hcirc' → ∀ k : ℕ,
      P {ω | ¬ ∀ u ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1,
        internalMetric (𝔇 (hC' ω)) (Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1) u v ≤
          ENNReal.ofReal (Real.exp (ε * k))} ≤ ψ k)
    (hcircTail : ∀ p ∈ expShellSquareIndex, ∑' k : ℕ, P {ω | -η * k < ξ * (hcirc ω (expShellMesh k)
      ⟨expShellMesh k * p.1, expShellMesh k * p.2⟩ + lqgQ γ * Real.log (expShellMesh k))} ≠ ⊤) :
    ∀ᵐ ω ∂P, ∑' k : ℕ, ENNReal.ofReal (Real.exp (ξ * α₀ * (k : ℝ))) *
      internalDiam (𝔇 (hC ω)) (Real.exp (-((k : ℝ) + 2))) (expShell k) ≠ ∞ := by
  -- for each grid index, the eventual bound on the internal diameter of the corresponding squares
  have hsq : ∀ᵐ ω ∂P, ∀ p : ℤ × ℤ, p ∈ expShellSquareIndex → ∀ᶠ k in atTop,
      ∀ u ∈ meshSquare (expShellMesh k) p, ∀ v ∈ meshSquare (expShellMesh k) p,
        internalMetric (𝔇 (hC ω)) (meshSquare (expShellMesh k) p) u v ≤
          ENNReal.ofReal (Real.exp (-η * k + ε * k)) := by
    refine ae_all_iff.2 fun p => ?_
    by_cases hp : p ∈ expShellSquareIndex
    · filter_upwards [h𝔇.ae_eventually_internalMetric_square_le hG hψ htail (t := expShellMesh)
        expShellMesh_pos (c := fun k => ⟨expShellMesh k * p.1, expShellMesh k * p.2⟩) (a := fun k => -η * k)
        (hcircTail p hp)] with ω hω _
      exact hω
    · exact Eventually.of_forall fun _ h => absurd h hp
  -- the geometric rate
  set η' : ℝ := (η - ε - ξ * α₀) / 2 with hη'
  have hη'0 : 0 < η' := by rw [hη']; linarith
  set N : ℕ := expShellSquareIndex.card with hN
  have hNev : ∀ᶠ k : ℕ in atTop, (N : ℝ) ≤ Real.exp (η' * k) := by
    filter_upwards [eventually_ge_atTop ⌈(N : ℝ) / η'⌉₊] with k hk
    have h1 : (N : ℝ) / η' ≤ k := (Nat.le_ceil _).trans (Nat.cast_le.2 hk)
    rw [div_le_iff₀ hη'0] at h1
    linarith [Real.add_one_le_exp (η' * k)]
  filter_upwards [h𝔇.ae_isEuclideanLengthMetric_self hG, hsq] with ω hD hω
  refine tsum_ofReal_exp_mul_mul_ne_top_of_eventually_le hη'0
    (fun k => hD.internalDiam_ne_top (isCompact_expShell k) (isPreconnected_expShell k) (Real.exp_pos _)) ?_
  filter_upwards [(eventually_all_finset expShellSquareIndex).2 hω, hNev] with k hk hNk
  calc internalDiam (𝔇 (hC ω)) (Real.exp (-((k : ℝ) + 2))) (expShell k)
      ≤ ∑ p ∈ expShellSquareIndex, ENNReal.ofReal (Real.exp (-η * k + ε * k)) :=
        hD.internalDiam_expShell_le_sum k hk
    _ = (N : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-η * k + ε * k)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal (Real.exp (η' * k)) * ENNReal.ofReal (Real.exp (-η * k + ε * k)) := by
        gcongr
        rw [← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal hNk
    _ = ENNReal.ofReal (Real.exp (-(ξ * α₀ + η') * k)) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        congr 2
        rw [hη']
        ring

end LatticeProb.LQG
