import LatticeProb.LQG.CornerSquareWeylDiameter
import LatticeProb.LQG.InternalMetricSquareTailWeyl
import LatticeProb.LQG.InternalMetricFiniteUnionOfTriangle
import LatticeProb.Topology.SquareCoverAtZero

/-!
# Internal diameter of a closed square through the origin for a γ-LQG metric with a log singularity

Let `𝔇` be a γ-LQG metric, `h` a whole-plane GFF, `ξ > 0` and `α < Q`, and let `E = |·|^{-αξ} · D_h` be the Weyl
scaling `e^{ξ f} · D_h` with `f = -α log |·|`. Then almost surely every closed square `[x, x + r] × [y, y + r]` which
contains the origin has finite internal `E`-diameter.

This is the almost sure form of the last paragraph of the proof of Proposition 3.17 in Ding, Dubédat, Dunlap and
Falconet, "Tightness of Liouville first passage percolation for γ ∈ (0, 2)", for squares through the origin. The
square is the union of finitely many closed squares of one side, each of which either avoids the origin, where the
weight `f` is continuous and the internal diameter is finite by the diameter tail of closed squares, or has the origin
as a corner, where the internal diameter is finite by the dyadic shell chaining to the corner. The internal diameter of
the preconnected union is at most the sum of those of the pieces.

## Main statements

* `IsLQGMetric.ae_internalMetric_weylScaling_closedSquare_le_of_zero_mem`
-/

open MeasureTheory Filter Set LatticeProb.Gauss
open scoped ENNReal

namespace LatticeProb.LQG

variable {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Finite internal diameter of a closed square through the origin for `|·|^{-αξ} · D_h`.** Let `𝔇` be a γ-LQG
metric with `ξ > 0`, `h` a whole-plane GFF, `α < Q`, and `0 < δ < θ < ξ (Q - 2) log 2`. Suppose that for every
whole-plane GFF `h'` on the same probability space and every `n`, the probability that the unit square has no half
crossings of `D_{h'}`-length at most `e^{δ n}` is at most `p n`, where `∑ₙ 4ⁿ p n < ∞`. Let `E` be a random function
which is almost surely the Weyl scaling `e^{-αξ log |·|} · D_h`. Then for every closed square
`S = [x, x + r] × [y, y + r]` with `r > 0` containing the origin, almost surely there is a real `A` with
`E(u, v; S) ≤ A` for all `u, v ∈ S`. -/
theorem IsLQGMetric.ae_internalMetric_weylScaling_closedSquare_le_of_zero_mem
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (hG : IsWholePlaneGFF P hC hcirc) (hξ : 0 < ξ) {θ δ : ℝ}
    (hθ : θ < ξ * (lqgQ γ - 2) * Real.log 2) (hδ : δ < θ) (hδ0 : 0 < δ) {p : ℕ → ℝ≥0∞}
    (huniv : ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC' hcirc' →
      ∀ n : ℕ, P {ω | ¬ HasShortHalfCrossings (𝔇 (hC' ω)) 0 1 0 1 (ENNReal.ofReal (Real.exp (δ * n)))} ≤ p n)
    (hp : ∑' n, 4 ^ n * p n ≠ ⊤) {α : ℝ} (hα : α < lqgQ γ)
    {x y r : ℝ} (hr : 0 < r) (h0 : (0 : ℂ) ∈ Icc x (x + r) ×ℂ Icc y (y + r)) {E : Ω → ℂ → ℂ → ℝ}
    (hE : ∀ᵐ ω ∂P, ∀ u v,
      ENNReal.ofReal (E ω u v) = weylScaling (𝔇 (hC ω)) ξ (fun w => -α * Real.log ‖w‖) u v) :
    ∀ᵐ ω ∂P, ∃ A : ℝ, ∀ u ∈ Icc x (x + r) ×ℂ Icc y (y + r), ∀ v ∈ Icc x (x + r) ×ℂ Icc y (y + r),
      internalMetric (E ω) (Icc x (x + r) ×ℂ Icc y (y + r)) u v ≤ ENNReal.ofReal A := by
  obtain ⟨s, Pc, hs, hU, hPc⟩ := LatticeProb.Topology.exists_finset_square_cover_of_zero_mem hr h0
  -- one almost sure bound per piece: away from the origin, or at a corner
  have hpiece : ∀ q ∈ Pc, ∀ᵐ ω ∂P, ∃ a : ℝ, ∀ u ∈ Icc q.1 (q.1 + s) ×ℂ Icc q.2 (q.2 + s),
      ∀ v ∈ Icc q.1 (q.1 + s) ×ℂ Icc q.2 (q.2 + s),
        internalMetric (E ω) (Icc q.1 (q.1 + s) ×ℂ Icc q.2 (q.2 + s)) u v ≤ ENNReal.ofReal a := by
    intro q hq
    rcases hPc q hq with hq0 | ⟨ha, hb⟩
    · refine h𝔇.ae_exists_internalMetric_closedSquare_le_of_weylScaling_continuousOn hG hs hξ hθ hδ huniv hp hE ?_
      refine continuousOn_const.mul (continuous_norm.continuousOn.log fun w hw => ?_)
      exact norm_ne_zero_iff.2 fun h => hq0 (h ▸ hw)
    · filter_upwards [h𝔇.ae_internalMetric_weylScaling_cornerSquare_le_of_shortHalfCrossings hG hξ hθ hδ hδ0 huniv
        hp hα hs ha hb, hE] with ω hω hEω
      obtain ⟨a, ha⟩ := hω
      exact ⟨a, ha (E ω) hEω⟩
  have hK : IsPreconnected (⋃ q ∈ Pc, Icc q.1 (q.1 + s) ×ℂ Icc q.2 (q.2 + s)) := by
    rw [hU]
    exact (LatticeProb.Topology.convex_reProdIm (convex_Icc _ _) (convex_Icc _ _)).isPreconnected
  filter_upwards [(eventually_all_finset Pc).2 hpiece, h𝔇.ae_isEuclideanLengthMetric_self hG, hE]
    with ω hω hD hEω
  have htri : ∀ u v w, ENNReal.ofReal (E ω u w) ≤ ENNReal.ofReal (E ω u v) + ENNReal.ofReal (E ω v w) :=
    fun u v w => by
      rw [hEω, hEω, hEω]
      exact hD.weylScaling_triangle ξ _ u v w
  rw [← hU]
  exact exists_internalMetric_biUnion_le_ofReal_of_ofReal_triangle htri
    (R := fun q : ℝ × ℝ => Icc q.1 (q.1 + s) ×ℂ Icc q.2 (q.2 + s)) hK
    (fun q _ => isClosed_Icc.reProdIm isClosed_Icc) hω

end LatticeProb.LQG
