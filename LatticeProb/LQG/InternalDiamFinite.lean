import LatticeProb.LQG.InternalMetricCompactFinite

/-! # Finite internal diameter of a compact connected set

For a Euclidean length metric `D` on `ℂ`, a compact preconnected set `A` and `δ > 0`, the internal diameter
`diam^δ_D(A) = sup_{x, y ∈ A} D(x, y; B_δ(A))` is finite. The `δ`-neighbourhood `B_δ(A)` is open and contains `A`, so
this is the bound for a compact preconnected subset of an open set, applied to `U = B_δ(A)`.

Main result:
* `IsEuclideanLengthMetric.internalDiam_ne_top`.
-/

namespace LatticeProb.LQG

open Set
open scoped ENNReal

/-- **Finite internal diameter.** For a Euclidean length metric `D`, a compact preconnected set `A` and `δ > 0`, the
internal diameter `diam^δ_D(A)` is finite. -/
theorem IsEuclideanLengthMetric.internalDiam_ne_top {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {A : Set ℂ}
    (hA : IsCompact A) (hAc : IsPreconnected A) {δ : ℝ} (hδ : 0 < δ) : internalDiam D δ A ≠ ⊤ := by
  obtain ⟨B, hB⟩ := hD.exists_internalMetric_le_ofReal_of_isCompact hA hAc Metric.isOpen_thickening
    (Metric.self_subset_thickening hδ A)
  refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top (b := ENNReal.ofReal B) ?_
  unfold internalDiam
  exact iSup₂_le fun x hx => iSup₂_le fun y hy => hB x hx y hy

end LatticeProb.LQG
