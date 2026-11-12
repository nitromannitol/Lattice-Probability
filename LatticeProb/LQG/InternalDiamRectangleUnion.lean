import LatticeProb.LQG.InternalMetricFiniteUnion
import LatticeProb.Topology.RectangleSquareCover

/-!
# Internal diameters of finite unions of closed rectangles, from closed squares

Let `D` be a random metric on `ℂ` which is almost surely a Euclidean length metric. If every closed axis-parallel
square almost surely has finite internal diameter for `D`, then so does every preconnected finite union of closed
axis-parallel rectangles.

The union is a finite union of closed squares (`LatticeProb.Topology.exists_finset_closedSquare_cover_biUnion`), the
square events hold simultaneously almost surely because there are finitely many squares, and on that event the
internal diameter of a preconnected finite union of closed sets is at most the sum of the internal diameters of the
pieces (`IsEuclideanLengthMetric.exists_internalMetric_biUnion_le_ofReal`).

* `isClosed_of_isClosedSquare`: closed squares are closed.
* `ae_exists_internalMetric_rectangleUnion_le_ofReal`: the reduction.
-/

namespace LatticeProb.LQG

open MeasureTheory Set
open scoped ENNReal

/-- A closed axis-parallel square is a closed subset of `ℂ`. -/
theorem isClosed_of_isClosedSquare {Q : Set ℂ} (hQ : Topology.IsClosedSquare Q) : IsClosed Q := by
  obtain ⟨x, y, s, -, rfl⟩ := hQ
  exact isClosed_Icc.reProdIm isClosed_Icc

/-- **Internal diameters of finite unions of closed rectangles.** Let `D ω` be almost surely a Euclidean length
metric, and suppose that every closed square `Q` almost surely has finite internal diameter
`sup_{u, v ∈ Q} D_ω(u, v; Q)`. Then every preconnected finite union `K` of closed rectangles almost surely has finite
internal diameter. -/
theorem ae_exists_internalMetric_rectangleUnion_le_ofReal {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {D : Ω → ℂ → ℂ → ℝ} (hD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hSq : ∀ Q : Set ℂ, Topology.IsClosedSquare Q → ∀ᵐ ω ∂P, ∃ a : ℝ, ∀ u ∈ Q, ∀ v ∈ Q,
      internalMetric (D ω) Q u v ≤ ENNReal.ofReal a)
    {K : Set ℂ} (hK : ∃ F : Finset (Set ℂ), (∀ R ∈ F, Topology.IsClosedRectangle R) ∧ K = ⋃ R ∈ F, R)
    (hKc : IsPreconnected K) :
    ∀ᵐ ω ∂P, ∃ A : ℝ, ∀ u ∈ K, ∀ v ∈ K, internalMetric (D ω) K u v ≤ ENNReal.ofReal A := by
  obtain ⟨F, hF, rfl⟩ := hK
  obtain ⟨G, hG, hFG⟩ := Topology.exists_finset_closedSquare_cover_biUnion F hF
  rw [hFG] at hKc ⊢
  have hall : ∀ᵐ ω ∂P, ∀ Q ∈ G, ∃ a : ℝ, ∀ u ∈ Q, ∀ v ∈ Q,
      internalMetric (D ω) Q u v ≤ ENNReal.ofReal a :=
    (Filter.eventually_all_finset G).2 fun Q hQ => hSq Q (hG Q hQ).1
  filter_upwards [hD, hall] with ω hω hQ
  exact hω.exists_internalMetric_biUnion_le_ofReal (R := fun Q => Q) hKc
    (fun Q hQ => isClosed_of_isClosedSquare (hG Q hQ).1) hQ

end LatticeProb.LQG
