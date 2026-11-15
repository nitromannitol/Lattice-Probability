import LatticeProb.Walk.FiniteSourceSharpMeshCurveLaw
import LatticeProb.Walk.NestedFrontierStoppedBrownianLaw

/-! # Exit-curve comparison for nested finite-network laws -/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open MatedCRTHarmonic.Markov
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigInterpolation

/-- A stopped Brownian comparison under a larger active law controls the
continuous exit curve of the nested active law, with explicit error bounds. -/
theorem levyProkhorov_continuousExitCurve_le_of_nested_frontier_finite_source (H : CellConfig)
    [Countable H.cells] [MeasurableSpace H.cells] [MeasurableSingletonClass H.cells]
    (hH : H.IsCellConfiguration)
    (hsymm : ∀ v w : H.cells, H.c v w = H.c w v)
    (hnonneg : ∀ v w : H.cells, 0 ≤ H.c v w)
    (hloop : ∀ v : H.cells, H.c v v = 0)
    (p : H.cells → Plane) (hp : ∀ K, p K ∈ (K.1 : Set Plane))
    (hpos : ∀ K, 0 < H.holding K) {ε m : ℝ≥0} (hε : 0 < ε) (hm : 0 < m)
    {U : Set Plane} (hU : IsOpen U) (hconv : Convex ℝ U)
    (R : Set H.cells) [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R]
    (A : Set R)
    (hAB : ∀ v : R, v ∈ A ↔ (ε : ℝ) • p v ∈ U)
    (hA : ∀ v ∈ A, 0 < (finiteConductanceRestriction
      (fun v w : H.cells => H.c v w) hsymm hnonneg hloop R).totalConductance v)
    (hretain : ∀ v ∈ A, ∀ w, w ∉ R → H.c v w = 0)
    (hpaths : ∀ v ∈ A, ∃ w : H.cells, (ε : ℝ) • p w ∉ U ∧
      Relation.ReflTransGen (fun x y : H.cells => 0 < H.c x y) (v : H.cells) w)
    (C : Set R) (hAC : A ⊆ C)
    (hC : ∀ v ∈ C, 0 < (finiteConductanceRestriction
      (fun v w : H.cells => H.c v w) hsymm hnonneg hloop R).totalConductance v)
    (v : R) (hv : v ∈ A) (P : Measure (ℕ → H.cells))
    (hP : P = ((finiteConductanceRestriction
      (fun v w : H.cells => H.c v w) hsymm hnonneg hloop R).trajectoryLaw A hA v).map
      (fun q n => (q n : H.cells)))
    (W : Set Plane) (δ : ℝ) (hδ : 0 ≤ δ)
    (hbuffer : ∀ x ∈ U, Metric.closedBall x ((ε : ℝ) * δ) ⊆ W)
    (hmesh : ∀ K : H.cells, (∃ z ∈ (K.1 : Set Plane), (ε : ℝ) • z ∈ W) →
      Metric.diam (K.1 : Set Plane) ≤ δ)
    (q : R → Plane) (z : Plane) (μ : Measure (BrownianPath 2))
    (d : ℝ) (r s : ℝ≥0)
    (hd : ∀ x : R, dist ((ε : ℝ) • p x) (q x) ≤ d) (hdr : d < (r : ℝ))
    (n : ℕ)
    (hbound : ((finiteConductanceRestriction
      (fun v w : H.cells => H.c v w) hsymm hnonneg hloop R).trajectoryLaw C hC v)
        {ω | (n : WithTop ℕ) ≤ FiniteConductanceNetwork.exitTime (q ⁻¹' U) ω} +
      ∑ k ∈ Finset.range n, ((finiteConductanceRestriction
        (fun v w : H.cells => H.c v w) hsymm hnonneg hloop R).trajectoryLaw C hC v)
        {ω | q (ω k) ∈ Metric.thickening (r : ℝ) (frontier U)} ≤ (r : ℝ≥0∞))
    (hsource : levyProkhorovEDist
      (((finiteConductanceRestriction
        (fun v w : H.cells => H.c v w) hsymm hnonneg hloop R).trajectoryLaw C hC v).map
        (stoppedPolygonalCurve q (q ⁻¹' U))) (stoppedBrownianLaw U z μ) ≤ (s : ℝ≥0∞)) :
    levyProkhorovEDist
      (P.map (fun ω : ℕ → H.cells =>
        let g := ConstantStepInterpolation.continuousPlanePath m (fun n => (ε : ℝ) • p (ω n))
        CurveSpaceComparison.isometryEquiv 2
          (normalizedPrefixCurve g (continuousExitTime U 0 g).toNNReal))) (stoppedBrownianLaw U z μ) ≤
      ENNReal.ofReal (4 * ((ε : ℝ) * δ)) + ((r + s : ℝ≥0) : ℝ≥0∞) := by
  have hsub : (fun x : R => (ε : ℝ) • p x) ⁻¹' U ⊆ C := by
    intro x hx
    exact hAC ((hAB x).2 hx)
  have hB : ∀ x ∈ (fun x : R => (ε : ℝ) • p x) ⁻¹' U,
      0 < (finiteConductanceRestriction
        (fun v w : H.cells => H.c v w) hsymm hnonneg hloop R).totalConductance x := by
    intro x hx
    exact hA x ((hAB x).2 hx)
  have htransfer := levyProkhorov_nested_stoppedBrownian_le_of_frontier_cutoff
    (finiteConductanceRestriction (fun v w : H.cells => H.c v w)
      hsymm hnonneg hloop R) C hC v (fun x : R => (ε : ℝ) • p x) q U z
      hsub hB μ d r hd hdr n hbound (s : ℝ≥0∞) hsource
  have hEq : A = (fun x : R => (ε : ℝ) • p x) ⁻¹' U := by
    ext x
    exact hAB x
  have htransfer' : levyProkhorovEDist
      (((finiteConductanceRestriction
        (fun v w : H.cells => H.c v w) hsymm hnonneg hloop R).trajectoryLaw A hA v).map
        (stoppedPolygonalCurve (fun x : R => (ε : ℝ) • p x)
          {x : R | (ε : ℝ) • p x ∈ U})) (stoppedBrownianLaw U z μ) ≤
        ((r + s : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_add]
    subst A
    exact htransfer
  exact levyProkhorov_continuousExitCurve_le_of_finite_source_sharp_local_mesh
    H hH hsymm hnonneg hloop p hp hpos hε hm hU hconv R A hAB hA hretain hpaths
    v hv P hP (r + s) W δ hδ hbuffer hmesh (stoppedBrownianLaw U z μ) htransfer'

end LatticeProb.CellConfigInterpolation
end
