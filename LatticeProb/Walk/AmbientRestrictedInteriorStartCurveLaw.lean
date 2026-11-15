import LatticeProb.Walk.AmbientRestrictedLocalMeshCurveLaw

/-! # Exit-curve comparison from an interior starting cell -/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open MatedCRTHarmonic.Markov
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigInterpolation

/-- The interior start condition in the local-mesh curve comparison follows
from the prescribed initial vertex of the finite restricted walk. -/
theorem levyProkhorov_continuousExitCurve_le_of_ambient_paths_local_mesh_of_mem (H : CellConfig)
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
    (v : R) (hv : v ∈ A) (P : Measure (ℕ → H.cells))
    (hP : P = ((finiteConductanceRestriction
      (fun v w : H.cells => H.c v w) hsymm hnonneg hloop R).trajectoryLaw A hA v).map
      (fun q n => (q n : H.cells)))
    (E : Set (ℕ → H.cells)) (r s : ℝ≥0)
    (hbad : P E ≤ (r : ℝ≥0∞))
    (W : Set Plane) (δ : ℝ) (hδ : 0 ≤ δ)
    (hbuffer : ∀ x ∈ U, Metric.closedBall x ((ε : ℝ) * δ) ⊆ W)
    (hmesh : ∀ K : H.cells, (∃ z ∈ (K.1 : Set Plane), (ε : ℝ) • z ∈ W) →
      Metric.diam (K.1 : Set Plane) ≤ δ)
    (hr : ENNReal.ofReal (4 * ((ε : ℝ) * δ)) < (r : ℝ≥0∞))
    (ν : Measure (BouRabeeGwynne.CurveSpace 2))
    (hsource : levyProkhorovEDist
      (P.map (stoppedPolygonalCurve (fun K => (ε : ℝ) • p K)
        {K : H.cells | (ε : ℝ) • p K ∈ U})) ν ≤ (s : ℝ≥0∞)) :
    levyProkhorovEDist
      (P.map (fun ω : ℕ → H.cells =>
        let g := ConstantStepInterpolation.continuousPlanePath m (fun n => (ε : ℝ) • p (ω n))
        CurveSpaceComparison.isometryEquiv 2
          (normalizedPrefixCurve g (continuousExitTime U 0 g).toNNReal))) ν ≤
      (r : ℝ≥0∞) + (s : ℝ≥0∞) := by
  classical
  have hmap : Measurable (fun q : ℕ → R => fun n => (q n : H.cells)) :=
    Measurable.of_eval fun n => (measurable_of_countable (fun x : R => (x : H.cells))).comp
      (measurable_pi_apply n)
  have hset : MeasurableSet {ω : ℕ → H.cells | ω 0 = (v : H.cells)} :=
    (measurableSet_singleton (v : H.cells)).preimage (measurable_pi_apply 0)
  have hstart_eq : ∀ᵐ ω ∂P, ω 0 = (v : H.cells) := by
    rw [hP]
    apply (ae_map_iff hmap.aemeasurable hset).2
    filter_upwards [(finiteConductanceRestriction
      (fun v w : H.cells => H.c v w) hsymm hnonneg hloop R).trajectoryLaw_ae_start A hA v] with q hq
    exact congrArg Subtype.val hq
  have hstart : ∀ᵐ ω ∂P, ω ∉ E → (ε : ℝ) • p (ω 0) ∈ U := by
    filter_upwards [hstart_eq] with ω hω
    intro _
    rw [hω]
    exact (hAB v).mp hv
  exact levyProkhorov_continuousExitCurve_le_of_ambient_paths_local_mesh
    H hH hsymm hnonneg hloop p hp hpos hε hm hU hconv R A hAB hA hretain hpaths
    v P hP E r s hbad hstart W δ hδ hbuffer hmesh hr ν hsource

end LatticeProb.CellConfigInterpolation
end
