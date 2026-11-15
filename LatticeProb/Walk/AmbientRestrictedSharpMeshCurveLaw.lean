import LatticeProb.Walk.AmbientRestrictedInteriorStartCurveLaw

/-! # Exit-curve comparison with an exact local mesh bound -/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open MatedCRTHarmonic.Markov
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigInterpolation

/-- The continuous and polygonal exit-curve laws differ by at most the
scaled local mesh bound and the error in the polygonal source law. -/
theorem levyProkhorov_continuousExitCurve_le_of_ambient_paths_sharp_local_mesh (H : CellConfig)
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
    (s : ℝ≥0)
    (W : Set Plane) (δ : ℝ) (hδ : 0 ≤ δ)
    (hbuffer : ∀ x ∈ U, Metric.closedBall x ((ε : ℝ) * δ) ⊆ W)
    (hmesh : ∀ K : H.cells, (∃ z ∈ (K.1 : Set Plane), (ε : ℝ) • z ∈ W) →
      Metric.diam (K.1 : Set Plane) ≤ δ)
    (ν : Measure (BouRabeeGwynne.CurveSpace 2))
    (hsource : levyProkhorovEDist
      (P.map (stoppedPolygonalCurve (fun K => (ε : ℝ) • p K)
        {K : H.cells | (ε : ℝ) • p K ∈ U})) ν ≤ (s : ℝ≥0∞)) :
    levyProkhorovEDist
      (P.map (fun ω : ℕ → H.cells =>
        let g := ConstantStepInterpolation.continuousPlanePath m (fun n => (ε : ℝ) • p (ω n))
        CurveSpaceComparison.isometryEquiv 2
          (normalizedPrefixCurve g (continuousExitTime U 0 g).toNNReal))) ν ≤
      ENNReal.ofReal (4 * ((ε : ℝ) * δ)) + (s : ℝ≥0∞) := by
  classical
  let q : ℝ≥0 := ⟨4 * ((ε : ℝ) * δ), by positivity⟩
  have hq : (q : ℝ≥0∞) = ENNReal.ofReal (4 * ((ε : ℝ) * δ)) := by
    exact ENNReal.coe_nnreal_eq q
  refine ENNReal.le_of_forall_pos_le_add fun t ht _ => ?_
  have hstrict : ENNReal.ofReal (4 * ((ε : ℝ) * δ)) < ((q + t : ℝ≥0) : ℝ≥0∞) := by
    rw [← hq]
    exact_mod_cast lt_add_of_pos_right q ht
  have h := levyProkhorov_continuousExitCurve_le_of_ambient_paths_local_mesh_of_mem
    H hH hsymm hnonneg hloop p hp hpos hε hm hU hconv R A hAB hA hretain hpaths
    v hv P hP ∅ (q + t) s (by simp) W δ hδ hbuffer hmesh hstrict ν hsource
  simpa only [hq, ENNReal.coe_add, add_assoc, add_comm, add_left_comm] using h

end LatticeProb.CellConfigInterpolation
end
