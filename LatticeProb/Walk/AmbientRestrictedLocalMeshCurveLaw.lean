import LatticeProb.Walk.AmbientRestrictedPrefixCurveLaw
import LatticeProb.Walk.LocalMeshFirstExitError

/-! # Restricted exit-curve comparison under a local mesh bound -/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open MatedCRTHarmonic.Markov
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigInterpolation

/-- A local mesh bound controls the final edge in the restricted-walk
comparison of polygonal and continuous exit-curve laws. -/
theorem levyProkhorov_continuousExitCurve_le_of_ambient_paths_local_mesh (H : CellConfig)
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
    (v : R) (P : Measure (ℕ → H.cells))
    (hP : P = ((finiteConductanceRestriction
      (fun v w : H.cells => H.c v w) hsymm hnonneg hloop R).trajectoryLaw A hA v).map
      (fun q n => (q n : H.cells)))
    (E : Set (ℕ → H.cells)) (r s : ℝ≥0)
    (hbad : P E ≤ (r : ℝ≥0∞))
    (hstart : ∀ᵐ ω ∂P, ω ∉ E → (ε : ℝ) • p (ω 0) ∈ U)
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
  have hedges : ∀ᵐ ω ∂P, ∀ j : ℕ,
      (j : ℕ∞) < hitTime {K : H.cells | (ε : ℝ) • p K ∉ U} ω →
        H.Adj (ω j) (ω (j + 1)) := by
    rw [hP]
    change ∀ᵐ ω ∂_, ∀ j : ℕ,
      (j : ℕ∞) < hitTime {K : H.cells | (ε : ℝ) • p K ∈ U}ᶜ ω →
        0 < H.c (ω j) (ω (j + 1))
    exact finiteConductanceRestriction_map_ae_pos_before_exit
      (fun v w : H.cells => H.c v w) hsymm hnonneg hloop R A
      {K : H.cells | (ε : ℝ) • p K ∈ U} hAB hA v
  apply levyProkhorov_continuousExitCurve_le_of_ambient_paths H hH hsymm hnonneg
    hloop p hp hpos hε hm hU hconv R A hAB hA hretain hpaths v P hP E r s hbad _ ν hsource
  filter_upwards [hstart, hedges] with ω hs he
  intro hω
  refine ⟨hs hω, ?_⟩
  intro n hn
  apply firstExit_finalEdge_error_lt_of_scaled_local_mesh H hH p hp U W (ε : ℝ) δ
    (by positivity) hδ hbuffer hmesh ω n hn
  · apply he n
    rw [hn]
    exact_mod_cast Nat.lt_succ_self n
  · exact hr

end LatticeProb.CellConfigInterpolation
end
