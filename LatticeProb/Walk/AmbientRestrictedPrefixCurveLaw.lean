import LatticeProb.Walk.AccessibleRestrictedPrefixCurveLaw
import LatticeProb.Walk.RestrictedBoundaryAccessibility

/-! # Finite-prefix curve comparison from ambient paths -/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open MatedCRTHarmonic.Markov
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigInterpolation

/-- Ambient positive-conductance paths and neighbor retention supply boundary
accessibility in the finite-prefix curve comparison for a restricted walk. -/
theorem levyProkhorov_continuousExitCurve_le_of_ambient_paths (H : CellConfig)
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
    (hgood : ∀ᵐ ω ∂P, ω ∉ E →
      (ε : ℝ) • p (ω 0) ∈ U ∧
      ∀ n, hitTime {K : H.cells | (ε : ℝ) • p K ∉ U} ω = (n + 1 : ℕ) →
      ENNReal.ofReal (2 * ((ε : ℝ) * (Metric.diam ((ω n).1 : Set Plane) +
        Metric.diam ((ω (n + 1)).1 : Set Plane)))) < (r : ℝ≥0∞))
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
  have haccess := finiteConductanceRestriction_boundaryAccessible_of_ambient_paths
    (fun v w : H.cells => H.c v w) hsymm hnonneg hloop R A
    {K : H.cells | (ε : ℝ) • p K ∈ U} hAB hretain hpaths
  exact levyProkhorov_continuousExitCurve_le_of_accessible_restricted_prefix
    H hH hsymm hnonneg hloop p hp hpos hε hm hU hconv R A hAB hA haccess
    v P hP E r s hbad hgood ν hsource

end LatticeProb.CellConfigInterpolation
end
