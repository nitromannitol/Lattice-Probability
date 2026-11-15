import LatticeProb.Walk.CountableFinitePrefixCurveLaw
import LatticeProb.Walk.AmbientRestrictedExitEdges

/-! # Finite-prefix curve comparison for restricted walks -/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open MatedCRTHarmonic.Markov
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigInterpolation

/-- A finite restricted walk has the adjacency needed for the finite-prefix
curve comparison up to its first exterior hit. -/
theorem levyProkhorov_continuousExitCurve_le_of_restricted_prefix (H : CellConfig)
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
    (v : R) (P : Measure (ℕ → H.cells))
    (hP : P = ((finiteConductanceRestriction
      (fun v w : H.cells => H.c v w) hsymm hnonneg hloop R).trajectoryLaw A hA v).map
      (fun q n => (q n : H.cells)))
    (E : Set (ℕ → H.cells)) (r s : ℝ≥0)
    (hbad : P E ≤ (r : ℝ≥0∞))
    (hgood : ∀ᵐ ω ∂P, ω ∉ E →
      (ε : ℝ) • p (ω 0) ∈ U ∧
      ∃ n, hitTime {K : H.cells | (ε : ℝ) • p K ∉ U} ω = (n + 1 : ℕ) ∧
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
  have hedges : ∀ᵐ ω ∂P, ∀ j : ℕ,
      (j : ℕ∞) < hitTime {K : H.cells | (ε : ℝ) • p K ∉ U} ω →
        H.Adj (ω j) (ω (j + 1)) := by
    rw [hP]
    change ∀ᵐ ω ∂_, ∀ j : ℕ,
      (j : ℕ∞) < hitTime {K : H.cells | (ε : ℝ) • p K ∈ U}ᶜ ω →
        0 < H.c (ω j) (ω (j + 1))
    exact (finiteConductanceRestriction_map_ae_pos_before_exit
        (fun v w : H.cells => H.c v w) hsymm hnonneg hloop R A
        {K : H.cells | (ε : ℝ) • p K ∈ U} hAB hA v)
  apply levyProkhorov_continuousExitCurve_le_of_prefix_countable H hH p hp hpos hε hm
    hU hconv P E r s hbad _ ν hsource
  filter_upwards [hgood, hedges] with ω hg he
  intro hω
  obtain ⟨hstart, n, hhit, hdiam⟩ := hg hω
  refine ⟨hstart, n, hhit, ?_, hdiam⟩
  intro j hj
  apply he j
  rw [hhit]
  exact_mod_cast Nat.lt_succ_of_le hj

end LatticeProb.CellConfigInterpolation
end
