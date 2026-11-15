import LatticeProb.Topology.AreaCurveGraphBoundary
import LatticeProb.Walk.ConstantStepGraphExit

/-! # Boundary hits for graphs embedded by area-parametrized curves -/

set_option autoImplicit false
noncomputable section

open Filter Set Metric MeasureTheory MatedCRTHarmonic.Markov
open scoped ENNReal Topology

namespace LatticeProb

/-- A graph inner-boundary vertex lies within the crossing-edge bound of the
frontier of the open domain traced by the curve segment. -/
theorem infDist_area_curve_innerBoundary_le
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (η : ℝ → E) (μ : Measure E) (hη : Continuous η)
    (hμ : ∀ a b, a < b → μ (η '' Icc a b) = ENNReal.ofReal (b - a))
    (G : SimpleGraph V) (r : V → ℝ) {U : Set E} (hU : IsOpen U)
    {a b : ℝ} (hab : a < b) (himage : η '' Icc a b = closure U)
    {v : V} (hv : v ∈ Graph.innerBoundary G {v | r v ∈ Icc a b}) {δ : ℝ}
    (hbound : ∀ x y, G.Adj x y → r x ∈ Icc a b → r y ∉ Icc a b →
      dist (η (r x)) (η (r y)) ≤ δ) :
    infDist (η (r v)) (frontier U) ≤ δ := by
  obtain ⟨hv, w, hw, hvw⟩ := hv
  obtain ⟨z, hz, hd⟩ := area_curve_innerBoundary_near_frontier η μ hη hμ G r hU hab
    himage hv hvw hw hbound
  exact (infDist_le_dist_of_mem hz).trans hd

/-- The first inner-boundary hit of a finite graph exit is close to the
frontier, provided every edge crossing the segment interval is short. -/
theorem infDist_area_curve_boundary_hit_le
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (η : ℝ → E) (μ : Measure E) (hη : Continuous η)
    (hμ : ∀ a b, a < b → μ (η '' Icc a b) = ENNReal.ofReal (b - a))
    (G : SimpleGraph V) (r : V → ℝ) {U : Set E} (hU : IsOpen U)
    {a b : ℝ} (hab : a < b) (himage : η '' Icc a b = closure U)
    (x : ℕ → V) (hstart : r (x 0) ∈ Icc a b)
    (hstep : ∀ n, x (n + 1) = x n ∨ G.Adj (x n) (x (n + 1)))
    {N : ℕ} (hexit : hitTime {v | r v ∈ Icc a b}ᶜ x = N) {δ : ℝ}
    (hbound : ∀ v w, G.Adj v w → r v ∈ Icc a b → r w ∉ Icc a b →
      dist (η (r v)) (η (r w)) ≤ δ) :
    infDist (η (r (x (hitTime (Graph.innerBoundary G {v | r v ∈ Icc a b}) x).toNat)))
      (frontier U) ≤ δ := by
  let A : Set V := {v | r v ∈ Icc a b}
  have hlt := ConstantStepInterpolation.innerBoundary_hitTime_lt_vertex_exit G A x hstart hstep hexit
  have hfin : hitTime (Graph.innerBoundary G A) x ≠ ⊤ := ne_top_of_lt (lt_of_lt_of_le hlt le_top)
  have hv : x (hitTime (Graph.innerBoundary G A) x).toNat ∈ Graph.innerBoundary G A :=
    (hitTime_eq_coe_iff.mp (coe_toNat_hitTime hfin).symm).1
  exact infDist_area_curve_innerBoundary_le η μ hη hμ G r hU hab himage hv hbound

/-- Vanishing crossing-edge bounds force the first inner-boundary vertices to
approach the frontier. -/
theorem tendsto_infDist_area_curve_boundary_hit
    {E V α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {l : Filter α}
    (η : ℝ → E) (μ : Measure E) (hη : Continuous η)
    (hμ : ∀ a b, a < b → μ (η '' Icc a b) = ENNReal.ofReal (b - a))
    (G : α → SimpleGraph V) (r : α → V → ℝ) {U : Set E} (hU : IsOpen U)
    {a b : ℝ} (hab : a < b) (himage : η '' Icc a b = closure U)
    (x : α → ℕ → V) (N : α → ℕ) (δ : α → ℝ)
    (hstart : ∀ i, r i (x i 0) ∈ Icc a b)
    (hstep : ∀ i n, x i (n + 1) = x i n ∨ (G i).Adj (x i n) (x i (n + 1)))
    (hexit : ∀ i, hitTime {v | r i v ∈ Icc a b}ᶜ (x i) = N i)
    (hbound : ∀ i v w, (G i).Adj v w → r i v ∈ Icc a b → r i w ∉ Icc a b →
      dist (η (r i v)) (η (r i w)) ≤ δ i)
    (hδ : Tendsto δ l (𝓝 0)) :
    Tendsto (fun i => infDist
      (η (r i (x i (hitTime (Graph.innerBoundary (G i) {v | r i v ∈ Icc a b}) (x i)).toNat)))
      (frontier U)) l (𝓝 0) := by
  apply squeeze_zero (fun _ => infDist_nonneg) (fun i => ?_) hδ
  exact infDist_area_curve_boundary_hit_le η μ hη hμ (G i) (r i) hU hab himage
    (x i) (hstart i) (hstep i) (hexit i) (hbound i)

end LatticeProb
end
