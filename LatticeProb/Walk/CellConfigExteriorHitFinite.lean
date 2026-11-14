import LatticeProb.Walk.CellConfigExteriorFrontier
import LatticeProb.Bonanno.MatedCRTHarmonic.Markov.HitTime

/-!
# Finite exterior hits from frontier hitting

A cell walk that almost surely hits every enclosing ball frontier also almost
surely visits a representative outside any prescribed bounded set.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set ReflectedGMS ReflectedGMS.GMS
open MatedCRTHarmonic.Markov
open scoped NNReal ENNReal Pointwise

namespace LatticeProb.CellConfigInterpolation

/-- Hitting each enclosing ball frontier forces a finite hit of the cells whose
scaled representatives lie outside a prescribed bounded set. -/
theorem ae_exterior_hitTime_ne_top_of_ball_frontier_hits
    (H : CellConfig) (hH : H.IsCellConfiguration) (p : H.cells → Plane)
    (hp : ∀ K, p K ∈ (K.1 : Set Plane))
    {ε : ℝ≥0} (hε : 0 < ε) {U : Set Plane} (hU : Bornology.IsBounded U)
    (z : Plane) (Q : Measure (ℕ → H.cells))
    (hhit : ∀ R : ℝ, 0 < R → z ∈ Metric.ball (0 : Plane) R →
      ∀ᵐ ω ∂Q, hitTime {K : H.cells |
        ((K.1 : Set Plane) ∩ frontier (Metric.ball (0 : Plane) R)).Nonempty} ω ≠ ⊤) :
    ∀ᵐ ω ∂Q, hitTime {K : H.cells | (ε : ℝ) • p K ∉ U} ω ≠ ⊤ := by
  have he : (ε : ℝ) ≠ 0 := by exact_mod_cast hε.ne'
  let A : Set Plane := {w | (ε : ℝ) • w ∈ U}
  have hA : Bornology.IsBounded A := by
    apply (hU.smul₀ (ε : ℝ)⁻¹).subset
    intro w hw
    change (ε : ℝ) • w ∈ U at hw
    refine ⟨(ε : ℝ) • w, hw, ?_⟩
    simp only [smul_smul, inv_mul_cancel₀ he, one_smul]
  obtain ⟨R, hR, hz, hfront⟩ :=
    CellConfigBoundary.exists_ball_frontier_representatives_outside H hH p hp hA z
  filter_upwards [hhit R hR hz] with ω hω
  obtain ⟨n, hn⟩ := hitTime_ne_top_iff.mp hω
  apply hitTime_ne_top_iff.mpr
  exact ⟨n, hfront _ hn⟩

end LatticeProb.CellConfigInterpolation
end
