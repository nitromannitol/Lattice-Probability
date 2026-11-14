import LatticeProb.Walk.CellConfigExteriorFrontier
import LatticeProb.Bonanno.MatedCRTHarmonic.Markov.HitTime

/-! # Simultaneous exterior hits for shifted cell walks -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set ReflectedGMS ReflectedGMS.GMS
open MatedCRTHarmonic.Markov
open scoped NNReal ENNReal Pointwise

namespace LatticeProb.CellConfigInterpolation

/-- Simultaneous shifted hits of enclosing ball frontiers imply simultaneous
exterior hits for every bounded set, positive scale, and cell representative. -/
theorem ae_exterior_hitTime_ne_top_all_shifts_of_ball_frontier_hits
    (H : CellConfig) (hH : H.IsCellConfiguration) (Q : Measure (ℕ → H.cells))
    (hhit : ∀ᵐ ω ∂Q, ∀ R : ℝ, ∀ k : ℕ,
      (((ω k).1 : Set Plane) ∩ Metric.ball (0 : Plane) R).Nonempty →
      hitTime {K : H.cells |
        ((K.1 : Set Plane) ∩ frontier (Metric.ball (0 : Plane) R)).Nonempty}
        (fun n => ω (k + n)) ≠ ⊤) :
    ∀ᵐ ω ∂Q, ∀ k : ℕ, ∀ p : H.cells → Plane,
      (∀ K, p K ∈ (K.1 : Set Plane)) → ∀ a : ℝ≥0, 0 < a →
      ∀ U : Set Plane, Bornology.IsBounded U →
      hitTime {K : H.cells | (a : ℝ) • p K ∉ U} (fun n => ω (k + n)) ≠ ⊤ := by
  filter_upwards [hhit] with ω hω
  intro k p hp a ha U hU
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  let A : Set Plane := {z | (a : ℝ) • z ∈ U}
  have hA : Bornology.IsBounded A := by
    apply (hU.smul₀ (a : ℝ)⁻¹).subset
    intro z hz
    change (a : ℝ) • z ∈ U at hz
    refine ⟨(a : ℝ) • z, hz, ?_⟩
    simp only [smul_smul, inv_mul_cancel₀ ha0, one_smul]
  obtain ⟨R, _, hz, hfront⟩ :=
    LatticeProb.CellConfigBoundary.exists_ball_frontier_representatives_outside
      H hH p hp hA (p (ω k))
  have hstart : (((ω k).1 : Set Plane) ∩ Metric.ball (0 : Plane) R).Nonempty :=
    ⟨p (ω k), hp _, hz⟩
  obtain ⟨n, hn⟩ := hitTime_ne_top_iff.mp (hω R k hstart)
  exact hitTime_ne_top_iff.mpr ⟨n, hfront _ hn⟩

end LatticeProb.CellConfigInterpolation
end
