import LatticeProb.Walk.CellConfigExteriorFrontier
import LatticeProb.Walk.CellConfigFiniteExit
import LatticeProb.Bonanno.MatedCRTHarmonic.Markov.HitTime

/-!
# Finite exit from frontier hitting

An interpolated cell walk exits bounded sets in finite time if it almost surely
reaches the frontier cells of every ball containing a fixed point.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open MatedCRTHarmonic.Markov
open scoped NNReal ENNReal Pointwise

namespace LatticeProb.CellConfigInterpolation

/-- Frontier hitting and unbounded jump times force finite exit from a bounded set. -/
theorem ae_continuousExitTime_ne_top_of_ball_frontier_hits
    (H : CellConfig) (hH : H.IsCellConfiguration) (p : H.cells → Plane)
    (hp : ∀ K, p K ∈ (K.1 : Set Plane)) (hpos : ∀ K, 0 < H.holding K)
    {ε : ℝ≥0} (hε : 0 < ε) {U : Set Plane} (hU : Bornology.IsBounded U)
    (z : Plane) (Q : Measure (ℕ → H.cells))
    (hunb : ∀ᵐ ω ∂Q, H.JumpTimesUnbounded ω)
    (hhit : ∀ R : ℝ, 0 < R → z ∈ Metric.ball (0 : Plane) R →
      ∀ᵐ ω ∂Q, hitTime {K : H.cells |
        ((K.1 : Set Plane) ∩ frontier (Metric.ball (0 : Plane) R)).Nonempty} ω ≠ ⊤) :
    ∀ᵐ ω ∂Q, continuousExitTime U 0 (H.interpolatedWalk p ε ω) ≠ ∞ := by
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
  apply ae_continuousExitTime_ne_top_of_visit H p hpos hε U Q hunb
  filter_upwards [hhit R hR hz] with ω hω
  let I : Set H.cells := {K | ((K.1 : Set Plane) ∩
    frontier (Metric.ball (0 : Plane) R)).Nonempty}
  have ht : hitTime I ω = (hitTime I ω).toNat := (coe_toNat_hitTime hω).symm
  have hmem : ω (hitTime I ω).toNat ∈ I := (hitTime_eq_coe_iff.mp ht).1
  exact ⟨(hitTime I ω).toNat, hfront _ hmem⟩

/-- A recurrent cell walk exits a bounded set in finite time when it almost surely
hits the frontier cells of every ball containing a fixed point. -/
theorem ae_continuousExitTime_ne_top_of_recurrent_ball_frontier_hits
    (H : CellConfig) (hH : H.IsCellConfiguration) (p : H.cells → Plane)
    (hp : ∀ K, p K ∈ (K.1 : Set Plane)) (hpos : ∀ K, 0 < H.holding K)
    (hrec : H.Recurrent) {ε : ℝ≥0} (hε : 0 < ε) {U : Set Plane}
    (hU : Bornology.IsBounded U) (z : Plane) {x : H.cells}
    {Q : Measure (ℕ → H.cells)} (hQ : H.IsSRWLaw x Q)
    (hhit : ∀ R : ℝ, 0 < R → z ∈ Metric.ball (0 : Plane) R →
      ∀ᵐ ω ∂Q, hitTime {K : H.cells |
        ((K.1 : Set Plane) ∩ frontier (Metric.ball (0 : Plane) R)).Nonempty} ω ≠ ⊤) :
    ∀ᵐ ω ∂Q, continuousExitTime U 0 (H.interpolatedWalk p ε ω) ≠ ∞ :=
  ae_continuousExitTime_ne_top_of_ball_frontier_hits H hH p hp hpos hε hU z Q
    (CellConfigWalk.ae_jumpTimesUnbounded_of_recurrent hrec hpos hQ) hhit

end LatticeProb.CellConfigInterpolation
end
