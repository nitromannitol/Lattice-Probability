import LatticeProb.Topology.DiskMobiusAction
import LatticeProb.Bonanno.LQGMetric.Complex.JordanMap

/-! # Holomorphic disk Möbius maps -/

set_option autoImplicit false

noncomputable section

open Set Metric
open QuantumZipper.CA

namespace LatticeProb

/-- Each disk Möbius parameter determines a holomorphic bijection of the open unit disk. -/
theorem diskMobiusParameters_holomorphic_bijOn (p : DiskMobiusParameters) :
    DifferentiableOn ℂ (fun z => (p.2 : ℂ) * diskMobius p.1 z) (ball 0 1) ∧
      BijOn (fun z => (p.2 : ℂ) * diskMobius p.1 z) (ball 0 1) (ball 0 1) := by
  have ha : ‖(p.1 : ℂ)‖ < 1 := mem_ball_zero_iff.mp p.1.property
  have hu : (p.2 : ℂ) ≠ 0 := by
    intro h
    have := p.2.property
    simp [h] at this
  have hrot : BijOn (fun z : ℂ => (p.2 : ℂ) * z) (ball 0 1) (ball 0 1) := by
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      rw [mem_ball_zero_iff, norm_mul, p.2.property, one_mul]
      exact mem_ball_zero_iff.mp hz
    · intro x hx y hy hxy
      exact mul_left_cancel₀ hu hxy
    · intro z hz
      refine ⟨(p.2 : ℂ)⁻¹ * z, ?_, ?_⟩
      · rw [mem_ball_zero_iff, norm_mul, norm_inv, p.2.property, inv_one, one_mul]
        exact mem_ball_zero_iff.mp hz
      · change (p.2 : ℂ) * ((p.2 : ℂ)⁻¹ * z) = z
        rw [← mul_assoc, mul_inv_cancel₀ hu, one_mul]
  constructor
  · exact ((differentiableOn_diskMobius ha).mono ball_subset_closedBall).const_mul (p.2 : ℂ)
  · exact hrot.comp (LQGMetric.JordanMap.jm_bijOn_diskMobius ha)

end LatticeProb
