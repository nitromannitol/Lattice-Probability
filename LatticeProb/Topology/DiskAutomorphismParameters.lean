import LatticeProb.Topology.DiskMobiusAction
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.BasicsAutomorphisms

/-! # Parameters for holomorphic disk automorphisms -/

set_option autoImplicit false

noncomputable section

open Set Metric
open QuantumZipper.CA

namespace LatticeProb

/-- Every holomorphic bijection of the open unit disk has disk Möbius parameters. -/
theorem exists_diskMobiusParameters_of_bijOn {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1))
    (hbij : BijOn f (ball 0 1) (ball 0 1)) :
    ∃ p : DiskMobiusParameters, ∀ z ∈ ball (0 : ℂ) 1,
      f z = (p.2 : ℂ) * diskMobius p.1 z := by
  obtain ⟨a, ha, hfa⟩ := hbij.surjOn (mem_ball_self one_pos)
  have han : ‖a‖ < 1 := mem_ball_zero_iff.mp ha
  have hneg : ‖-a‖ < 1 := by simpa using han
  have hmap : MapsTo (diskMobius (-a)) (ball (0 : ℂ) 1) (ball 0 1) :=
    fun _ hz => diskMobius_mem_ball hneg hz
  have hleft : ∀ z ∈ ball (0 : ℂ) 1, diskMobius a (diskMobius (-a) z) = z := by
    intro z hz
    simpa using diskMobius_neg_diskMobius hneg (mem_ball_zero_iff.mp hz).le
  have hright : ∀ z ∈ ball (0 : ℂ) 1, diskMobius (-a) (diskMobius a z) = z := by
    intro z hz
    exact diskMobius_neg_diskMobius han (mem_ball_zero_iff.mp hz).le
  have hm : BijOn (diskMobius (-a)) (ball (0 : ℂ) 1) (ball 0 1) := by
    refine ⟨hmap, ?_, ?_⟩
    · intro x hx y hy hxy
      have h := congrArg (diskMobius a) hxy
      rwa [hleft x hx, hleft y hy] at h
    · intro y hy
      exact ⟨diskMobius a y, diskMobius_mem_ball han hy, hright y hy⟩
  have hg : DifferentiableOn ℂ (f ∘ diskMobius (-a)) (ball 0 1) :=
    hf.comp ((differentiableOn_diskMobius hneg).mono ball_subset_closedBall) hmap
  have hg0 : (f ∘ diskMobius (-a)) 0 = 0 := by
    simpa [Function.comp_def, diskMobius] using hfa
  obtain ⟨u, hu, hrot⟩ := exists_rotation_of_bijOn_ball hg (hbij.comp hm) hg0
  refine ⟨⟨⟨a, ha⟩, ⟨u, hu⟩⟩, ?_⟩
  intro z hz
  have h := hrot (diskMobius_mem_ball han hz)
  simpa [Function.comp_def, hright z hz] using h

/-- A continuous closed-disk extension has the same Möbius parameters on the boundary. -/
theorem exists_diskMobiusParameters_on_closedBall_of_bijOn {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1))
    (hbij : BijOn f (ball 0 1) (ball 0 1))
    (hc : ContinuousOn f (closedBall 0 1)) :
    ∃ p : DiskMobiusParameters, ∀ z ∈ closedBall (0 : ℂ) 1,
      f z = (p.2 : ℂ) * diskMobius p.1 z := by
  obtain ⟨p, hp⟩ := exists_diskMobiusParameters_of_bijOn hf hbij
  refine ⟨p, ?_⟩
  apply Set.EqOn.of_subset_closure hp hc
    (continuousOn_const.mul (differentiableOn_diskMobius
      (mem_ball_zero_iff.mp p.1.property)).continuousOn) ball_subset_closedBall
  rw [closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)]

end LatticeProb
