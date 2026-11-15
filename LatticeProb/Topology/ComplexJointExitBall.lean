import LatticeProb.Topology.FirstExitBallSelection
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Complex and planar first-exit ball witnesses -/

set_option autoImplicit false

open MeasureTheory Set Metric
open scoped ENNReal

namespace LatticeProb

/-- Two complex open-ball witnesses yield planar closed-ball success when both
planar exit clocks are finite. -/
theorem not_mem_firstExitBallFailure_of_complex_witnesses
    {β : Type*} (f : β → C(ℝ, EuclideanSpace ℝ (Fin 2))) (ω : β)
    (η : ℝ → ℂ) (hη : ∀ t, f ω t = Complex.orthonormalBasisOneI.repr (η t))
    {ε : ℝ} (hε : 0 < ε) (k : ℤ)
    (hfwd : openExitTime (fun s (_ : Unit) => f ω (0 + (s : ℝ)))
      (ball 0 (Real.exp (k : ℝ))) () ≠ ⊤)
    (hbwd : openExitTime (fun s (_ : Unit) => f ω (0 - (s : ℝ)))
      (ball 0 (Real.exp (k : ℝ))) () ≠ ⊤)
    (hwback : ∃ z, ball z (ε * Real.exp (k : ℝ)) ⊆
      η '' Icc (sSup {t : ℝ | t ≤ 0 ∧ η t ∉ ball 0 (Real.exp (k : ℝ))}) 0)
    (hwforward : ∃ z, ball z (ε * Real.exp (k : ℝ)) ⊆
      η '' Icc 0 (sInf {t : ℝ | 0 ≤ t ∧ η t ∉ ball 0 (Real.exp (k : ℝ))})) :
    ω ∉ firstExitBallFailure f ε k := by
  let i := Complex.orthonormalBasisOneI.repr
  have hout (t : ℝ) : f ω t ∉ ball 0 (Real.exp (k : ℝ)) ↔
      η t ∉ ball 0 (Real.exp (k : ℝ)) := by
    rw [hη t]
    simpa only [mem_ball, map_zero, i.dist_map] using
      (show i (η t) ∉ ball (i 0) (Real.exp (k : ℝ)) ↔
        η t ∉ ball 0 (Real.exp (k : ℝ)) by simp only [mem_ball, i.dist_map])
  have hleft : {t : ℝ | t ≤ 0 ∧ f ω t ∉ ball 0 (Real.exp (k : ℝ))} =
      {t : ℝ | t ≤ 0 ∧ η t ∉ ball 0 (Real.exp (k : ℝ))} := by
    ext t
    simp only [mem_ofPred_eq, hout]
  have hright : {t : ℝ | 0 ≤ t ∧ f ω t ∉ ball 0 (Real.exp (k : ℝ))} =
      {t : ℝ | 0 ≤ t ∧ η t ∉ ball 0 (Real.exp (k : ℝ))} := by
    ext t
    simp only [mem_ofPred_eq, hout]
  have hpos : 0 < ε * Real.exp (k : ℝ) := mul_pos hε (Real.exp_pos _)
  have transfer (A : Set ℝ) (z : ℂ)
      (hz : ball z (ε * Real.exp (k : ℝ)) ⊆ η '' A) :
      closedBall (i z) (ε * Real.exp (k : ℝ) / 2) ⊆ f ω '' A := by
    intro x hx
    have hx' : i.symm x ∈ ball z (ε * Real.exp (k : ℝ)) := by
      apply closedBall_subset_ball (half_lt_self hpos)
      simpa only [mem_closedBall, ← i.dist_map, i.apply_symm_apply] using hx
    obtain ⟨t, ht, ht'⟩ := hz hx'
    refine ⟨t, ht, ?_⟩
    calc
      f ω t = i (η t) := hη t
      _ = i (i.symm x) := congrArg i ht'
      _ = x := i.apply_symm_apply x
  obtain ⟨zb, hb⟩ := hwback
  obtain ⟨zf, hf⟩ := hwforward
  intro hfail
  apply hfail
  refine ⟨⟨hfwd, (half_pos hpos).le, i zf, ?_⟩,
    ⟨hbwd, (half_pos hpos).le, i zb, ?_⟩⟩
  · rw [hright]
    exact transfer _ _ hf
  · rw [hleft]
    exact transfer _ _ hb

end LatticeProb
