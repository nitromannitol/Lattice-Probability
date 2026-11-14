import LatticeProb.Analysis.ConeJointExitEndpoint
import LatticeProb.Analysis.ConeExitReversal

/-!
# Endpoint of a joint forward exit

Time reversal transfers the equal-endpoint barrier at the joint backward exit
to the joint forward exit.
-/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- Continuous coordinates with separate future strict drops have an
equal-endpoint closed barrier in one coordinate up to their joint exit. -/
theorem jointForwardExit_closed_barrier {X Y : ℝ → ℝ} {s : ℝ}
    (hX : Continuous X) (hY : Continuous Y)
    (hx : ∃ r > s, X r < X s) (hy : ∃ r > s, Y r < Y s) :
    (X (coneJointExit X Y s) = X s ∧
      ∀ t ∈ Icc s (coneJointExit X Y s), X s ≤ X t) ∨
    (Y (coneJointExit X Y s) = Y s ∧
      ∀ t ∈ Icc s (coneJointExit X Y s), Y s ≤ Y t) := by
  let Xr : ℝ → ℝ := fun t => X (-t)
  let Yr : ℝ → ℝ := fun t => Y (-t)
  have hx' : ∃ r < -s, Xr r < Xr (-s) := by
    obtain ⟨r, hrs, hr⟩ := hx
    exact ⟨-r, by linarith, by simpa [Xr] using hr⟩
  have hy' : ∃ r < -s, Yr r < Yr (-s) := by
    obtain ⟨r, hrs, hr⟩ := hy
    exact ⟨-r, by linarith, by simpa [Yr] using hr⟩
  have hrev : coneJointExitBackward Xr Yr (-s) = -coneJointExit X Y s := by
    have h : coneJointExit X Y s = -coneJointExitBackward Xr Yr (-s) := by
      simpa only [coneJointExit, coneJointExitBackward, Xr, Yr, neg_neg] using
        jointDrop_rev Xr Yr (-s)
    linarith
  have hXr : Continuous Xr := hX.comp continuous_neg
  have hYr : Continuous Yr := hY.comp continuous_neg
  have h := jointBackwardExit_closed_barrier hXr hYr hx' hy'
  rw [hrev] at h
  rcases h with ⟨heq, hbar⟩ | ⟨heq, hbar⟩
  · left
    refine ⟨by simpa [Xr] using heq, ?_⟩
    intro t ht
    have ht' : -t ∈ Icc (-coneJointExit X Y s) (-s) := by
      constructor <;> linarith [ht.1, ht.2]
    simpa [Xr] using hbar (-t) ht'
  · right
    refine ⟨by simpa [Yr] using heq, ?_⟩
    intro t ht
    have ht' : -t ∈ Icc (-coneJointExit X Y s) (-s) := by
      constructor <;> linarith [ht.1, ht.2]
    simpa [Yr] using hbar (-t) ht'

end LatticeProb
