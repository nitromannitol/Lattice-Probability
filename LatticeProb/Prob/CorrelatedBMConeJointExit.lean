import LatticeProb.Analysis.ConeJointExitEndpoint
import LatticeProb.Prob.CorrelatedBMLadderRegular

/-!
# Joint backward exits of correlated Brownian coordinates

Both time orientations of a two-sided correlated Brownian pair have a closed
barrier with equal endpoint values at every joint backward exit, almost surely.
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open MatedCRTHarmonic.MatedCRT

namespace LatticeProb.CorrelatedBM

/-- Each coordinate has earlier strict drops at every time, simultaneously
in the original and reversed time orientations. -/
theorem ae_forall_strict_drop_time_orientation {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) :
    ∀ᵐ ω ∂μ, ∀ (i : Fin 2) (s d : ℝ), d = 1 ∨ d = -1 →
      ∃ r < s, lrCoord i (d * r) ω < lrCoord i (d * s) ω := by
  filter_upwards [ae_all_iff.2 (fun i : Fin 2 => ae_coordinate_low hμ i)] with ω hlow
  intro i s d hd
  rcases hd with rfl | rfl
  · obtain ⟨r, hr, hv⟩ := (hlow i (s - 1) (lrCoord i s ω - 1)).1
    refine ⟨r, by linarith, ?_⟩
    simpa only [one_mul] using (show lrCoord i r ω < lrCoord i s ω by linarith)
  · obtain ⟨r, hr, hv⟩ := (hlow i (-s + 1) (lrCoord i (-s) ω - 1)).2
    refine ⟨-r, by linarith, ?_⟩
    simpa only [neg_one_mul, neg_neg] using
      (show lrCoord i r ω < lrCoord i (-s) ω by linarith)

/-- Almost surely, every joint backward exit of the coordinate pair, in either
time orientation, is an equal-endpoint closed barrier for one coordinate. -/
theorem ae_jointBackwardExit_closed_barrier {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) :
    ∀ᵐ ω ∂μ, ∀ (s d : ℝ), d = 1 ∨ d = -1 →
      let X : ℝ → ℝ := fun t => lrCoord 0 (d * t) ω
      let Y : ℝ → ℝ := fun t => lrCoord 1 (d * t) ω
      (X (coneJointExitBackward X Y s) = X s ∧
        ∀ t ∈ Icc (coneJointExitBackward X Y s) s, X s ≤ X t) ∨
      (Y (coneJointExitBackward X Y s) = Y s ∧
        ∀ t ∈ Icc (coneJointExitBackward X Y s) s, Y s ≤ Y t) := by
  filter_upwards [ae_forall_strict_drop_time_orientation hμ] with ω hdrop
  intro s d hd
  exact jointBackwardExit_closed_barrier
    ((continuous_lrCoord_time 0 ω).comp (continuous_const.mul continuous_id))
    ((continuous_lrCoord_time 1 ω).comp (continuous_const.mul continuous_id))
    (hdrop 0 s d hd) (hdrop 1 s d hd)

end LatticeProb.CorrelatedBM
