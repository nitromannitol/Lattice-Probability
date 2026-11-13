import LatticeProb.LQG.LQGBallMassBoundsHolds
import LatticeProb.LQG.GMCRatioLimitMeasure
import LatticeProb.LQG.LQGMeasureExistenceProved
import LatticeProb.LQG.LQGMeasureSquarePositive
import LatticeProb.LQG.LQGMeasureNonatomicAll
import LatticeProb.LQG.LQGMeasureNonatomicUpper

/-!
# The LQG measure statements without hypotheses

The multiscale ball-mass bounds, the non-atomicity, the volume growth, the full support and the
positivity on dyadic squares of the LQG measure are reduced in this library to three statements:
the whole-plane ball-mass bounds `WholePlaneLQGBallMassBoundsLP` (Ding and Gwynne 2020, Lemma 3.8),
the coordinate change `LQGMeasureCoordChangeLP` at `α₀ = 0`, and the existence
`LQGMeasureExistenceLP`.  All three are proved (`wholePlaneLQGBallMassBoundsLP_holds`,
`lqgMeasureCoordChangeLP_zero`, `lqgMeasureExistenceLP_proved`), so each statement of the chain
holds with no hypothesis.

## Main results

* `rescaledBallMassUniformStepLP_holds`, `wholePlaneScaledBallMassStepLP_holds`: the rescaled
  ball-mass bound, uniformly in the dyadic scale, and the multiscale ball-mass bound around the
  origin for the whole-plane GFF.
* `lqgMeasureNonatomicAllLP_holds`: the LQG measure has no atom, for every whole-plane GFF model
  (from `LQGMeasureNonatomicUpper.lqgMeasureNonatomicLP_holds`).
* `liouvilleBallMassBoundStepLP_holds`, `lqgVolumeGrowthAllScalesStmtLP_holds`: ball-volume bounds
  for the LQG measure with a log singularity at the origin.
* `lqgMeasureFullSupportStmtLP_holds`, `lqgMeasureSquarePositiveLP_holds`: the LQG measure charges
  every nonempty open set and every closed dyadic square.
-/

universe u

namespace LatticeProb.LQG

open MeasureTheory LatticeProb.LQG.LQGMeasureNonatomicMass LatticeProb.LQG.LQGMeasureNonatomicUpper

/-- The rescaled ball-mass bound of Ding and Gwynne, Lemma 3.8, uniformly in the dyadic scale. -/
theorem rescaledBallMassUniformStepLP_holds : RescaledBallMassUniformStepLP.{u} :=
  rescaledBallMassUniformStep_lp
    (fun _ _ P γ hC hcirc => wholePlaneLQGBallMassBoundsLP_holds P γ hC hcirc)
    (fun _ _ P γ hC hcirc => lqgMeasureCoordChangeLP_zero P γ hC hcirc)

/-- The multiscale ball-mass bound for the whole-plane GFF around the origin
(arXiv:2208.11795, Lemma 2.4). -/
theorem wholePlaneScaledBallMassStepLP_holds : WholePlaneScaledBallMassStepLP.{u} :=
  wholePlaneScaledBallMassStep_of_uniform_lp rescaledBallMassUniformStepLP_holds
    circleAverageDyadicTailStep_lp

/-- The universal form of the non-atomicity of the LQG measure. -/
theorem lqgMeasureNonatomicAllLP_holds : LQGMeasureNonatomicAllLP.{u} :=
  fun γ α₀ _ _ P hC hcirc => lqgMeasureNonatomicLP_holds P γ α₀ hC hcirc

/-- The ball-volume bounds for the LQG measure on every ball `B_R`
(arXiv:2208.11795, Lemma 2.4). -/
theorem liouvilleBallMassBoundStepLP_holds : LiouvilleBallMassBoundStepLP.{u} :=
  liouvilleBallMassBoundStep_of_scaled_lp wholePlaneScaledBallMassStepLP_holds
    (fun _ _ P γ hC hcirc => lqgMeasureExistenceLP_proved P γ 0 hC hcirc)
    (fun _ _ P γ α₀ hC hcirc => lqgMeasureNonatomicLP_holds P γ α₀ hC hcirc)

/-- Volume growth of the LQG measure at all small scales. -/
theorem lqgVolumeGrowthAllScalesStmtLP_holds : LQGVolumeGrowthAllScalesStmtLP.{u} :=
  lqgVolumeGrowthAllScalesStmt_of_ballMass_lp liouvilleBallMassBoundStepLP_holds

/-- The LQG measure charges every nonempty open set, almost surely. -/
theorem lqgMeasureFullSupportStmtLP_holds : LQGMeasureFullSupportStmtLP.{u} :=
  lqgMeasureFullSupportStmt_of_volumeGrowth_lp lqgVolumeGrowthAllScalesStmtLP_holds

/-- The LQG measure charges every closed dyadic square, almost surely. -/
theorem lqgMeasureSquarePositiveLP_holds : LQGMeasureSquarePositiveLP.{u} :=
  lqgMeasureSquarePositiveLP_of_inputs
    (fun _ _ P γ hC hcirc => wholePlaneLQGBallMassBoundsLP_holds P γ hC hcirc)
    (fun _ _ P γ hC hcirc => lqgMeasureCoordChangeLP_zero P γ hC hcirc)
    (fun _ _ P γ α hC hcirc => lqgMeasureExistenceLP_proved P γ α hC hcirc)

end LatticeProb.LQG
