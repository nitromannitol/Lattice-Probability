import LatticeProb.Analysis.AnnulusThickeningVolume

/-!
# Area of the thickened boundary of a round disk

For an open disk `B_R(z)` in `ℂ` with `0 < R ≤ 2` and `0 < s < 1`, the `s`-thickening of its boundary circle has
Lebesgue measure at most `12 π s`. This is the boundary-regularity hypothesis
`volume (thickening s (frontier D)) ≤ C s` on a domain `D`, for round disks of radius at most `2`, with
`C = 12 π`.

The estimate is the case of a single circle of `volume_thickening_sphere_le`, together with
`frontier (ball z R) = sphere z R` for `R ≠ 0`.

## Main result

* `LatticeProb.volume_thickening_frontier_ball_le`: `|thickening s (∂B_R(z))| ≤ 12 π s`.
-/

open Metric MeasureTheory Set

namespace LatticeProb

/-- **Area of the thickened boundary of a round disk**: for `0 < R ≤ 2` and `0 < s < 1`, the `s`-thickening
of the boundary of the disk `B_R(z)` in `ℂ` has Lebesgue measure at most `12 π s`. -/
theorem volume_thickening_frontier_ball_le (z : ℂ) {R s : ℝ} (hR : 0 < R) (hR2 : R ≤ 2) (hs : 0 < s)
    (hs1 : s < 1) :
    volume (thickening s (frontier (ball z R))) ≤ ENNReal.ofReal (12 * Real.pi * s) := by
  have hpi := Real.pi_pos
  rw [frontier_ball z hR.ne']
  refine (volume_thickening_sphere_le z hR.le hs).trans (ENNReal.ofReal_le_ofReal ?_)
  have h4 : 0 ≤ 4 * Real.pi * s := by positivity
  calc 4 * Real.pi * s * (R + s) ≤ 4 * Real.pi * s * 3 :=
        mul_le_mul_of_nonneg_left (by linarith) h4
    _ = 12 * Real.pi * s := by ring

end LatticeProb
