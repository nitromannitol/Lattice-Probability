import LatticeProb.Analysis.HeatKernelLatticeVolume

/-!
# Volume doubling for Euclidean lattice balls

Counting measure on open Euclidean lattice balls is uniformly doubling in each positive
dimension, including the transition between small and large radii.
-/

noncomputable section

open MeasureTheory Set
open LatticeProb.Euclidean.Lattice LatticeProb.Euclidean.Cube LatticeProb.Euclidean.Shell

namespace LatticeProb

/-- Counting measure on open Euclidean lattice balls is uniformly doubling. -/
theorem lattice_ball_count_doubling (d : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : Site d) (r : ℝ), 0 < r →
      (Measure.count {w : Site d | radius (physical 1 (w - x)) < 2 * r}).toReal ≤
        C * (Measure.count {w : Site d | radius (physical 1 (w - x)) < r}).toReal := by
  obtain ⟨c, hc, hlower⟩ := lattice_ball_count_lower d hd
  let A : ℝ := (1 + Real.sqrt d / 2) ^ d * unitBallVolume d
  have hA : 0 < A := by
    dsimp [A]
    exact mul_pos (pow_pos (by positivity) _) (unitBallVolume_pos d)
  let B : ℝ := A * 2 ^ d / c
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨1 + B, by positivity, ?_⟩
  intro x r hr
  by_cases hsmall : 2 * r ≤ 1
  · rw [lattice_ball_count_of_le_one x (by linarith : 0 < 2 * r) hsmall,
      lattice_ball_count_of_le_one x hr (by linarith)]
    nlinarith
  · have hupper := lattice_ball_count_le_pow d hd x (2 * r) (by linarith)
    have hlower' := hlower x r hr
    have hv : 0 ≤ (Measure.count {w : Site d |
        radius (physical 1 (w - x)) < r}).toReal := ENNReal.toReal_nonneg
    have hscale : A * (2 * r) ^ d = B * (c * r ^ d) := by
      dsimp [B]
      rw [mul_pow]
      field_simp
    change (Measure.count {w : Site d | radius (physical 1 (w - x)) < 2 * r}).toReal ≤
      A * (2 * r) ^ d at hupper
    rw [hscale] at hupper
    have hmul := mul_le_mul_of_nonneg_left hlower' hB.le
    nlinarith

end LatticeProb
