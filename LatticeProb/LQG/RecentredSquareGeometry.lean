import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.LogCorrFamily
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaExistence

/-! # Geometry of centred dyadic squares -/

open MeasureTheory Set
open scoped ENNReal

namespace LatticeProb.LQG

open MatedCRTHarmonic.GMCFacts LQGMetric.DGMC LQGMetric.DGMC.Neg3
open QuantumZipper

/-- Every point of a centred dyadic square lies within its side length of its centre. -/
theorem norm_sub_le_of_mem_centred_sqQ (z : ℂ) (m : ℕ) {w : ℂ}
    (hw : w ∈ sqQ (sqCorner z (radius m)) m) : ‖w - z‖ ≤ radius m := by
  obtain ⟨y, hy, rfl⟩ := eq_of_mem_sqQ hw
  exact norm_sqPoint_sub_le z (radius_pos m).le (cell0_subset_unitSq hy)

/-- Every finer circle centred in the square lies in the normalizing disk. -/
theorem norm_add_radius_le_of_mem_centred_sqQ (z : ℂ) {ε : ℝ} {m : ℕ}
    (hm : radius m ≤ ε / 2) (k : ℕ) {w : ℂ}
    (hw : w ∈ sqQ (sqCorner z (radius m)) m) :
    ‖w - z‖ + radius (m + k) ≤ ε := by
  have h1 := norm_sub_le_of_mem_centred_sqQ z m hw
  have h2 := AreaExist.aradius_anti (Nat.le_add_right m k)
  linarith

/-- The area of a dyadic square is the square of its side length. -/
theorem volume_centred_sqQ (z : ℂ) (m : ℕ) :
    volume (sqQ (sqCorner z (radius m)) m) = ENNReal.ofReal (radius m ^ 2) := by
  have h := lintegral_sqQ (fun _ => (1 : ℝ≥0∞)) measurable_const (sqCorner z (radius m)) m
  simpa only [setLIntegral_const, one_mul, mul_one, volume_cell0] using h

/-- The area and finite-volume hypotheses for the centred square. -/
theorem centred_sqQ_volume_bounds (z : ℂ) {ε : ℝ} {m : ℕ}
    (hm : radius m ≤ ε / 2) :
    volume (sqQ (sqCorner z (radius m)) m) < ⊤ ∧
      volume.real (sqQ (sqCorner z (radius m)) m) ≤ (1 / 4 : ℝ) * ε ^ 2 := by
  have hε : 0 < ε := by linarith [radius_pos m]
  rw [volume_centred_sqQ]
  constructor
  · exact ENNReal.ofReal_lt_top
  · rw [Measure.real, volume_centred_sqQ, ENNReal.toReal_ofReal (sq_nonneg _)]
    nlinarith [radius_pos m, sq_nonneg (ε / 2 - radius m)]

end LatticeProb.LQG
