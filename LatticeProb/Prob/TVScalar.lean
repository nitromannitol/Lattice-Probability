import LatticeProb.Bonanno.QuantumZipper.Proofs.Section5.TVLocal
import Mathlib.Algebra.Order.Sub.Unbundled.Hom

/-! Scalar multiplication and total variation. -/

open MeasureTheory
open scoped ENNReal

namespace LatticeProb

/-- Scaling both measures scales total variation by at most the same factor. -/
theorem tvDist_smul_le {α : Type*} [MeasurableSpace α]
    (c : ℝ≥0∞) (μ ν : Measure α) :
    QuantumZipper.TV.tvDist (c • μ) (c • ν) ≤ c * QuantumZipper.TV.tvDist μ ν := by
  refine iSup_le fun s => iSup_le fun hs => sup_le ?_ ?_
  · simpa only [Measure.smul_apply, smul_eq_mul] using
      ((le_mul_tsub).trans (mul_le_mul_right (QuantumZipper.TV.le_tvDist hs) c))
  · simpa only [Measure.smul_apply, smul_eq_mul] using
      ((le_mul_tsub).trans (mul_le_mul_right (QuantumZipper.TV.le_tvDist' hs) c))

/-- A finite scalar factors out of the total variation distance. -/
theorem tvDist_smul {α : Type*} [MeasurableSpace α]
    (c : ℝ≥0∞) (hc : c ≠ ⊤) (μ ν : Measure α) :
    QuantumZipper.TV.tvDist (c • μ) (c • ν) = c * QuantumZipper.TV.tvDist μ ν := by
  simp only [QuantumZipper.TV.tvDist, Measure.smul_apply, smul_eq_mul,
    ENNReal.mul_iSup, mul_max, ENNReal.mul_sub (fun _ _ => hc)]

end LatticeProb
