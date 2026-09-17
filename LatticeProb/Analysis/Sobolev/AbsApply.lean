import LatticeProb.Analysis.Sobolev.Basic
import LatticeProb.Analysis.Sobolev.Scaling
import LatticeProb.Analysis.Sobolev.TestFn

open MeasureTheory
open scoped ENNReal FourierTransform

namespace LatticeProb.Sobolev

/-- A test function whose `H^s` norm is at most `η²` has `|F φ| ≤ η ‖F‖`. -/
theorem abs_apply_le_negSobolevNorm {d : ℕ} (D : Set (Space d)) (s η : ℝ) (hη : 0 < η)
    (F : (Space d → ℝ) → ℝ)
    (hsmul : ∀ (c : ℝ) (φ : Space d → ℝ), F (fun x => c * φ x) = c * F φ)
    {φ : Space d → ℝ} (hφ : IsTestFn D φ)
    (hn : sobolevNormSq d s φ ≤ ENNReal.ofReal (η ^ 2)) :
    ENNReal.ofReal |F φ| ≤ ENNReal.ofReal η * negSobolevNorm d s D F := by
  have hscale : sobolevNormSq d s (fun x => (1 / η) * φ x) ≤ 1 := by
    rw [sobolevNormSq_const_mul]
    calc ENNReal.ofReal ((1 / η) ^ 2) * sobolevNormSq d s φ
        ≤ ENNReal.ofReal ((1 / η) ^ 2) * ENNReal.ofReal (η ^ 2) := mul_le_mul_right hn _
      _ = ENNReal.ofReal ((1 / η) ^ 2 * η ^ 2) := (ENNReal.ofReal_mul (by positivity)).symm
      _ = 1 := by
          rw [show (1 / η) ^ 2 * η ^ 2 = 1 by field_simp]
          simp
  have hφ' : IsTestFn D (fun x => (1 / η) * φ x) := hφ.const_mul _
  have h1 : ENNReal.ofReal |F (fun x => (1 / η) * φ x)| ≤ negSobolevNorm d s D F :=
    le_sSup ⟨_, hφ', hscale, rfl⟩
  rw [hsmul] at h1
  rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / η)] at h1
  calc ENNReal.ofReal |F φ|
      = ENNReal.ofReal (η * ((1 / η) * |F φ|)) := by
          rw [show η * ((1 / η) * |F φ|) = |F φ| by field_simp]
    _ = ENNReal.ofReal η * ENNReal.ofReal ((1 / η) * |F φ|) := ENNReal.ofReal_mul (by positivity)
    _ ≤ ENNReal.ofReal η * negSobolevNorm d s D F := mul_le_mul_right h1 _

end LatticeProb.Sobolev
