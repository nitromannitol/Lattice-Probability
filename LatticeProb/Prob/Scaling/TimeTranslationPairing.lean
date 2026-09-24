import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Translation of a time shift between the two factors of a pairing.

Moved from Parking-Sharpness.
-/

open MeasureTheory

namespace LatticeProb.Scaling.TimeTranslationPairing

/-- Translation invariance of the space-time volume measure moves a time shift from one
factor of a pairing to the other, with the sign of the shift reversed. -/
theorem integral_translate_pairing {d : ℕ} (u g : ℝ × (Fin d → ℝ) → ℝ) (h : ℝ) :
    (∫ p : ℝ × (Fin d → ℝ), u (p.1 + h, p.2) * g p) =
      ∫ p : ℝ × (Fin d → ℝ), u p * g (p.1 - h, p.2) := by
  letI : (volume : Measure (ℝ × (Fin d → ℝ))).IsAddRightInvariant := by
    change ((volume : Measure ℝ).prod (volume : Measure (Fin d → ℝ))).IsAddRightInvariant
    infer_instance
  simpa [Prod.add_def] using
    integral_add_right_eq_self (fun p : ℝ × (Fin d → ℝ) => u p * g (p.1 - h, p.2))
      ((h, 0) : ℝ × (Fin d → ℝ))

end LatticeProb.Scaling.TimeTranslationPairing
