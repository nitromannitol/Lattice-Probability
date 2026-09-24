/-
Translation of smooth tests in time and the corresponding change of variables
for weak equations and forward difference quotients.

Moved from Parking-Sharpness.
-/
import LatticeProb.Prob.Scaling.TimeIntegration
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

open MeasureTheory
noncomputable section
namespace LatticeProb.Scaling.TimeTest

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Translate a test forward in time by translating its argument backward. -/
def timeShift (h : ℝ) (ψ : ℝ × E → ℝ) (p : ℝ × E) : ℝ := ψ (p.1 - h, p.2)

/-- Shifting a smooth function in time keeps it smooth. -/
theorem contDiff_timeShift {ψ : ℝ × E → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (h : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (timeShift h ψ) :=
  hψ.comp ((contDiff_fst.sub contDiff_const).prodMk contDiff_snd)

omit [NormedSpace ℝ E] in
/-- Shifting a compactly supported function in time keeps it compactly supported. -/
theorem hasCompactSupport_timeShift {ψ : ℝ × E → ℝ} (hψ : HasCompactSupport ψ) (h : ℝ) :
    HasCompactSupport (timeShift h ψ) := by
  change HasCompactSupport (fun p : ℝ × E => ψ (p.1 - h, p.2))
  simpa [Function.comp_def, Prod.sub_def] using hψ.comp_homeomorph (Homeomorph.subRight (h, (0 : E)))

omit [NormedSpace ℝ E] in
/-- A point in the support of a time-shifted function pulls back to a point in the support of
the original function. -/
theorem mem_tsupport_timeShift {ψ : ℝ × E → ℝ} {h : ℝ} {p : ℝ × E}
    (hp : p ∈ tsupport (timeShift h ψ)) : (p.1 - h, p.2) ∈ tsupport ψ :=
  tsupport_comp_subset_preimage ψ ((continuous_fst.sub continuous_const).prodMk continuous_snd) hp

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Time differentiation commutes with a time shift. -/
theorem timeDeriv_timeShift (ψ : ℝ × E → ℝ) (h : ℝ) :
    timeDeriv (timeShift h ψ) = timeShift h (timeDeriv ψ) := by
  funext p
  exact deriv_comp_sub_const (fun s => ψ (s, p.2)) h p.1

variable {d : ℕ}

/-- Move a time translation from the field onto the test in a pairing. -/
theorem integral_time_translate (u f : ℝ × (Fin d → ℝ) → ℝ) (h : ℝ) :
    (∫ p, u (p.1 + h, p.2) * f p) = ∫ p, u p * timeShift h f p := by
  rw [Measure.volume_eq_prod]
  simpa only [timeShift, Prod.fst_add, Prod.snd_add, Prod.add_def, add_zero, add_sub_cancel_right, Prod.eta] using
    (integral_add_right_eq_self (μ := (volume : Measure ℝ).prod volume) (fun p : ℝ × (Fin d → ℝ) => u p * f (p.1 - h, p.2))
      (h, (0 : Fin d → ℝ)))

/-- Pairing a difference quotient with a test equals a difference of pairings.
Continuity and compact support guarantee integrability of both terms. -/
theorem integral_time_difference_quotient {u f : ℝ × (Fin d → ℝ) → ℝ}
    (hu : Continuous u) (hf : Continuous f) (hc : HasCompactSupport f) (h : ℝ) :
    (∫ p, ((u (p.1 + h, p.2) - u p) / h) * f p) =
      ((∫ p, u p * timeShift h f p) - ∫ p, u p * f p) / h := by
  have hi : Integrable (fun p => u p * f p) :=
    (hu.mul hf).integrable_of_hasCompactSupport hc.mul_left
  have hit : Integrable (fun p => u (p.1 + h, p.2) * f p) :=
    ((hu.comp ((continuous_fst.add_const h).prodMk continuous_snd)).mul hf).integrable_of_hasCompactSupport hc.mul_left
  simp_rw [div_mul_eq_mul_div, sub_mul]
  rw [integral_div, integral_sub hit hi, integral_time_translate]

end LatticeProb.Scaling.TimeTest
