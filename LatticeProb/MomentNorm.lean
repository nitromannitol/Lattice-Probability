/- Adapted from nitromannitol/Parking-Sharpness, Apache-2.0. -/
/-
The `L^r` moment norm as a real number, `rNorm μ r f := (∫ |f|^r ∂μ)^{1/r}`, and its basic API
(nonnegativity, monotonicity in the function and in the exponent, homogeneity under a
nonnegative scalar, Minkowski's inequality, the bridge to Mathlib's `eLpNorm`, and the effect of
dividing by a deterministic scale), for an arbitrary measurable space and measure.  Also Young's
inequality in the specific form `X ≤ Y + a(√(bX) + k) → X ≤ 2Y + a²b + 2ak` that absorbs a
square-root cross term.  Every statement here is for an abstract measurable space, measure and
function.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

noncomputable section

namespace LatticeProb.MomentNorm

open MeasureTheory
open scoped ENNReal

/-! ### Young's inequality in the form the absorption needs -/

theorem young_absorb {X Y a b k : ℝ} (hX : 0 ≤ X) (hb : 0 ≤ b)
    (h : X ≤ Y + a * (Real.sqrt (b * X) + k)) :
    X ≤ 2 * Y + a ^ 2 * b + 2 * a * k := by
  have hsplit : Real.sqrt (b * X) = Real.sqrt b * Real.sqrt X := Real.sqrt_mul hb X
  have hb2 : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb
  have hX2 : Real.sqrt X ^ 2 = X := Real.sq_sqrt hX
  have hkey : 2 * (a * (Real.sqrt b * Real.sqrt X)) ≤ a ^ 2 * b + X := by
    nlinarith [sq_nonneg (a * Real.sqrt b - Real.sqrt X), Real.sqrt_nonneg b,
      Real.sqrt_nonneg X]
  rw [hsplit] at h
  nlinarith

/-! ### The `r`-th moment norm -/

variable {Ω : Type} [MeasurableSpace Ω]

/-- `(E |f|^r)^{1/r}`, the real-valued moment norm. -/
def rNorm (μ : Measure Ω) (r : ℝ) (f : Ω → ℝ) : ℝ :=
  (∫ ω, |f ω| ^ r ∂μ) ^ (1 / r)

theorem rNorm_nonneg (μ : Measure Ω) (r : ℝ) (f : Ω → ℝ) : 0 ≤ rNorm μ r f :=
  Real.rpow_nonneg (integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) r) _

/-- The lower integral of the `r`-th power of the norm, as a real integral. -/
theorem lintegral_enorm_rpow (μ : Measure Ω) {r : ℝ} (hr0 : 0 < r) (f : Ω → ℝ)
    (hint : Integrable (fun ω => |f ω| ^ r) μ) :
    ∫⁻ ω, ‖f ω‖ₑ ^ r ∂μ = ENNReal.ofReal (∫ ω, |f ω| ^ r ∂μ) := by
  rw [ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun _ => Real.rpow_nonneg (abs_nonneg _) r)]
  refine lintegral_congr fun ω => ?_
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _)
    (le_of_lt hr0)]

/-- The `L^r` norm of Mathlib in terms of the real `r`-th moment. -/
theorem eLpNorm_eq_ofReal (μ : Measure Ω) {r : ℝ} (hr0 : 0 < r) (f : Ω → ℝ)
    (hint : Integrable (fun ω => |f ω| ^ r) μ) :
    eLpNorm f (ENNReal.ofReal r) μ
      = (ENNReal.ofReal (∫ ω, |f ω| ^ r ∂μ)) ^ (1 / r) := by
  have hp0 : ENNReal.ofReal r ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hr0
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (le_of_lt hr0), lintegral_enorm_rpow μ hr0 f hint]

/-- The bridge between the real `r`-th moment norm and the `L^r` norm of
Mathlib. -/
theorem eLpNorm_toReal_eq (μ : Measure Ω) {r : ℝ} (hr : 1 ≤ r) (f : Ω → ℝ)
    (hint : Integrable (fun ω => |f ω| ^ r) μ) :
    (eLpNorm f (ENNReal.ofReal r) μ).toReal = rNorm μ r f := by
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr
  have hI0 : (0 : ℝ) ≤ ∫ ω, |f ω| ^ r ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) r
  rw [eLpNorm_eq_ofReal μ hr0 f hint,
    ENNReal.ofReal_rpow_of_nonneg hI0 (show (0:ℝ) ≤ 1 / r by positivity),
    ENNReal.toReal_ofReal (Real.rpow_nonneg hI0 _)]
  rfl

theorem eLpNorm_ne_top (μ : Measure Ω) {r : ℝ} (hr : 1 ≤ r) (f : Ω → ℝ)
    (hint : Integrable (fun ω => |f ω| ^ r) μ) :
    eLpNorm f (ENNReal.ofReal r) μ ≠ ⊤ := by
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr
  rw [eLpNorm_eq_ofReal μ hr0 f hint]
  exact ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top

/-- The `r`-th moment norm is monotone in the absolute value. -/
theorem rNorm_mono (μ : Measure Ω) {r : ℝ} (hr0 : 0 < r) {f g : Ω → ℝ}
    (h : ∀ᵐ ω ∂μ, |f ω| ≤ |g ω|) (hg : Integrable (fun ω => |g ω| ^ r) μ) :
    rNorm μ r f ≤ rNorm μ r g := by
  refine Real.rpow_le_rpow
    (integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) r) ?_ (by positivity)
  refine integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg _) r) hg ?_
  filter_upwards [h] with ω hω
  exact Real.rpow_le_rpow (abs_nonneg _) hω (le_of_lt hr0)

/-- A nonnegative constant comes out of the `r`-th moment norm. -/
theorem rNorm_const_mul (μ : Measure Ω) {r : ℝ} (hr0 : 0 < r) {c : ℝ} (hc : 0 ≤ c)
    (f : Ω → ℝ) : rNorm μ r (fun ω => c * f ω) = c * rNorm μ r f := by
  have hpt : ∀ ω : Ω, |c * f ω| ^ r = c ^ r * |f ω| ^ r := by
    intro ω
    rw [abs_mul, abs_of_nonneg hc, Real.mul_rpow hc (abs_nonneg _)]
  have hI0 : (0 : ℝ) ≤ ∫ ω, |f ω| ^ r ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) r
  rw [rNorm, rNorm]
  simp only [hpt]
  rw [integral_const_mul, Real.mul_rpow (Real.rpow_nonneg hc r) hI0,
    ← Real.rpow_mul hc, mul_one_div, div_self (ne_of_gt hr0), Real.rpow_one]

/-- **Minkowski's inequality** for the real `r`-th moment norm. -/
theorem rNorm_add_le (μ : Measure Ω) {r : ℝ} (hr : 1 ≤ r) {f g : Ω → ℝ}
    (hfm : AEStronglyMeasurable f μ) (hgm : AEStronglyMeasurable g μ)
    (hf : Integrable (fun ω => |f ω| ^ r) μ) (hg : Integrable (fun ω => |g ω| ^ r) μ)
    (hfg : Integrable (fun ω => |f ω + g ω| ^ r) μ) :
    rNorm μ r (fun ω => f ω + g ω) ≤ rNorm μ r f + rNorm μ r g := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal hr
  have hadd : eLpNorm (fun ω => f ω + g ω) (ENNReal.ofReal r) μ
      ≤ eLpNorm f (ENNReal.ofReal r) μ + eLpNorm g (ENNReal.ofReal r) μ :=
    eLpNorm_add_le hfm hgm hp1
  have hne_f := eLpNorm_ne_top μ hr f hf
  have hne_g := eLpNorm_ne_top μ hr g hg
  rw [← eLpNorm_toReal_eq μ hr (fun ω => f ω + g ω) hfg, ← eLpNorm_toReal_eq μ hr f hf,
    ← eLpNorm_toReal_eq μ hr g hg, ← ENNReal.toReal_add hne_f hne_g]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hne_f, hne_g⟩) hadd

/-- Moment norms increase with the exponent under a probability measure. -/
theorem rNorm_mono_exponent (μ : Measure Ω) [IsProbabilityMeasure μ] {p q : ℝ} (hp : 1 ≤ p)
    (hpq : p ≤ q) (f : Ω → ℝ) (hm : AEStronglyMeasurable f μ)
    (hpi : Integrable (fun ω => |f ω| ^ p) μ) (hqi : Integrable (fun ω => |f ω| ^ q) μ) :
    rNorm μ p f ≤ rNorm μ q f := by
  rw [← eLpNorm_toReal_eq μ hp f hpi, ← eLpNorm_toReal_eq μ (hp.trans hpq) f hqi]
  exact ENNReal.toReal_mono (eLpNorm_ne_top μ (hp.trans hpq) f hqi)
    (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hpq) hm)

/-- Raising the moment norm back to its exponent recovers the moment. -/
theorem rNorm_rpow (μ : Measure Ω) {r : ℝ} (hr : 0 < r) (f : Ω → ℝ) :
    rNorm μ r f ^ r = ∫ ω, |f ω| ^ r ∂μ := by
  rw [rNorm, ← Real.rpow_mul (integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) r),
    one_div_mul_cancel hr.ne', Real.rpow_one]

/-- Division by a deterministic scale preserves every finite moment. -/
theorem integrable_abs_div_rpow {μ : Measure Ω} {f : Ω → ℝ} {r : ℝ}
    (hi : Integrable (fun ω => |f ω| ^ r) μ) (a : ℝ) :
    Integrable (fun ω => |f ω / a| ^ r) μ := by
  simpa only [abs_div, Real.div_rpow (abs_nonneg _) (abs_nonneg a)] using hi.div_const (|a| ^ r)

/-- The normalized moment in terms of the unnormalized moment norm. -/
theorem integral_abs_div_rpow (μ : Measure Ω) {r : ℝ} (hr : 0 < r) (f : Ω → ℝ) {a : ℝ}
    (ha : 0 ≤ a) :
    ∫ ω, |f ω / a| ^ r ∂μ = (rNorm μ r f / a) ^ r := by
  simp only [abs_div, abs_of_nonneg ha, Real.div_rpow (abs_nonneg _) ha]
  rw [integral_div, Real.div_rpow (rNorm_nonneg _ _ _) ha, rNorm_rpow μ hr f]

end LatticeProb.MomentNorm

end
