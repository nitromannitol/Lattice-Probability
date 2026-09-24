/-
Hölder's inequality combining a TAIL bound (the measure of a set) with a MOMENT bound (an
`L^r` norm), for an arbitrary probability space.  Stated for abstract objects only (an
arbitrary measurable space, an arbitrary probability measure, an arbitrary measurable set and
an arbitrary nonnegative function with a finite `r`-th moment), so this module can move
verbatim into the shared library.  Built from Mathlib's own Bochner-integral Hölder inequality
(`MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg`) at the conjugate exponent pair
`(r/(r-1), r)`.

Moved from Parking-Sharpness.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Data.Real.ConjExponents
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

open MeasureTheory

noncomputable section

namespace LatticeProb.Scaling.Holder

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The `r`-th moment norm as a real number, `(∫ |f|^r ∂μ)^{1/r}` — restated here (rather than
imported) so this module stays Mathlib-only. -/
def rMoment (μ : Measure Ω) (r : ℝ) (f : Ω → ℝ) : ℝ := (∫ ω, |f ω| ^ r ∂μ) ^ (1 / r)

/-- A finite `r`-th absolute moment gives a finite `L^r` seminorm, for `r ≥ 1`. -/
theorem eLpNorm_ne_top_of_rpow_integrable (μ : Measure Ω) {r : ℝ} (hr : 1 ≤ r) (f : Ω → ℝ)
    (hint : Integrable (fun ω => |f ω| ^ r) μ) :
    eLpNorm f (ENNReal.ofReal r) μ ≠ ⊤ := by
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr
  have hp0 : ENNReal.ofReal r ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hr0
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hr0.le]
  have hlint : ∫⁻ ω, ‖f ω‖ₑ ^ r ∂μ = ENNReal.ofReal (∫ ω, |f ω| ^ r ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun _ => Real.rpow_nonneg (abs_nonneg _) r)]
    refine lintegral_congr fun ω => ?_
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hr0.le]
  rw [hlint]
  exact ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top

/-- **Hölder's inequality for the integral of an indicator against a nonnegative function**:
`∫ 1_S · g ≤ μ(S)^{1-1/r} · (∫ |g|^r)^{1/r}`, for any measurable set `S`, any `r > 1`, and any
nonnegative, a.e.-strongly-measurable `g` with a finite `r`-th moment. -/
theorem integral_indicator_le_measureReal_rpow_mul_rMoment (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Set Ω) (hS : MeasurableSet S) (g : Ω → ℝ) (hgm : AEStronglyMeasurable g μ)
    (hg0 : 0 ≤ᵐ[μ] g) {r : ℝ} (hr : 1 < r)
    (hgi : Integrable (fun ω => |g ω| ^ r) μ) :
    ∫ ω, Set.indicator S g ω ∂μ ≤ (μ.real S) ^ (1 - 1 / r) * rMoment μ r g := by
  have hr0 : (0 : ℝ) < r := lt_trans zero_lt_one hr
  set q : ℝ := r / (r - 1) with hqdef
  have hpq : q.HolderConjugate r := by
    rw [Real.holderConjugate_comm, Real.holderConjugate_iff]
    refine ⟨hr, ?_⟩
    rw [hqdef, inv_div]
    have hrne : r - 1 ≠ 0 := by linarith
    field_simp
    ring
  set f : Ω → ℝ := Set.indicator S (fun _ => (1 : ℝ)) with hfdef
  have hfg : Set.indicator S g = fun ω => f ω * g ω := by
    funext ω
    by_cases hω : ω ∈ S
    · simp [f, Set.indicator_of_mem hω]
    · simp [f, Set.indicator_of_notMem hω]
  have hf_nonneg : 0 ≤ᵐ[μ] f :=
    Filter.Eventually.of_forall (fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
  have hfmeas : Measurable f := measurable_const.indicator hS
  have hqpos : (0 : ℝ) < q := by rw [hqdef]; exact div_pos hr0 (by linarith)
  have hfmem : MemLp f (ENNReal.ofReal q) μ :=
    MemLp.of_bound hfmeas.aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun ω => by
        by_cases hω : ω ∈ S
        · simp [f, Set.indicator_of_mem hω]
        · simp [f, Set.indicator_of_notMem hω]))
  have hgmem : MemLp g (ENNReal.ofReal r) μ :=
    ⟨hgm, (eLpNorm_ne_top_of_rpow_integrable μ hr.le g hgi).lt_top⟩
  have hmain := integral_mul_le_Lp_mul_Lq_of_nonneg hpq hf_nonneg hg0 hfmem hgmem
  rw [← hfg] at hmain
  have hfpow : (∫ ω, f ω ^ q ∂μ) = μ.real S := by
    have heq : (fun ω => f ω ^ q) = f := by
      funext ω
      by_cases hω : ω ∈ S
      · simp [f, Set.indicator_of_mem hω]
      · simp [f, Set.indicator_of_notMem hω, Real.zero_rpow hqpos.ne']
    rw [heq, hfdef, integral_indicator_const (1 : ℝ) hS, smul_eq_mul, mul_one]
  rw [hfpow] at hmain
  have hexp : (1 : ℝ) / q = 1 - 1 / r := by
    rw [hqdef]
    have hrne : r - 1 ≠ 0 := by linarith
    field_simp
  rw [hexp] at hmain
  have hrmeq : (∫ ω, g ω ^ r ∂μ) = ∫ ω, |g ω| ^ r ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hg0] with ω hω
    rw [abs_of_nonneg hω]
  unfold rMoment
  rw [hrmeq] at hmain
  exact hmain

end LatticeProb.Scaling.Holder

end
