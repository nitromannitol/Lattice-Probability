/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.KilledHeatRefl at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatBasic
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.OccupationHit2
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.GaussKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Killed heat kernel, part 11: towards the reflection principle for the bridge maximum
(task P2-KILLED, D-KHK1)

DZZ (`LBM_LGDarXiv.tex` l. 491–499) use `P(max_{s ≤ t} (B_s − (s/t)B_t)_1 ≥ x) = e^{−2x²/t}`.
Route (Doob's time change of the bridge, e.g. Revuz–Yor, Ch. I, Exercise 3.10; Karatzas–Shreve
§5.6.B): `V_u = ((t + u)/t) β_{tu/(t+u)}` is a Brownian motion (`isPreBrownianReal_timeChange`),
and `max_{s<t} β_s ≥ x` iff `V_u − (x/t)u ≥ x` for some `u ≥ 0`, whose probability is the
probability that a Brownian motion with drift `x/t` ever reaches `x`.

Proved here:
* `occDens_neg_eq`: QZ's occupation density of `σ b_t + μ t` at a negative level is
  `e^{2μy/σ²}/μ` (own elementary computation: `(y − μm)² = (−y − μm)² − 4μym`, then QZ's
  `occDens_eq_inv_mu`);
* `prob_hit_neg_eq`: `P(σ b + μ t ever hits y) = e^{2μy/σ²}` for `y < 0`, `μ, σ > 0` (QZ's
  `prob_hit_neg` + the above; Revuz–Yor Ch. II Exercise 3.12);
* `isPreBrownianReal_timeChange`: the time change of a coordinate of a planar bridge is a
  pre-Brownian motion.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LQGMetric
namespace KilledHeat

open QuantumZipper.Williams

/-- Occupation density of drift Brownian motion at a negative level. -/
theorem occDens_neg_eq {σ μ : ℝ} (hσ : 0 < σ) (hμ : 0 < μ) {y : ℝ} (hy : y < 0) :
    occDens σ μ y = Real.exp (2 * μ * y / σ ^ 2) / μ := by
  have key : ∀ m ∈ Set.Ioi (0 : ℝ), gaussianPDFReal (μ * m) (occVar σ m) y =
      Real.exp (2 * μ * y / σ ^ 2) * gaussianPDFReal (μ * m) (occVar σ m) (-y) := by
    intro m hm
    have hm' : (0 : ℝ) < m := hm
    rw [gaussianPDFReal, gaussianPDFReal, coe_occVar σ hm'.le]
    have he : Real.exp (-(y - μ * m) ^ 2 / (2 * (σ ^ 2 * m))) = Real.exp (2 * μ * y / σ ^ 2) *
        Real.exp (-(-y - μ * m) ^ 2 / (2 * (σ ^ 2 * m))) := by
      rw [← Real.exp_add]
      congr 1
      field_simp
      ring
    rw [he]
    ring
  rw [occDens, setIntegral_congr_fun measurableSet_Ioi key, integral_const_mul, ← occDens,
    occDens_eq_inv_mu hσ hμ (neg_pos.mpr hy)]
  ring

/-- `P(σ b + μ · ever hits y) = e^{2μy/σ²}` for `y < 0`. -/
theorem prob_hit_neg_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {b : ℝ≥0 → Ω → ℝ}
    (hb : GoodBM b P) {σ μ : ℝ} (hσ : 0 < σ) (hμ : 0 < μ) {y : ℝ} (hy : y < 0) :
    P.real {ω | ∃ t, dpath σ μ b ω t = y} = Real.exp (2 * μ * y / σ ^ 2) := by
  rw [(prob_hit_neg hb hσ hμ hy).2, occDens_neg_eq hσ hμ hy, occDens_zero_eq_inv_mu hσ hμ]
  field_simp

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The time `t u/(t + u) ∈ [0, t)` of Doob's time change. -/
def tcTime (t u : ℝ≥0) : ℝ≥0 := t * u / (t + u)

lemma tcTime_le (t u : ℝ≥0) : tcTime t u ≤ t := by
  unfold tcTime
  rcases eq_or_ne (t + u) 0 with h | h
  · simp [h]
  · rw [div_le_iff₀ (pos_iff_ne_zero.mpr h)]
    exact mul_le_mul_of_nonneg_left le_add_self zero_le

lemma tcTime_mono (t : ℝ≥0) {u u' : ℝ≥0} (h : u ≤ u') : tcTime t u ≤ tcTime t u' := by
  unfold tcTime
  rcases eq_or_ne t 0 with ht | ht
  · simp [ht]
  have h1 : 0 < t + u := add_pos_of_pos_of_nonneg (pos_iff_ne_zero.mpr ht) zero_le
  have h2 : 0 < t + u' := add_pos_of_pos_of_nonneg (pos_iff_ne_zero.mpr ht) zero_le
  rw [div_le_div_iff₀ h1 h2]
  have : t * u * (t + u') = t * t * u + t * u * u' := by ring
  have : t * u' * (t + u) = t * t * u' + t * u * u' := by ring
  calc t * u * (t + u') = t * t * u + t * u * u' := by ring
    _ ≤ t * t * u' + t * u * u' := by gcongr
    _ = t * u' * (t + u) := by ring

/-- Doob's time change of the `b`-coordinate of `X`: `V_u = ((t + u)/t) X_{tu/(t+u)}`. -/
def timeChange (t : ℝ≥0) (X : ℝ≥0 → Ω → ℂ) (b : Bool) : ℝ≥0 → Ω → ℝ :=
  fun u ω ↦ (((t : ℝ) + u) / t) • coordProc X (b, tcTime t u) ω

/-- **Doob's time change**: a coordinate of a planar bridge of length `t`, time-changed, is a
pre-Brownian motion. -/
theorem isPreBrownianReal_timeChange {t : ℝ≥0} (ht : t ≠ 0) {X : ℝ≥0 → Ω → ℂ} {P : Measure Ω}
    (hX : IsPlanarBridge t X P) (b : Bool) : IsPreBrownianReal (timeChange t X b) P := by
  have h0 : IsGaussianProcess (fun u ω ↦ coordProc X (b, tcTime t u) ω) P :=
    hX.gauss.comp_right (fun u : ℝ≥0 ↦ (b, tcTime t u))
  have hG : IsGaussianProcess (timeChange t X b) P := h0.smul (fun u : ℝ≥0 ↦ ((t : ℝ) + (u : ℝ)) / t)
  refine hG.isPreBrownianReal_of_covariance (fun u ↦ ?_) (fun u u' huu' ↦ ?_)
  · simp only [timeChange, smul_eq_mul]
    rw [integral_const_mul, hX.mean, mul_zero]
  · show cov[fun ω ↦ (((t : ℝ) + u) / t) * coordProc X (b, tcTime t u) ω,
      fun ω ↦ (((t : ℝ) + u') / t) * coordProc X (b, tcTime t u') ω; P] = u
    rw [covariance_const_mul_left, covariance_const_mul_right,
      hX.cov _ _ (tcTime_le t u) (tcTime_le t u'), bridgeCov_same',
      min_eq_left (tcTime_mono t huu')]
    have ht' : (0 : ℝ) < t := lt_of_le_of_ne (NNReal.coe_nonneg t) (Ne.symm (by exact_mod_cast ht))
    have h1 : (t : ℝ) + u ≠ 0 := by positivity
    have h2 : (t : ℝ) + u' ≠ 0 := by positivity
    simp only [tcTime]
    push_cast
    field_simp
    ring
where
  bridgeCov_same' (T : ℝ≥0) (b : Bool) (x y : ℝ≥0) :
      bridgeCov T (b, x) (b, y) = ((min x y : ℝ≥0) : ℝ) - x * y / T := by
    simp [bridgeCov]

end KilledHeat
end LQGMetric
