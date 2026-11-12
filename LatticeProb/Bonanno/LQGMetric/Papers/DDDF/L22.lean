/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.L22 at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Probability.Moments.Variance

/-!
# DDDF Lemma 22 (quantile gaps are controlled by the variance)

DDDF = Ding–Dubédat–Dunlap–Falconet, arXiv:1904.08021, `literature/src/1904.08021/tightness.tex`
l. 1022–1033 (`Lem:Quantiles/Var`; blueprint node DDDF.L22): if `Z` has finite variance,
`p ∈ (0, 1/2)`, `ℓ̄ ≥ ℓ`, `P(Z ≥ ℓ̄) ≥ p` and `P(Z ≤ ℓ) ≥ p`, then `(ℓ̄ − ℓ)² ≤ 2 p⁻² Var Z`.

Proof: own elementary proof (deviation, see the report) instead of DDDF's independent copy
(l. 1031): with `m = E Z`, one of `{Z ≥ ℓ̄}`, `{Z ≤ ℓ}` lies in `{|Z − m| ≥ (ℓ̄ − ℓ)/2}`, so
Chebyshev gives `p ≤ 4 Var Z / (ℓ̄ − ℓ)²`, and `4/p ≤ 2/p²` for `p ≤ 1/2`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory

namespace LQGMetric
namespace DDDF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **DDDF Lemma 22** (`Lem:Quantiles/Var`, tightness.tex l. 1022–1033). -/
theorem dddf_lemma22 [IsProbabilityMeasure P] {Z : Ω → ℝ} (hZ : MemLp Z 2 P) {p : ℝ}
    (hp0 : 0 < p) (hp : p < 1 / 2) {lb l : ℝ} (hll : l ≤ lb)
    (hhi : ENNReal.ofReal p ≤ P {ω | lb ≤ Z ω}) (hlo : ENNReal.ofReal p ≤ P {ω | Z ω ≤ l}) :
    (lb - l) ^ 2 ≤ 2 / p ^ 2 * variance Z P := by
  have hV := variance_nonneg Z P
  rcases hll.eq_or_lt with h | h
  · rw [h, sub_self]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity
  set m := P[Z]
  set c := (lb - l) / 2 with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  have hcheb := meas_ge_le_variance_div_sq hZ hc0
  have key : p ≤ variance Z P / c ^ 2 := by
    have h1 : ENNReal.ofReal p ≤ ENNReal.ofReal (variance Z P / c ^ 2) := by
      rcases le_total m ((lb + l) / 2) with hm | hm
      · refine hhi.trans ((measure_mono fun ω (hω : lb ≤ Z ω) => ?_).trans hcheb)
        show c ≤ |Z ω - m|
        rw [abs_of_nonneg (by linarith)]; linarith
      · refine hlo.trans ((measure_mono fun ω (hω : Z ω ≤ l) => ?_).trans hcheb)
        show c ≤ |Z ω - m|
        rw [abs_of_nonpos (by linarith)]; linarith
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
  rw [le_div_iff₀ (by positivity)] at key
  have hlb : (lb - l) ^ 2 = 4 * c ^ 2 := by rw [hc]; ring
  rw [hlb, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  have : 4 * c ^ 2 * p ^ 2 ≤ 2 * (p * c ^ 2) := by
    have := mul_nonneg (mul_nonneg hp0.le (sq_nonneg c)) (by linarith : (0 : ℝ) ≤ 1 - 2 * p)
    nlinarith
  linarith
end DDDF
end LQGMetric
