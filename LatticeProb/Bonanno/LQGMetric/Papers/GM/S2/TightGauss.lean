/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S2.TightGauss at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgProc
import Mathlib.Probability.Moments.Basic

/-!
# GM S2.4e, a Gaussian input: lower tails of concentric circle-average increments (P2-TIGHT)

Decision D-A3 (`decisions/DEC-A.md` (c), S2.4e): "`h_{8^k r}(z) − h_r(z)` is Brownian at time
`k log 8`, and a Gaussian union bound makes `8^{k(ξQ−ζ)} e^{ξ(h_{8^k r} − h_r)}` large for all
`k ∈ [K/2, K)` with probability → 1". The single-`k` estimate:

`prob_circleAvg_inc_le`: for a whole-plane GFF, `0 < r < ρ` and `a ≥ 0`,
`P[h_ρ(z) − h_r(z) ≤ −a] ≤ exp(−a² / (2 log(ρ/r)))`.

Proof: `h_ρ(z) − h_r(z)` is centred Gaussian (`CircleAvg.map_cInc`, task P2-FCIRC) with variance
`log ρ − log r` (`CircleAvg.circCov_center`; Duplantier–Sheffield, *Liouville quantum gravity and
KPZ*, Prop. 3.3), and the Chernoff bound (mathlib `measure_le_le_exp_mul_mgf`) with the Gaussian
moment generating function (`mgf_id_gaussianReal`) at `t = −a/v`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace LQGMetric
namespace GM
namespace Tight

/-- Gaussian lower tail: `N(0, v)(−∞, −a] ≤ exp(−a²/(2v))`. -/
theorem gaussianReal_real_le_neg {v : ℝ≥0} (hv : 0 < (v : ℝ)) {a : ℝ} (ha : 0 ≤ a) :
    (gaussianReal 0 v).real {x | x ≤ -a} ≤ Real.exp (-a ^ 2 / (2 * v)) := by
  have ht : -a / v ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hv.le
  have hb := measure_le_le_exp_mul_mgf (μ := gaussianReal 0 v) (X := id) (-a) ht
    (integrable_exp_mul_gaussianReal _)
  rw [mgf_id_gaussianReal] at hb
  refine hb.trans (le_of_eq ?_)
  rw [← Real.exp_add]
  congr 1
  field_simp
  ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

/-- **Lower tail of `h_ρ(z) − h_r(z)`**, `0 < r < ρ`. -/
theorem prob_circleAvg_inc_le [IsProbabilityMeasure P] (hh : IsWholePlaneGFF h P) {r ρ : ℝ}
    (hr : 0 < r) (hrρ : r < ρ) (z : ℂ) {a : ℝ} (ha : 0 ≤ a) :
    P {ω | circleAvg (h ω) ρ z - circleAvg (h ω) r z ≤ -a} ≤
      ENNReal.ofReal (Real.exp (-a ^ 2 / (2 * Real.log (ρ / r)))) := by
  have hρ : 0 < ρ := hr.trans hrρ
  have hlaw := (CircleAvg.map_cInc hh hρ hr z z).1
  have hv : CircleAvg.incCov z ρ z r z ρ z r = Real.log (ρ / r) := by
    rw [CircleAvg.incCov, CircleAvg.circCov_center z hρ ρ hρ,
      CircleAvg.circCov_center z hρ r hr, CircleAvg.circCov_center z hr ρ hρ,
      CircleAvg.circCov_center z hr r hr, inv_mul_cancel₀ hρ.ne', inv_mul_cancel₀ hr.ne',
      Real.posLog_one, Real.posLog_eq_log (by
        rw [abs_of_pos (by positivity)]
        exact (one_le_inv_mul₀ hr).2 hrρ.le),
      (Real.posLog_eq_zero_iff _).2 (by
        rw [abs_of_pos (by positivity)]
        exact (inv_mul_le_one₀ hρ).2 hrρ.le),
      Real.log_div hρ.ne' hr.ne', Real.log_mul (inv_pos.2 hr).ne' hρ.ne', Real.log_inv]
    ring
  have hlog : 0 < Real.log (ρ / r) := Real.log_pos ((one_lt_div hr).2 hrρ)
  have hm := CircleAvg.measurable_cInc hh ρ z r z
  have e : {ω | circleAvg (h ω) ρ z - circleAvg (h ω) r z ≤ -a} =
      CircleAvg.cInc h ρ z r z ⁻¹' Iic (-a) := rfl
  rw [e, ← ofReal_measureReal, ← map_measureReal_apply hm (measurableSet_Iic), hlaw]
  refine ENNReal.ofReal_le_ofReal ((gaussianReal_real_le_neg ?_ ha).trans_eq ?_)
  · rw [Real.coe_toNNReal _ (by rw [hv]; exact hlog.le), hv]; exact hlog
  · rw [Real.coe_toNNReal _ (by rw [hv]; exact hlog.le), hv]

/-- **Union bound over dyadic-type scales** `8^k r`, `k ∈ [m, n)`, `m ≥ 1`:
`P[∃ k, h_{8^k r}(z) − h_r(z) ≤ −a k] ≤ ∑_k exp(−a² k / (2 log 8))`. -/
theorem prob_exists_circleAvg_inc_le [IsProbabilityMeasure P] (hh : IsWholePlaneGFF h P)
    {r : ℝ} (hr : 0 < r) (z : ℂ) {a : ℝ} (ha : 0 ≤ a) {m : ℕ} (hm : 1 ≤ m) (n : ℕ) :
    P {ω | ∃ k ∈ Finset.Ico m n,
        circleAvg (h ω) (8 ^ k * r) z - circleAvg (h ω) r z ≤ -(a * k)} ≤
      ∑ k ∈ Finset.Ico m n, ENNReal.ofReal (Real.exp (-(a ^ 2 * k) / (2 * Real.log 8))) := by
  have e : {ω | ∃ k ∈ Finset.Ico m n,
      circleAvg (h ω) (8 ^ k * r) z - circleAvg (h ω) r z ≤ -(a * k)} =
      ⋃ k ∈ Finset.Ico m n, {ω | circleAvg (h ω) (8 ^ k * r) z - circleAvg (h ω) r z ≤
        -(a * k)} := by
    ext ω; simp
  rw [e]
  refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  have hk1 : 1 ≤ k := hm.trans (Finset.mem_Ico.1 hk).1
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have h8 : (1 : ℝ) < 8 ^ k := one_lt_pow₀ (by norm_num) (by omega)
  have hlt : r < 8 ^ k * r := by nlinarith
  refine (prob_circleAvg_inc_le hh hr hlt z (by positivity)).trans_eq ?_
  have hl : Real.log (8 ^ k * r / r) = k * Real.log 8 := by
    rw [mul_div_assoc, div_self hr.ne', mul_one, Real.log_pow]
  have hl8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  rw [hl]
  congr 2
  field_simp

end Tight
end GM
end LQGMetric
