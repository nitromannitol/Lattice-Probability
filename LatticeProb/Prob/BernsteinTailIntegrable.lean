/-
# Integrability of the Bernstein tail

The Bernstein tail is integrable against a nonnegative real moment weight.
The proof uses the Gaussian and exponential comparison in
`LatticeProb.Prob.BernsteinIntegrate`.
-/
import Mathlib

open MeasureTheory Set

namespace LatticeProb

/-- The Bernstein tail has an integrable real moment weight on the positive half-line. -/
theorem integrable_rpow_mul_bernstein_tail (r a v : ℝ) (hr : 2 ≤ r)
    (ha : 0 < a) (hv : 0 < v) :
    Integrable (fun t : ℝ => r * t ^ (r - 1) *
      (2 * Real.exp (-(t ^ 2 / (2 * (v + a * t)))))) (volume.restrict (Ioi 0)) := by
  have hpoint : ∀ t ∈ Ioi (0 : ℝ),
      r * t ^ (r - 1) * Real.exp (-(t ^ 2 / (2 * (v + a * t))))
        ≤ r * t ^ (r - 1) * Real.exp (-(t ^ 2 / (4 * v)))
          + r * t ^ (r - 1) * Real.exp (-(t / (4 * a))) := by
    intro t ht
    have ht0 : 0 < t := ht
    have hcoef : 0 ≤ r * t ^ (r - 1) := by positivity
    by_cases h : a * t ≤ v
    · have hexp : -(t ^ 2 / (2 * (v + a * t))) ≤ -(t ^ 2 / (4 * v)) := by
        apply neg_le_neg
        rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * v)
          (by positivity : (0 : ℝ) < 2 * (v + a * t))]
        nlinarith [h, sq_nonneg t]
      have h1 := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hcoef
      have h2 : 0 ≤ r * t ^ (r - 1) * Real.exp (-(t / (4 * a))) := by positivity
      linarith
    · have h' : v < a * t := lt_of_not_ge h
      have hle : t ^ 2 / (4 * a * t) ≤ t ^ 2 / (2 * (v + a * t)) := by
        rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * a * t)
          (by positivity : (0 : ℝ) < 2 * (v + a * t))]
        nlinarith [h', sq_nonneg t, ht0.le]
      have h2t : t ^ 2 / (4 * a * t) = t / (4 * a) := by
        field_simp
      have hexp : -(t ^ 2 / (2 * (v + a * t))) ≤ -(t / (4 * a)) := by
        rw [← h2t]
        exact neg_le_neg hle
      have h1 := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hcoef
      have h3 : 0 ≤ r * t ^ (r - 1) * Real.exp (-(t ^ 2 / (4 * v))) := by positivity
      linarith
  have hGint : IntegrableOn (fun t : ℝ => r * t ^ (r - 1) * Real.exp (-(t ^ 2 / (4 * v))))
      (Ioi 0) := by
    have h0 : IntegrableOn (fun t : ℝ => t ^ (r - 1) * Real.exp (-(1 / (4 * v)) * t ^ 2))
        (Ioi 0) :=
      integrableOn_rpow_mul_exp_neg_mul_sq (b := 1 / (4 * v)) (by positivity) (by linarith)
    refine (MeasureTheory.Integrable.const_mul h0 r).congr ?_
    filter_upwards with t
    rw [show t ^ 2 / (4 * v) = (1 / (4 * v)) * t ^ 2 by
      rw [div_eq_mul_inv, one_div]; ring_nf]
    ring_nf
  have hEint : IntegrableOn (fun t : ℝ => r * t ^ (r - 1) * Real.exp (-(t / (4 * a))))
      (Ioi 0) := by
    have h0 : IntegrableOn (fun t : ℝ => t ^ (r - 1) * Real.exp (-(1 / (4 * a)) * t))
        (Ioi 0) := by
      simpa [Real.rpow_one] using
        integrableOn_rpow_mul_exp_neg_mul_rpow (s := r - 1) (p := 1) (b := 1 / (4 * a))
          (by linarith) (by norm_num) (by positivity)
    refine (MeasureTheory.Integrable.const_mul h0 r).congr ?_
    filter_upwards with t
    rw [show t / (4 * a) = (1 / (4 * a)) * t by
      rw [div_eq_mul_inv, one_div]; ring_nf]
    ring_nf
  have hGEint : IntegrableOn (fun t : ℝ =>
      r * t ^ (r - 1) * Real.exp (-(t ^ 2 / (4 * v)))
        + r * t ^ (r - 1) * Real.exp (-(t / (4 * a)))) (Ioi 0) := hGint.add hEint
  have hFint : IntegrableOn (fun t : ℝ =>
      r * t ^ (r - 1) * Real.exp (-(t ^ 2 / (2 * (v + a * t))))) (Ioi 0) := by
    refine MeasureTheory.Integrable.mono' hGEint ?_ ?_
    · fun_prop
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      have htpos : 0 < t ^ (r - 1) := Real.rpow_pos_of_pos ht _
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hpoint t ht
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hFint.const_mul 2

end LatticeProb
