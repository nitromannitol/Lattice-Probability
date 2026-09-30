/- A uniform error bound for the right-endpoint time quadrature.

Moved from Parking-Sharpness.
-/
import Mathlib

open MeasureTheory Finset
namespace LatticeProb.Scaling.TimeRiemannEstimate

/-- A Lipschitz integrand has a right-endpoint quadrature error bounded by the
interval length times the mesh times its Lipschitz constant. -/
theorem abs_sum_sub_integral_le {f : ℝ → ℝ} {L : NNReal} (hf : LipschitzWith L f)
    {h : ℝ} (hh : 0 ≤ h) (N : ℕ) :
    |h * ∑ k ∈ Finset.range N, f (((k + 1 : ℕ) : ℝ) * h) -
      ∫ s in (0 : ℝ)..(N : ℝ) * h, f s| ≤ (N : ℝ) * h * ((L : ℝ) * h) := by
  have hstep : ∀ k : ℕ, (k : ℝ) * h ≤ (k + 1 : ℕ) * h := by
    intro k
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ k) hh
  have hlocal : ∀ k : ℕ,
      |h * f (((k + 1 : ℕ) : ℝ) * h) -
        ∫ s in (k : ℝ) * h..((k + 1 : ℕ) : ℝ) * h, f s| ≤ h * ((L : ℝ) * h) := by
    intro k
    have hlen : ((k + 1 : ℕ) : ℝ) * h - (k : ℝ) * h = h := by push_cast; ring
    have heq : h * f (((k + 1 : ℕ) : ℝ) * h) =
        ∫ s in (k : ℝ) * h..((k + 1 : ℕ) : ℝ) * h,
          f (((k + 1 : ℕ) : ℝ) * h) := by
      rw [intervalIntegral.integral_const, hlen, smul_eq_mul]
    rw [heq, ← intervalIntegral.integral_sub intervalIntegrable_const
      (hf.continuous.intervalIntegrable _ _)]
    have hb : ∀ s ∈ Set.uIcc ((k : ℝ) * h) (((k + 1 : ℕ) : ℝ) * h),
        ‖f (((k + 1 : ℕ) : ℝ) * h) - f s‖ ≤ (L : ℝ) * h := by
      intro s hs
      rw [Set.uIcc_of_le (hstep k)] at hs
      have hd : dist (((k + 1 : ℕ) : ℝ) * h) s ≤ h := by
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hs.2)]
        linarith [hs.1]
      exact (hf.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left hd L.coe_nonneg)
    have hb' := intervalIntegral.norm_integral_le_of_norm_le_const (fun s hs => hb s (Set.uIoc_subset_uIcc hs))
    rw [hlen, abs_of_nonneg hh] at hb'
    simpa only [Real.norm_eq_abs, mul_comm] using hb'
  have hint := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := f)
    (a := fun k : ℕ => (k : ℝ) * h) (n := N)
    (fun _ _ => hf.continuous.intervalIntegrable _ _)
  simp only [Nat.cast_zero, zero_mul] at hint
  rw [← hint, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    |∑ k ∈ Finset.range N, (h * f (((k + 1 : ℕ) : ℝ) * h) -
      ∫ s in (k : ℝ) * h..((k + 1 : ℕ) : ℝ) * h, f s)|
      ≤ ∑ k ∈ Finset.range N, |h * f (((k + 1 : ℕ) : ℝ) * h) -
        ∫ s in (k : ℝ) * h..((k + 1 : ℕ) : ℝ) * h, f s| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range N, h * ((L : ℝ) * h) :=
      Finset.sum_le_sum fun k _ => hlocal k
    _ = _ := by simp [mul_assoc]

end LatticeProb.Scaling.TimeRiemannEstimate
