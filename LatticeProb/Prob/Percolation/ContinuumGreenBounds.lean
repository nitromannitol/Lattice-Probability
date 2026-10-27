import LatticeProb.Prob.Percolation.ContinuumGreen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

private theorem scalar_power (n : ℕ) (hn : 1 ≤ n) (r a b : ℝ) (hr : 0 < r) (ha : r ≤ a)
    (hb : r ≤ b) :
    |(a ^ n)⁻¹ - (b ^ n)⁻¹| ≤ (n : ℝ) / r ^ (n + 1) * |a - b| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun x : ℝ => (x ^ n)⁻¹)
    (f' := fun x : ℝ => -((n : ℝ) / x ^ (n + 1))) (s := Set.Ici r)
    (fun x hx => by
      have hx0 : 0 < x := lt_of_lt_of_le hr hx
      have hpow : x ^ n = x ^ (n - 1) * x := by
        rw [← pow_succ, Nat.sub_add_cancel hn]
      convert ((hasDerivAt_id x).pow n).inv (pow_ne_zero n (ne_of_gt hx0)) |>.hasDerivWithinAt
        using 1
      · funext t; simp
      · simp only [Pi.pow_apply, id_eq, pow_succ]
        field_simp
        rw [hpow]
        ring)
    (fun x hx => by
      have hx0 : 0 < x := lt_of_lt_of_le hr hx
      rw [Real.norm_eq_abs, abs_neg,
        abs_of_nonneg (div_nonneg (Nat.cast_nonneg n) (le_of_lt (pow_pos hx0 _)))]
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg n) (pow_pos hr _)
        (pow_le_pow_left₀ (le_of_lt hr) hx _))
    (convex_Ici r) hb ha
  simpa only [Real.norm_eq_abs] using h

private theorem scalar_log (r a b : ℝ) (hr : 0 < r) (ha : r ≤ a)
    (hb : r ≤ b) :
    |Real.log a - Real.log b| ≤ r⁻¹ * |a - b| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := Real.log) (f' := fun x : ℝ => x⁻¹) (s := Set.Ici r)
    (fun x hx => (Real.hasDerivAt_log (ne_of_gt (lt_of_lt_of_le hr hx))).hasDerivWithinAt)
    (fun x hx => by
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (lt_of_lt_of_le hr hx))]
      exact inv_le_inv₀ (lt_of_lt_of_le hr hx) hr |>.2 hx)
    (convex_Ici r) hb ha
  simpa only [Real.norm_eq_abs] using h

/-- A uniform two-point estimate for the radial continuum Green function. -/
theorem continuumGreen_radial_bound (d : ℕ) (hd : 2 ≤ d) (κ : {a : ℝ // 0 < a}) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z w : {x : EuclideanSpace ℝ (Fin d) // x ≠ 0})
      (r : ℝ), 0 < r → r ≤ ‖z.val‖ → r ≤ ‖w.val‖ →
      |continuumGreen d hd κ z - continuumGreen d hd κ w| ≤
        C * ‖z.val - w.val‖ / r ^ (d - 1) := by
  by_cases hd2 : d = 2
  · subst d
    let A : ℝ := -(1 / (2 * Real.pi * κ.val))
    refine ⟨|A| + 1, by positivity, ?_⟩
    intro z w r hr hz hw
    have hs := scalar_log r ‖z.val‖ ‖w.val‖ hr hz hw
    have hn := abs_norm_sub_norm_le z.val w.val
    have hA : 0 ≤ |A| := abs_nonneg A
    have ht : |A| * |Real.log ‖z.val‖ - Real.log ‖w.val‖| ≤
        (|A| + 1) * ‖z.val - w.val‖ / r := by
      calc
        _ ≤ |A| * (r⁻¹ * |‖z.val‖ - ‖w.val‖|) := mul_le_mul_of_nonneg_left hs hA
        _ ≤ |A| * (r⁻¹ * ‖z.val - w.val‖) := by gcongr
        _ ≤ (|A| + 1) * (r⁻¹ * ‖z.val - w.val‖) :=
          mul_le_mul_of_nonneg_right (by linarith)
            (mul_nonneg (le_of_lt (inv_pos.mpr hr)) (norm_nonneg _))
        _ = _ := by rw [div_eq_mul_inv]; ring
    have hk : continuumGreen 2 hd κ z - continuumGreen 2 hd κ w =
        A * (Real.log ‖z.val‖ - Real.log ‖w.val‖) := by
      simp only [continuumGreen, ↓reduceIte, A]
      ring
    rw [hk, abs_mul]
    simpa only [Nat.reduceSub, pow_one] using ht
  · let n : ℕ := d - 2
    have hn : 1 ≤ n := by dsimp [n]; omega
    have hnd : n + 1 = d - 1 := by dsimp [n]; omega
    let A : ℝ := Real.Gamma ((d : ℝ) / 2 - 1) /
      (4 * Real.rpow Real.pi ((d : ℝ) / 2) * κ.val)
    refine ⟨|A| * n + 1, by positivity, ?_⟩
    intro z w r hr hz hw
    have hz0 : 0 ≤ ‖z.val‖ := norm_nonneg _
    have hw0 : 0 ≤ ‖w.val‖ := norm_nonneg _
    have he : (2 : ℝ) - d = -(n : ℝ) := by dsimp [n]; rw [Nat.cast_sub hd]; push_cast; ring
    have hpz : Real.rpow ‖z.val‖ (2 - (d : ℝ)) = (‖z.val‖ ^ n)⁻¹ := by
      rw [he]
      change (‖z.val‖ ^ (-(n : ℝ)) : ℝ) = _
      rw [Real.rpow_neg hz0, Real.rpow_natCast]
    have hpw : Real.rpow ‖w.val‖ (2 - (d : ℝ)) = (‖w.val‖ ^ n)⁻¹ := by
      rw [he]
      change (‖w.val‖ ^ (-(n : ℝ)) : ℝ) = _
      rw [Real.rpow_neg hw0, Real.rpow_natCast]
    have hs := scalar_power n hn r ‖z.val‖ ‖w.val‖ hr hz hw
    have hv := abs_norm_sub_norm_le z.val w.val
    have hA : 0 ≤ |A| := abs_nonneg A
    have ht : |A| * |(‖z.val‖ ^ n)⁻¹ - (‖w.val‖ ^ n)⁻¹| ≤
        (|A| * n + 1) * ‖z.val - w.val‖ / r ^ (d - 1) := by
      rw [← hnd]
      have hk : 0 ≤ (n : ℝ) / r ^ (n + 1) :=
        div_nonneg (Nat.cast_nonneg n) (le_of_lt (pow_pos hr _))
      calc
        _ ≤ |A| * ((n : ℝ) / r ^ (n + 1) * |‖z.val‖ - ‖w.val‖|) := mul_le_mul_of_nonneg_left hs hA
        _ ≤ |A| * ((n : ℝ) / r ^ (n + 1) * ‖z.val - w.val‖) := by gcongr
        _ = (|A| * n) * ((r ^ (n + 1))⁻¹ * ‖z.val - w.val‖) := by rw [div_eq_mul_inv]; ring
        _ ≤ (|A| * n + 1) * ((r ^ (n + 1))⁻¹ * ‖z.val - w.val‖) :=
          mul_le_mul_of_nonneg_right (by linarith)
            (mul_nonneg (le_of_lt (inv_pos.mpr (pow_pos hr _))) (norm_nonneg _))
        _ = _ := by rw [div_eq_mul_inv]; ring
    simpa only [continuumGreen, if_neg hd2, hpz, hpw, ← mul_sub, abs_mul, A] using ht

end LatticeProb.Percolation
