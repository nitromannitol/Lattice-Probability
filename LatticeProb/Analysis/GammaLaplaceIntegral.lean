import Mathlib

/-!
# Negative powers as Laplace integrals

For `z > 0` and `q > 0`, `z^{-q} Γ(q) = ∫_0^∞ t^{q-1} e^{-z t} dt`, with the integral computed in `[0, ∞]`.
Together with a Laplace bound `E e^{-t Z} ≤ min 1 (A t^{-a})`, this controls `E Z^{-q}` for `q < a`:
the one-dimensional integral `∫_0^∞ t^{q-1} min(1, A t^{-a}) dt` is at most `1/q + A/(a-q)`.

* `LatticeProb.ofReal_rpow_neg_mul_gamma`: `ofReal z ^ (-q) * ofReal (Γ q) = ∫⁻_{t>0} ofReal (t^{q-1} e^{-z t})`.
* `LatticeProb.lintegral_Ioi_rpow_mul_min_le`: the bound `∫⁻_{t>0} t^{q-1} min(1, A t^{-a}) ≤ 1/q + A/(a-q)`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace LatticeProb

/-- For `z > 0` and `q > 0`, `z^{-q} Γ(q) = ∫_0^∞ t^{q-1} e^{-z t} dt`, as an identity in `[0, ∞]`. -/
theorem ofReal_rpow_neg_mul_gamma {z q : ℝ} (hz : 0 < z) (hq : 0 < q) :
    ENNReal.ofReal z ^ (-q) * ENNReal.ofReal (Real.Gamma q) =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (q - 1) * Real.exp (-(z * t))) := by
  have hint : IntegrableOn (fun t : ℝ => t ^ (q - 1) * Real.exp (-(z * t))) (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := q - 1) (b := z) (by linarith)
      one_pos hz
    refine this.congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp [Real.rpow_one]
  have h0 : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun t : ℝ => t ^ (q - 1) * Real.exp (-(z * t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (Real.exp_pos _).le
  rw [← ofReal_integral_eq_lintegral_ofReal hint h0, Real.integral_rpow_mul_exp_neg_mul_Ioi hq hz,
    (ENNReal.ofReal_rpow_of_pos hz).symm.symm, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Real.rpow_neg hz.le, one_div, Real.inv_rpow hz.le]

/-- **A one-dimensional integral.** For `0 < q < a` and `A ≥ 0`,
`∫_0^∞ t^{q-1} min(1, A t^{-a}) dt ≤ 1/q + A/(a - q)`. -/
theorem lintegral_Ioi_rpow_mul_min_le {q a A : ℝ} (hq : 0 < q) (hqa : q < a) (hA : 0 ≤ A) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (q - 1)) * ENNReal.ofReal (min 1 (A * t ^ (-a))) ≤
      ENNReal.ofReal (1 / q + A / (a - q)) := by
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ),
    lintegral_union measurableSet_Ioi (Ioc_disjoint_Ioi le_rfl)]
  have h1 : ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (t ^ (q - 1)) *
      ENNReal.ofReal (min 1 (A * t ^ (-a))) ≤ ENNReal.ofReal (1 / q) := by
    calc ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (t ^ (q - 1)) * ENNReal.ofReal (min 1 (A * t ^ (-a)))
        ≤ ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (t ^ (q - 1)) := by
          refine lintegral_mono fun t => ?_
          calc ENNReal.ofReal (t ^ (q - 1)) * ENNReal.ofReal (min 1 (A * t ^ (-a)))
              ≤ ENNReal.ofReal (t ^ (q - 1)) * 1 := by
                gcongr
                rw [← ENNReal.ofReal_one]
                exact ENNReal.ofReal_le_ofReal (min_le_left _ _)
            _ = _ := mul_one _
      _ = ENNReal.ofReal (1 / q) := by
          have hi : IntegrableOn (fun t : ℝ => t ^ (q - 1)) (Ioc 0 1) :=
            (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
              (intervalIntegral.intervalIntegrable_rpow' (by linarith))
          have h0 : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] fun t : ℝ => t ^ (q - 1) := by
            filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
            exact Real.rpow_nonneg ht.1.le _
          rw [← ofReal_integral_eq_lintegral_ofReal hi h0, ← intervalIntegral.integral_of_le zero_le_one,
            integral_rpow (Or.inl (by linarith))]
          simp [Real.zero_rpow hq.ne']
  have h2 : ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (t ^ (q - 1)) *
      ENNReal.ofReal (min 1 (A * t ^ (-a))) ≤ ENNReal.ofReal (A / (a - q)) := by
    have hlt : q - 1 - a < -1 := by linarith
    have hi : IntegrableOn (fun t : ℝ => A * t ^ (q - 1 - a)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt hlt one_pos).const_mul A
    have h0 : 0 ≤ᵐ[volume.restrict (Ioi (1 : ℝ))] fun t : ℝ => A * t ^ (q - 1 - a) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg hA (Real.rpow_nonneg (by linarith [mem_Ioi.1 ht]) _)
    calc ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (t ^ (q - 1)) * ENNReal.ofReal (min 1 (A * t ^ (-a)))
        ≤ ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (A * t ^ (q - 1 - a)) := by
          refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
          have ht0 : 0 < t := by linarith [mem_Ioi.1 ht]
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht0.le _)]
          refine ENNReal.ofReal_le_ofReal ?_
          calc t ^ (q - 1) * min 1 (A * t ^ (-a)) ≤ t ^ (q - 1) * (A * t ^ (-a)) := by
                gcongr
                exact min_le_right _ _
            _ = A * t ^ (q - 1 - a) := by
                rw [mul_left_comm, ← Real.rpow_add ht0, show q - 1 + -a = q - 1 - a by ring]
      _ = ENNReal.ofReal (A / (a - q)) := by
          rw [← ofReal_integral_eq_lintegral_ofReal hi h0, integral_const_mul,
            integral_Ioi_rpow_of_lt hlt one_pos]
          congr 1
          have : q - 1 - a + 1 = -(a - q) := by ring
          rw [this, Real.one_rpow]
          field_simp [(sub_pos.2 hqa).ne']
  calc _ ≤ ENNReal.ofReal (1 / q) + ENNReal.ofReal (A / (a - q)) := add_le_add h1 h2
    _ = _ := (ENNReal.ofReal_add (by positivity) (div_nonneg hA (sub_pos.2 hqa).le)).symm

end LatticeProb
