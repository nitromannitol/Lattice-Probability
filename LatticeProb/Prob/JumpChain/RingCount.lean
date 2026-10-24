import LatticeProb.Prob.JumpChain.Position
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Clock-ring probabilities

Partial clock sums have Erlang densities, obtained by convolution of independent
exponential intervals. Their clock-count windows have Poisson probabilities, also
for the actual count on regular histories. The first ring uses interval zero.
-/

namespace LatticeProb.JumpChain

open MeasureTheory ProbabilityTheory Set Preorder
open scoped NNReal ENNReal

noncomputable section

variable {S : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

/-- Integrating a polynomial against the two exponential factors raises its degree by one. -/
theorem integral_exponential_poisson_term (R t : ℝ) (n : ℕ) :
    (∫ u in 0..t, R * Real.exp (-(R * u)) *
      (Real.exp (-(R * (t - u))) * (R * (t - u)) ^ n / n.factorial)) =
      Real.exp (-(R * t)) * (R * t) ^ (n + 1) / (n + 1).factorial := by
  have hexp (u : ℝ) : Real.exp (-(R * u)) * Real.exp (-(R * (t - u))) =
      Real.exp (-(R * t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hfun : (fun u : ℝ ↦ R * Real.exp (-(R * u)) *
      (Real.exp (-(R * (t - u))) * (R * (t - u)) ^ n / n.factorial)) =
      fun u ↦ (R * Real.exp (-(R * t)) * R ^ n / n.factorial) * (t - u) ^ n := by
    funext u
    rw [mul_pow]
    calc
      _ = (R * (Real.exp (-(R * u)) * Real.exp (-(R * (t - u)))) *
          R ^ n / n.factorial) * (t - u) ^ n := by ring
      _ = _ := by rw [hexp]
  rw [hfun, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_left (fun x : ℝ ↦ x ^ n), sub_self, sub_zero,
    integral_pow]
  simp only [zero_pow (Nat.succ_ne_zero n), sub_zero, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_pow, pow_succ]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The elementary density of a sum of `n + 1` exponential intervals. -/
def erlangDensity (R : ℝ) (n : ℕ) (x : ℝ) : ℝ≥0∞ :=
  if 0 ≤ x then ENNReal.ofReal
    (R * (Real.exp (-(R * x)) * (R * x) ^ n / n.factorial)) else 0

/-- Erlang densities are measurable. -/
theorem measurable_erlangDensity (R : ℝ) (n : ℕ) : Measurable (erlangDensity R n) := by
  unfold erlangDensity
  exact Measurable.ite (measurableSet_le measurable_const measurable_id)
    (by fun_prop) measurable_const

/-- The density at index zero is the exponential density. -/
theorem erlangDensity_zero (R : ℝ) : erlangDensity R 0 = exponentialPDF R := by
  funext x
  simp only [erlangDensity, exponentialPDF_eq, pow_zero, mul_one,
    Nat.factorial_zero, Nat.cast_one, div_one]
  split_ifs <;> simp

/-- Convolution with one exponential interval raises the Erlang shape by one. -/
theorem exponential_lconvolution_erlangDensity {R : ℝ} (hR : 0 < R) (n : ℕ) :
    lconvolution (exponentialPDF R) (erlangDensity R n) volume =
      erlangDensity R (n + 1) := by
  funext t
  rw [lconvolution_def]
  by_cases ht : 0 ≤ t
  · have hfun : (fun u ↦ exponentialPDF R u * erlangDensity R n (-u + t)) =
        (Icc 0 t).indicator (fun u ↦ ENNReal.ofReal
          (R * (R * Real.exp (-(R * u)) *
            (Real.exp (-(R * (t - u))) * (R * (t - u)) ^ n / n.factorial)))) := by
      funext u
      by_cases hu : 0 ≤ u
      · rw [exponentialPDF_of_nonneg hu]
        by_cases hut : u ≤ t
        · rw [erlangDensity, if_pos (by linarith),
            indicator_of_mem (show u ∈ Icc 0 t from ⟨hu, hut⟩)]
          rw [← ENNReal.ofReal_mul (mul_nonneg hR.le (Real.exp_pos _).le)]
          congr 1
          rw [show -u + t = t - u by ring]
          ring
        · rw [erlangDensity, if_neg (by linarith), mul_zero,
            indicator_of_notMem (show u ∉ Icc 0 t from fun h ↦ hut h.2)]
      · rw [exponentialPDF_of_neg (lt_of_not_ge hu), zero_mul,
          indicator_of_notMem (show u ∉ Icc 0 t from fun h ↦ hu h.1)]
    rw [hfun, lintegral_indicator measurableSet_Icc]
    have hi : IntegrableOn (fun u : ℝ ↦ R * (R * Real.exp (-(R * u)) *
        (Real.exp (-(R * (t - u))) * (R * (t - u)) ^ n / n.factorial))) (Icc 0 t) :=
      (by fun_prop : Continuous _).integrableOn_Icc
    rw [← ofReal_integral_eq_lintegral_ofReal hi]
    · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht,
        intervalIntegral.integral_const_mul, integral_exponential_poisson_term,
        erlangDensity, if_pos ht]
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
      exact mul_nonneg hR.le (mul_nonneg (mul_nonneg hR.le (Real.exp_pos _).le)
        (div_nonneg (mul_nonneg (Real.exp_pos _).le
          (pow_nonneg (mul_nonneg hR.le (sub_nonneg.mpr hu.2)) n))
          (Nat.cast_nonneg _)))
  · rw [erlangDensity, if_neg ht]
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [] with u
    change exponentialPDF R u * erlangDensity R n (-u + t) = 0
    by_cases hu : 0 ≤ u
    · rw [erlangDensity, if_neg (by linarith), mul_zero]
    · rw [exponentialPDF_of_neg (lt_of_not_ge hu), zero_mul]

namespace BoundedRates

/-- The first clock-ring time has the exponential law of rate `R`. -/
theorem historyLaw_map_jumpTime_one (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] :
    (rates.historyLaw μ).map (fun h ↦ jumpTime h 1) = expMeasure rates.R := by
  simpa only [jumpTime, Finset.sum_range_one] using
    (rates.historyLaw_map_clock μ 0).trans rates.clockLaw_eq_expMeasure

/-- The first ring has the exponential cumulative distribution at nonnegative times. -/
theorem historyLaw_jumpTime_one_le (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (t : ℝ≥0) :
    rates.historyLaw μ {h | jumpTime h 1 ≤ t} =
      ENNReal.ofReal (1 - Real.exp (-(rates.R * t))) := by
  letI := isProbabilityMeasure_expMeasure rates.R_pos
  have hmap := congrArg (fun ν : Measure ℝ ↦ ν (Iic (t : ℝ)))
    (rates.historyLaw_map_jumpTime_one μ)
  rw [Measure.map_apply (measurable_jumpTime 1) measurableSet_Iic] at hmap
  change rates.historyLaw μ {h | jumpTime h 1 ≤ t} = _ at hmap
  rw [hmap, ← ofReal_cdf, cdf_expMeasure_eq rates.R_pos, if_pos t.coe_nonneg]

/-- No ring has occurred by time `t` precisely when the first clock exceeds `t`. -/
theorem historyLaw_jumpTime_window_zero (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (t : ℝ≥0) :
    rates.historyLaw μ {h | jumpTime h 0 ≤ t ∧ (t : ℝ) < jumpTime h (0 + 1)} =
      ENNReal.ofReal (Real.exp (-(rates.R * t)) * (rates.R * t) ^ 0 / Nat.factorial 0) := by
  have hset : {h : History S | jumpTime h 0 ≤ t ∧ (t : ℝ) < jumpTime h (0 + 1)} =
      {h | jumpTime h 1 ≤ t}ᶜ := by
    ext h
    simp only [jumpTime_zero, zero_add, mem_compl_iff, mem_setOf_eq, not_le]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨t.coe_nonneg, h⟩⟩
  rw [hset, measure_compl (measurableSet_le (measurable_jumpTime 1) measurable_const)
    (measure_ne_top _ _), measure_univ, rates.historyLaw_jumpTime_one_le]
  have hexp : Real.exp (-(rates.R * (t : ℝ))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg rates.R_pos.le t.property))
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (sub_nonneg.mpr hexp)]
  simp only [sub_sub_cancel, pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one,
    div_one]

/-- A partial clock sum is independent of the next recorded interval. -/
theorem indepFun_jumpTime_clock (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (n : ℕ) :
    IndepFun (fun h : History S ↦ jumpTime h n) (fun h ↦ (h n).2)
      (rates.historyLaw μ) := by
  classical
  cases n with
  | zero =>
    simpa only [jumpTime_zero] using
      (indepFun_const_left (μ := rates.historyLaw μ) (0 : ℝ)
        (fun h : History S ↦ (h 0).2))
  | succ n =>
    let total : (↥(Finset.Iic n) → S × ℝ) → ℝ := fun h ↦
      ∑ k : Fin (n + 1), (h ⟨k.val, Finset.mem_Iic.mpr (by omega)⟩).2
    have hm : Measurable total := by unfold total; fun_prop
    have heq : (fun h : History S ↦ total (frestrictLe n h)) =
        (fun h ↦ jumpTime h (n + 1)) := by
      funext h
      change (∑ k : Fin (n + 1), (h k.val).2) =
        ∑ k ∈ Finset.range (n + 1), (h k).2
      exact Fin.sum_univ_eq_sum_range (fun k ↦ (h k).2) (n + 1)
    have hi := (rates.indepFun_prefix_clock μ n).comp hm measurable_id
    change IndepFun (fun h ↦ total (frestrictLe n h))
      (fun h ↦ (h (n + 1)).2) (rates.historyLaw μ) at hi
    rw [heq] at hi
    exact hi

/-- The law of the next ring time is the convolution with one exponential interval. -/
theorem historyLaw_map_jumpTime_succ (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (n : ℕ) :
    (rates.historyLaw μ).map (fun h ↦ jumpTime h (n + 1)) =
      Measure.conv ((rates.historyLaw μ).map (fun h ↦ jumpTime h n))
        (expMeasure rates.R) := by
  have hi := (rates.indepFun_jumpTime_clock μ n).map_add_eq_map_conv_map
    (measurable_jumpTime n) ((measurable_pi_apply n).snd)
  change (rates.historyLaw μ).map (fun h ↦ jumpTime h n + (h n).2) = _ at hi
  simp_rw [← jumpTime_succ] at hi
  rw [rates.historyLaw_map_clock, rates.clockLaw_eq_expMeasure] at hi
  exact hi

/-- Each positive-index ring time has its elementary Erlang density. -/
theorem historyLaw_map_jumpTime_erlang (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (n : ℕ) :
    (rates.historyLaw μ).map (fun h ↦ jumpTime h (n + 1)) =
      volume.withDensity (erlangDensity rates.R n) := by
  induction n with
  | zero =>
    rw [rates.historyLaw_map_jumpTime_one, erlangDensity_zero]
    rfl
  | succ n ih =>
    rw [rates.historyLaw_map_jumpTime_succ μ (n + 1), ih]
    change Measure.conv (volume.withDensity (erlangDensity rates.R n))
      (volume.withDensity (exponentialPDF rates.R)) = _
    rw [Measure.conv_comm, conv_withDensity_eq_lconvolution
      (by unfold exponentialPDF; fun_prop) (measurable_erlangDensity rates.R n),
      exponential_lconvolution_erlangDensity rates.R_pos]

/-- The exponential upper tail at a nonnegative threshold. -/
theorem expMeasure_Ioi_of_nonneg {R s : ℝ} (hR : 0 < R) (hs : 0 ≤ s) :
    expMeasure R (Ioi s) = ENNReal.ofReal (Real.exp (-(R * s))) := by
  letI := isProbabilityMeasure_expMeasure hR
  have hc : expMeasure R (Iic s) = ENNReal.ofReal (1 - Real.exp (-(R * s))) := by
    rw [← ofReal_cdf, cdf_expMeasure_eq hR, if_pos hs]
  rw [← compl_Iic, measure_compl measurableSet_Iic (measure_ne_top _ _), measure_univ, hc]
  have he : Real.exp (-(R * s)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hR.le hs))
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (sub_nonneg.mpr he),
    sub_sub_cancel]

/-- The ring-count window has the Poisson probability with parameter `R * t`. -/
theorem historyLaw_jumpTime_window (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (t : ℝ≥0) (n : ℕ) :
    rates.historyLaw μ {h | jumpTime h n ≤ t ∧ (t : ℝ) < jumpTime h (n + 1)} =
      ENNReal.ofReal (Real.exp (-(rates.R * t)) * (rates.R * t) ^ n / n.factorial) := by
  cases n with
  | zero => exact rates.historyLaw_jumpTime_window_zero μ t
  | succ n =>
    letI := isProbabilityMeasure_expMeasure rates.R_pos
    let A : Set (ℝ × ℝ) := {p | p.1 ≤ t ∧ (t : ℝ) < p.1 + p.2}
    have hA : MeasurableSet A :=
      (measurableSet_le measurable_fst measurable_const).inter
        (measurableSet_lt measurable_const (measurable_fst.add measurable_snd))
    have hjoint := (rates.indepFun_jumpTime_clock μ (n + 1)).map_prod_eq_prod_map_map
      (measurable_jumpTime (n + 1)).aemeasurable
      ((measurable_pi_apply (n + 1)).snd).aemeasurable
    rw [rates.historyLaw_map_jumpTime_erlang, rates.historyLaw_map_clock,
      rates.clockLaw_eq_expMeasure] at hjoint
    have hwindow : rates.historyLaw μ
        {h | jumpTime h (n + 1) ≤ t ∧ (t : ℝ) < jumpTime h (n + 1 + 1)} =
        (volume.withDensity (erlangDensity rates.R n)).prod (expMeasure rates.R) A := by
      rw [← hjoint, Measure.map_apply (by fun_prop) hA]
      simp only [A, preimage_setOf_eq, jumpTime_succ]
    rw [hwindow, Measure.prod_apply hA,
      lintegral_withDensity_eq_lintegral_mul volume (measurable_erlangDensity rates.R n)
        (measurable_measure_prodMk_left hA)]
    have hfun (x : ℝ) : erlangDensity rates.R n x *
        expMeasure rates.R {y | (x, y) ∈ A} = ENNReal.ofReal rates.R⁻¹ *
          (erlangDensity rates.R n x * exponentialPDF rates.R (-x + t)) := by
      by_cases hx : x ≤ t
      · have hs : {y : ℝ | (x, y) ∈ A} = Ioi ((t : ℝ) - x) := by
          ext y
          simp only [A, mem_setOf_eq, mem_Ioi]
          constructor
          · intro h
            linarith [h.2]
          · intro h
            exact ⟨hx, by linarith⟩
        rw [hs, expMeasure_Ioi_of_nonneg rates.R_pos (sub_nonneg.mpr hx),
          exponentialPDF_of_nonneg (by linarith)]
        have hcancel : ENNReal.ofReal rates.R⁻¹ *
            ENNReal.ofReal (rates.R * Real.exp (-(rates.R * (-x + t)))) =
            ENNReal.ofReal (Real.exp (-(rates.R * ((t : ℝ) - x)))) := by
          rw [← ENNReal.ofReal_mul (inv_nonneg.mpr rates.R_pos.le)]
          congr 1
          rw [← mul_assoc, inv_mul_cancel₀ rates.R_pos.ne', one_mul]
          congr 2
          ring
        calc
          _ = erlangDensity rates.R n x *
              (ENNReal.ofReal rates.R⁻¹ *
                ENNReal.ofReal (rates.R * Real.exp (-(rates.R * (-x + t))))) := by
                  rw [hcancel]
          _ = _ := by ring
      · have hs : {y : ℝ | (x, y) ∈ A} = ∅ := by
          ext y
          simp only [A, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
          exact fun h ↦ (hx h).elim
        rw [hs, measure_empty, mul_zero, exponentialPDF_of_neg (by linarith),
          mul_zero, mul_zero]
    change (∫⁻ x, erlangDensity rates.R n x *
      expMeasure rates.R {y | (x, y) ∈ A}) = _
    rw [lintegral_congr hfun]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    change ENNReal.ofReal rates.R⁻¹ *
      lconvolution (erlangDensity rates.R n) (exponentialPDF rates.R) volume t = _
    rw [lconvolution_comm, exponential_lconvolution_erlangDensity rates.R_pos,
      erlangDensity, if_pos t.coe_nonneg,
      ← ENNReal.ofReal_mul (inv_nonneg.mpr rates.R_pos.le)]
    congr 1
    rw [← mul_assoc, inv_mul_cancel₀ rates.R_pos.ne', one_mul]

/-- The actual ring-count event has exactly the history window probability. -/
theorem regularLaw_ringCount_eq_window (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (t : ℝ≥0) (n : ℕ) :
    rates.regularLaw μ {h | h.ringCount t = n} =
      rates.historyLaw μ {h | jumpTime h n ≤ t ∧ (t : ℝ) < jumpTime h (n + 1)} := by
  have hset : {h : RegularHistory S | h.ringCount t = n} =
      Subtype.val ⁻¹' {h : History S |
        jumpTime h n ≤ t ∧ (t : ℝ) < jumpTime h (n + 1)} := by
    ext h
    exact h.ringCount_eq_iff t n
  rw [hset, ← Measure.map_apply
    (s := {h : History S | jumpTime h n ≤ t ∧ (t : ℝ) < jumpTime h (n + 1)})
    measurable_subtype_coe
    ((measurableSet_le (measurable_jumpTime n) measurable_const).inter
      (measurableSet_lt measurable_const (measurable_jumpTime (n + 1)))),
    rates.regularLaw_map_val]

/-- The actual number of rings at time `t` is Poisson with parameter `R * t`. -/
theorem regularLaw_ringCount (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (t : ℝ≥0) (n : ℕ) :
    rates.regularLaw μ {h | h.ringCount t = n} =
      ENNReal.ofReal (Real.exp (-(rates.R * t)) * (rates.R * t) ^ n / n.factorial) := by
  rw [rates.regularLaw_ringCount_eq_window, rates.historyLaw_jumpTime_window]

/-- The zero-ring probability also holds for the actual count on regular histories. -/
theorem regularLaw_ringCount_zero (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (t : ℝ≥0) :
    rates.regularLaw μ {h | h.ringCount t = 0} =
      ENNReal.ofReal (Real.exp (-(rates.R * t))) := by
  rw [rates.regularLaw_ringCount_eq_window, rates.historyLaw_jumpTime_window_zero]
  simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one]

end BoundedRates

end

end LatticeProb.JumpChain
