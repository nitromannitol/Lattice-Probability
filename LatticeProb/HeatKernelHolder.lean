/-
Power-integral bounds for heat-kernel Hölder estimates. The inequalities
`1 - exp(-c) ≤ c^α` and `(a+b)^(-γ) ≤ 2^(-γ) (ab)^(-γ/2)` give bounds
on double integrals over squares and offset rectangles.
-/
import Mathlib

open Real MeasureTheory

namespace LatticeProb.HeatKernelHolder

theorem one_sub_exp_neg_le_min (c : ℝ) (_hc : 0 ≤ c) : 1 - Real.exp (-c) ≤ min c 1 := by
  rcases le_total c 1 with h | h
  · rw [min_eq_left h]
    nlinarith [Real.add_one_le_exp (-c)]
  · rw [min_eq_right h]
    have := Real.exp_pos (-c)
    linarith

theorem min_le_rpow (c α : ℝ) (hc : 0 ≤ c) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) : min c 1 ≤ c ^ α := by
  rcases eq_or_lt_of_le hc with hc0 | hc0
  · rw [← hc0]
    rw [min_eq_left (by norm_num : (0:ℝ) ≤ 1)]
    positivity
  · rcases le_total c 1 with h | h
    · rw [min_eq_left h]
      calc c = c ^ (1:ℝ) := (Real.rpow_one c).symm
        _ ≤ c ^ α := Real.rpow_le_rpow_of_exponent_ge hc0 h hα1
    · rw [min_eq_right h]
      calc (1:ℝ) = 1 ^ α := (Real.one_rpow α).symm
        _ ≤ c ^ α := Real.rpow_le_rpow (by norm_num) h hα0

/-- **`1 - e^{-c} ≤ c^α` for `c ≥ 0`, `α ∈ [0,1]`.** -/
theorem one_sub_exp_neg_le_rpow (c α : ℝ) (hc : 0 ≤ c) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    1 - Real.exp (-c) ≤ c ^ α :=
  (one_sub_exp_neg_le_min c hc).trans (min_le_rpow c α hc hα0 hα1)

/-- **AM-GM: `(a+b)^{-γ} ≤ 2^{-γ}(ab)^{-γ/2}` for `a,b>0`, `γ ≥ 0`.** -/
theorem rpow_neg_add_le_rpow_neg_mul (a b γ : ℝ) (ha : 0 < a) (hb : 0 < b) (hγ : 0 ≤ γ) :
    (a + b) ^ (-γ) ≤ (2:ℝ) ^ (-γ) * (a * b) ^ (-γ / 2) := by
  have hAMGM : 2 * Real.sqrt (a*b) ≤ a + b := by
    nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), Real.sq_sqrt ha.le, Real.sq_sqrt hb.le,
      Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sqrt_mul ha.le b]
  have hpos : (0:ℝ) < 2 * Real.sqrt (a*b) := by positivity
  have hmono : (a+b) ^ (-γ) ≤ (2 * Real.sqrt (a*b)) ^ (-γ) :=
    Real.rpow_le_rpow_of_nonpos hpos hAMGM (by linarith)
  refine hmono.trans_eq ?_
  rw [Real.mul_rpow (by norm_num) (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
    ← Real.rpow_mul (by positivity)]
  congr 2
  ring

/-- Power integral over `Ioc 0 t`. -/
theorem integral_Ioc_rpow (t r : ℝ) (ht : 0 ≤ t) (hr : -1 < r) :
    ∫ a in Set.Ioc (0:ℝ) t, a ^ r = t ^ (r+1) / (r+1) := by
  rw [← intervalIntegral.integral_of_le ht]
  rw [integral_rpow (Or.inl hr)]
  rw [Real.zero_rpow (by linarith)]
  ring

/-- Power integral over `Ioc 0 t`, exponent written as `1 - γ/2`. -/
theorem integral_Ioc_rpow_one_sub_half (t γ : ℝ) (ht : 0 ≤ t) (hγ2 : γ < 2) :
    ∫ b in Set.Ioc (0:ℝ) t, b ^ (-γ/2) = t ^ (1 - γ/2) / (1 - γ/2) := by
  have hrm1 : (-1:ℝ) < -γ/2 := by linarith
  have hexp : -γ/2 + 1 = 1 - γ/2 := by ring
  rw [integral_Ioc_rpow t (-γ/2) ht hrm1, hexp]

/-- **The inner integral bound**: for fixed `a > 0`,
`∫ b in (0,t], (a+b)^{-γ} ≤ 2^{-γ}·a^{-γ/2}·(t^{1-γ/2}/(1-γ/2))`. -/
theorem integral_Ioc_rpow_neg_add_le (a t γ : ℝ) (ha : 0 < a) (ht : 0 ≤ t)
    (hγ0 : 0 ≤ γ) (hγ2 : γ < 2) :
    ∫ b in Set.Ioc (0:ℝ) t, (a + b) ^ (-γ)
      ≤ (2:ℝ) ^ (-γ) * a ^ (-γ/2) * (t ^ (1 - γ/2) / (1 - γ/2)) := by
  have hrm1 : (-1:ℝ) < -γ/2 := by linarith
  have hb_int : IntegrableOn (fun b : ℝ => b ^ (-γ/2)) (Set.Ioc (0:ℝ) t) volume :=
    (intervalIntegral.intervalIntegrable_rpow' hrm1).1
  have hdom_int : Integrable (fun b : ℝ => (2:ℝ)^(-γ) * a^(-γ/2) * b^(-γ/2))
      (volume.restrict (Set.Ioc (0:ℝ) t)) := by
    have := hb_int.const_mul ((2:ℝ)^(-γ) * a^(-γ/2))
    simpa [mul_assoc] using this
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc (0:ℝ) t)] fun b : ℝ => (a+b)^(-γ) :=
    ae_restrict_of_forall_mem measurableSet_Ioc
      (fun b hb => Real.rpow_nonneg (by linarith [hb.1]) _)
  have hbound : ∀ b ∈ Set.Ioc (0:ℝ) t, (a+b)^(-γ) ≤ (2:ℝ)^(-γ) * a^(-γ/2) * b^(-γ/2) := by
    intro b hb
    have hkey := rpow_neg_add_le_rpow_neg_mul a b γ ha hb.1 hγ0
    rwa [Real.mul_rpow ha.le hb.1.le, ← mul_assoc] at hkey
  calc ∫ b in Set.Ioc (0:ℝ) t, (a+b)^(-γ)
      ≤ ∫ b in Set.Ioc (0:ℝ) t, (2:ℝ)^(-γ) * a^(-γ/2) * b^(-γ/2) :=
        integral_mono_of_nonneg hnonneg hdom_int
          (ae_restrict_of_forall_mem measurableSet_Ioc hbound)
    _ = (2:ℝ)^(-γ) * a^(-γ/2) * (t ^ (1 - γ/2) / (1 - γ/2)) := by
        rw [MeasureTheory.integral_const_mul, integral_Ioc_rpow_one_sub_half t γ ht hγ2]

/-- **Double power integral bound**: `∫∫_{(0,t]²} (a+b)^{-γ} ≤ 2^{-γ}·(t^{1-γ/2}/(1-γ/2))²`
for `0 ≤ γ < 2`. -/
theorem doubleIntegral_rpow_neg_add_le (t γ : ℝ) (ht : 0 ≤ t) (hγ0 : 0 ≤ γ) (hγ2 : γ < 2) :
    ∫ a in Set.Ioc (0:ℝ) t, ∫ b in Set.Ioc (0:ℝ) t, (a + b) ^ (-γ)
      ≤ (2:ℝ) ^ (-γ) * (t ^ (1 - γ/2) / (1 - γ/2)) ^ 2 := by
  have hrm1 : (-1:ℝ) < -γ/2 := by linarith
  have ha_int : IntegrableOn (fun a : ℝ => a ^ (-γ/2)) (Set.Ioc (0:ℝ) t) volume :=
    (intervalIntegral.intervalIntegrable_rpow' hrm1).1
  have hdom_int : Integrable (fun a : ℝ => (2:ℝ)^(-γ) * a^(-γ/2) * (t ^ (1 - γ/2) / (1 - γ/2)))
      (volume.restrict (Set.Ioc (0:ℝ) t)) := by
    have h1 := ha_int.const_mul ((2:ℝ)^(-γ))
    have h2 := h1.mul_const (t ^ (1 - γ/2) / (1 - γ/2))
    simpa [mul_assoc] using h2
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc (0:ℝ) t)]
      fun a : ℝ => ∫ b in Set.Ioc (0:ℝ) t, (a+b)^(-γ) := by
    apply ae_restrict_of_forall_mem measurableSet_Ioc
    intro a ha
    apply MeasureTheory.integral_nonneg_of_ae
    exact ae_restrict_of_forall_mem measurableSet_Ioc
      (fun b hb => Real.rpow_nonneg (by linarith [ha.1, hb.1]) _)
  have hbound : ∀ a ∈ Set.Ioc (0:ℝ) t,
      (∫ b in Set.Ioc (0:ℝ) t, (a+b)^(-γ))
        ≤ (2:ℝ)^(-γ) * a^(-γ/2) * (t ^ (1 - γ/2) / (1 - γ/2)) :=
    fun a ha => integral_Ioc_rpow_neg_add_le a t γ ha.1 ht hγ0 hγ2
  calc ∫ a in Set.Ioc (0:ℝ) t, ∫ b in Set.Ioc (0:ℝ) t, (a+b)^(-γ)
      ≤ ∫ a in Set.Ioc (0:ℝ) t,
          (2:ℝ)^(-γ) * a^(-γ/2) * (t ^ (1 - γ/2) / (1 - γ/2)) :=
        integral_mono_of_nonneg hnonneg hdom_int
          (ae_restrict_of_forall_mem measurableSet_Ioc hbound)
    _ = (2:ℝ) ^ (-γ) * (t ^ (1 - γ/2) / (1 - γ/2)) ^ 2 := by
        rw [show (fun a : ℝ => (2:ℝ)^(-γ) * a^(-γ/2) * (t ^ (1 - γ/2) / (1 - γ/2)))
              = (fun a : ℝ => ((2:ℝ)^(-γ) * (t ^ (1 - γ/2) / (1 - γ/2))) * a^(-γ/2)) from by
            funext a; ring]
        rw [MeasureTheory.integral_const_mul, integral_Ioc_rpow_one_sub_half t γ ht hγ2]
        ring

/-- **Subadditivity of a concave power**: `t^p - t'^p ≤ (t-t')^p` for `0 ≤ t' ≤ t`, `0 ≤ p ≤ 1`. -/
theorem rpow_sub_rpow_le_rpow_sub (t' t p : ℝ) (ht' : 0 ≤ t') (htt' : t' ≤ t)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    t ^ p - t' ^ p ≤ (t - t') ^ p := by
  have hsub : (0:ℝ) ≤ t - t' := by linarith
  have hkey := Real.rpow_add_le_add_rpow hsub ht' hp0 hp1
  have heq : t - t' + t' = t := by ring
  rw [heq] at hkey
  linarith

/-- Exact power integral over `Ioc t' t` (general lower endpoint). -/
theorem integral_Ioc_rpow_offset (t' t r : ℝ) (htt' : t' ≤ t) (hr : -1 < r) :
    ∫ a in Set.Ioc t' t, a ^ r = (t ^ (r+1) - t' ^ (r+1)) / (r+1) := by
  rw [← intervalIntegral.integral_of_le htt']
  rw [integral_rpow (Or.inl hr)]

/-- **Bound on the power integral over `Ioc t' t`** via subadditivity of the concave power. -/
theorem integral_Ioc_rpow_offset_le (t' t γ : ℝ) (ht' : 0 ≤ t') (htt' : t' ≤ t)
    (hγ0 : 0 ≤ γ) (hγ2 : γ < 2) :
    ∫ a in Set.Ioc t' t, a ^ (-γ/2) ≤ (t - t') ^ (1 - γ/2) / (1 - γ/2) := by
  have hrm1 : (-1:ℝ) < -γ/2 := by linarith
  have hexp : -γ/2 + 1 = 1 - γ/2 := by ring
  rw [integral_Ioc_rpow_offset t' t (-γ/2) htt' hrm1, hexp]
  have hp0 : (0:ℝ) ≤ 1 - γ/2 := by linarith
  have hp1 : (1:ℝ) - γ/2 ≤ 1 := by linarith
  have hsub := rpow_sub_rpow_le_rpow_sub t' t (1 - γ/2) ht' htt' hp0 hp1
  have hpos : (0:ℝ) < 1 - γ/2 := by linarith
  exact (div_le_div_iff_of_pos_right hpos).mpr hsub

/-- **The offset rectangle double integral bound**: for `0 ≤ t' ≤ t`, `0 ≤ B`, `0 ≤ γ < 2`,
`∫_{a∈(t',t]}∫_{b∈(0,B]} (a+b)^{-γ} ≤ 2^{-γ}·((t-t')^{1-γ/2}/(1-γ/2))·(B^{1-γ/2}/(1-γ/2))`. -/
theorem doubleIntegral_rpow_neg_add_le_offset (t' t B γ : ℝ) (ht' : 0 ≤ t') (htt' : t' ≤ t)
    (hB : 0 ≤ B) (hγ0 : 0 ≤ γ) (hγ2 : γ < 2) :
    ∫ a in Set.Ioc t' t, ∫ b in Set.Ioc (0:ℝ) B, (a + b) ^ (-γ)
      ≤ (2:ℝ) ^ (-γ) * ((t - t') ^ (1 - γ/2) / (1 - γ/2)) * (B ^ (1 - γ/2) / (1 - γ/2)) := by
  have hrm1 : (-1:ℝ) < -γ/2 := by linarith
  have ha_int : IntegrableOn (fun a : ℝ => a ^ (-γ/2)) (Set.Ioc t' t) volume :=
    (intervalIntegral.intervalIntegrable_rpow' hrm1).1
  have hdom_int : Integrable (fun a : ℝ => (2:ℝ)^(-γ) * a^(-γ/2) * (B ^ (1 - γ/2) / (1 - γ/2)))
      (volume.restrict (Set.Ioc t' t)) := by
    have h1 := ha_int.const_mul ((2:ℝ)^(-γ))
    have h2 := h1.mul_const (B ^ (1 - γ/2) / (1 - γ/2))
    simpa [mul_assoc] using h2
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc t' t)]
      fun a : ℝ => ∫ b in Set.Ioc (0:ℝ) B, (a+b)^(-γ) := by
    apply ae_restrict_of_forall_mem measurableSet_Ioc
    intro a ha
    have ha0 : 0 < a := lt_of_le_of_lt ht' ha.1
    apply MeasureTheory.integral_nonneg_of_ae
    exact ae_restrict_of_forall_mem measurableSet_Ioc
      (fun b hb => Real.rpow_nonneg (by linarith [ha0, hb.1]) _)
  have hbound : ∀ a ∈ Set.Ioc t' t,
      (∫ b in Set.Ioc (0:ℝ) B, (a+b)^(-γ))
        ≤ (2:ℝ)^(-γ) * a^(-γ/2) * (B ^ (1 - γ/2) / (1 - γ/2)) := by
    intro a ha
    have ha0 : 0 < a := lt_of_le_of_lt ht' ha.1
    exact integral_Ioc_rpow_neg_add_le a B γ ha0 hB hγ0 hγ2
  calc ∫ a in Set.Ioc t' t, ∫ b in Set.Ioc (0:ℝ) B, (a+b)^(-γ)
      ≤ ∫ a in Set.Ioc t' t,
          (2:ℝ)^(-γ) * a^(-γ/2) * (B ^ (1 - γ/2) / (1 - γ/2)) :=
        integral_mono_of_nonneg hnonneg hdom_int
          (ae_restrict_of_forall_mem measurableSet_Ioc hbound)
    _ ≤ (2:ℝ) ^ (-γ) * ((t - t') ^ (1 - γ/2) / (1 - γ/2)) * (B ^ (1 - γ/2) / (1 - γ/2)) := by
        rw [show (fun a : ℝ => (2:ℝ)^(-γ) * a^(-γ/2) * (B ^ (1 - γ/2) / (1 - γ/2)))
              = (fun a : ℝ => ((2:ℝ)^(-γ) * (B ^ (1 - γ/2) / (1 - γ/2))) * a^(-γ/2)) from by
            funext a; ring]
        rw [MeasureTheory.integral_const_mul]
        have hb := integral_Ioc_rpow_offset_le t' t γ ht' htt' hγ0 hγ2
        have h2pos : (0:ℝ) ≤ (2:ℝ)^(-γ) * (B ^ (1 - γ/2) / (1 - γ/2)) := by
          have hp0 : (0:ℝ) ≤ 1 - γ/2 := by linarith
          exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
            (div_nonneg (Real.rpow_nonneg hB _) hp0)
        calc (2:ℝ)^(-γ) * (B ^ (1 - γ/2) / (1 - γ/2)) * ∫ a in Set.Ioc t' t, a^(-γ/2)
            ≤ (2:ℝ)^(-γ) * (B ^ (1 - γ/2) / (1 - γ/2)) * ((t - t') ^ (1 - γ/2) / (1 - γ/2)) :=
              mul_le_mul_of_nonneg_left hb h2pos
          _ = (2:ℝ) ^ (-γ) * ((t - t') ^ (1 - γ/2) / (1 - γ/2)) * (B ^ (1 - γ/2) / (1 - γ/2)) := by
              ring

end LatticeProb.HeatKernelHolder
