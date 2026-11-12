import Mathlib

/-!
# Negative powers of a mean, and the Laplace transform from a negative moment

* `LatticeProb.measure_univ_rpow_le_lintegral_rpow_mul`: for `g > 0` finite and `r > 0`,
  `μ(univ)^{1+r} ≤ (∫ g dμ)^r · ∫ g^{-r} dμ`  (reverse Hölder / Jensen for `x ↦ x^{-r}`).
* `LatticeProb.exp_neg_le_rpow_neg`: `exp(-u) ≤ s^s e^{-s} u^{-s}` for `u, s > 0`.
* `LatticeProb.integral_exp_neg_le_of_lintegral_rpow_neg_le`: if `Z` is a.e. finite with `E Z^{-s} ≤ K` then
  `E exp(-λ Z) ≤ s^s e^{-s} K λ^{-s}` for every `λ > 0` (and `Z > 0` a.s.).
-/

open MeasureTheory Set
open scoped ENNReal

namespace LatticeProb

section ReverseHolder

variable {α : Type*} [MeasurableSpace α]

/-- **Negative power of a mean** (reverse Hölder). If `0 < g < ∞` everywhere and `r > 0`, then
`μ(univ)^{1+r} ≤ (∫ g dμ)^r ∫ g^{-r} dμ`. -/
theorem measure_univ_rpow_le_lintegral_rpow_mul (μ : Measure α) {g : α → ℝ≥0∞} (hg : AEMeasurable g μ)
    (h0 : ∀ x, g x ≠ 0) (htop : ∀ x, g x ≠ ⊤) {r : ℝ} (hr : 0 < r) :
    μ univ ^ (1 + r) ≤ (∫⁻ x, g x ∂μ) ^ r * ∫⁻ x, g x ^ (-r) ∂μ := by
  set a : ℝ := r / (1 + r) with ha
  have h1r : 0 < 1 + r := by linarith
  have hpq : (1 + r).HolderConjugate ((1 + r) / r) := by
    rw [Real.holderConjugate_iff]
    refine ⟨by linarith, ?_⟩
    field_simp
  have hf : AEMeasurable (fun x => g x ^ (-a)) μ := hg.pow_const _
  have hh : AEMeasurable (fun x => g x ^ a) μ := hg.pow_const _
  have hmul : ∀ x, (fun x => g x ^ (-a)) x * (fun x => g x ^ a) x = 1 := by
    intro x
    simp only
    rw [← ENNReal.rpow_add _ _ (h0 x) (htop x)]
    simp
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf hh
  have hlhs : ∫⁻ x, ((fun x => g x ^ (-a)) * (fun x => g x ^ a)) x ∂μ = μ univ := by
    have : ∀ x, ((fun x => g x ^ (-a)) * (fun x => g x ^ a)) x = 1 := hmul
    simp only [this, lintegral_const, one_mul]
  have hf_p : ∀ x, (g x ^ (-a)) ^ (1 + r) = g x ^ (-r) := by
    intro x
    rw [← ENNReal.rpow_mul]
    congr 1
    rw [ha]
    field_simp
  have hh_q : ∀ x, (g x ^ a) ^ ((1 + r) / r) = g x := by
    intro x
    rw [← ENNReal.rpow_mul]
    have : a * ((1 + r) / r) = 1 := by
      rw [ha]
      field_simp
    rw [this, ENNReal.rpow_one]
  rw [hlhs] at hH
  simp only [hf_p, hh_q] at hH
  have h1p : 1 / (1 + r) * (1 + r) = 1 := by field_simp
  have h1q : 1 / ((1 + r) / r) = a := by
    rw [ha]
    field_simp
  rw [h1q] at hH
  have hpow := ENNReal.rpow_le_rpow hH h1r.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ h1r.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, h1p,
    ENNReal.rpow_one] at hpow
  have h2 : a * (1 + r) = r := by
    rw [ha]
    field_simp
  rw [h2] at hpow
  rw [mul_comm]
  exact hpow

end ReverseHolder

/-- **Elementary bound.** For `u, s > 0`, `exp(-u) ≤ s^s e^{-s} u^{-s}`. -/
theorem exp_neg_le_rpow_neg {u s : ℝ} (hu : 0 < u) (hs : 0 < s) :
    Real.exp (-u) ≤ s ^ s * Real.exp (-s) * u ^ (-s) := by
  set t : ℝ := u / s with ht
  have ht0 : 0 < t := div_pos hu hs
  have hts : t * s = u := by rw [ht]; field_simp
  have h1 : t ≤ Real.exp (t - 1) := by
    have := Real.add_one_le_exp (t - 1)
    linarith
  have h2 : Real.exp (-t) ≤ Real.exp (-1) / t := by
    rw [le_div_iff₀ ht0]
    calc Real.exp (-t) * t ≤ Real.exp (-t) * Real.exp (t - 1) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = Real.exp (-1) := by rw [← Real.exp_add]; ring_nf
  have h3 : Real.exp (-u) = Real.exp (-t) ^ s := by
    rw [← Real.exp_mul]
    congr 1
    rw [← hts]
    ring
  rw [h3]
  calc Real.exp (-t) ^ s ≤ (Real.exp (-1) / t) ^ s :=
        Real.rpow_le_rpow (Real.exp_pos _).le h2 hs.le
    _ = Real.exp (-s) * t ^ (-s) := by
        rw [Real.div_rpow (Real.exp_pos _).le ht0.le, ← Real.exp_mul, Real.rpow_neg ht0.le]
        ring_nf
    _ = s ^ s * Real.exp (-s) * u ^ (-s) := by
        rw [ht, Real.div_rpow hu.le hs.le, Real.rpow_neg hs.le]
        have hs' : 0 < s ^ s := Real.rpow_pos_of_pos hs s
        field_simp

section Laplace

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Laplace transform from a negative moment.** If `Z : Ω → [0, ∞]` is a.e. finite and measurable with
`E Z^{-s} ≤ K` then `E exp(-λ Z) ≤ s^s e^{-s} K λ^{-s}` for every `λ > 0`. -/
theorem integral_exp_neg_le_of_lintegral_rpow_neg_le [IsProbabilityMeasure P] {Z : Ω → ℝ≥0∞}
    (hZ : AEMeasurable Z P) (hfin : ∀ᵐ ω ∂P, Z ω < ⊤) {s K : ℝ} (hs : 0 < s) (hK : 0 ≤ K)
    (hmom : ∫⁻ ω, Z ω ^ (-s) ∂P ≤ ENNReal.ofReal K) {lam : ℝ} (hlam : 0 < lam) :
    ∫ ω, Real.exp (-(lam * (Z ω).toReal)) ∂P ≤ s ^ s * Real.exp (-s) * K * lam ^ (-s) := by
  have hmeas : AEMeasurable (fun ω => Z ω ^ (-s)) P := hZ.pow_const _
  have hne : ∫⁻ ω, Z ω ^ (-s) ∂P ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmom
  have hlt : ∀ᵐ ω ∂P, Z ω ^ (-s) < ⊤ := ae_lt_top' hmeas hne
  have hpos : ∀ᵐ ω ∂P, 0 < (Z ω).toReal := by
    filter_upwards [hlt, hfin] with ω h1 h2
    refine ENNReal.toReal_pos ?_ h2.ne
    intro h0
    rw [h0, ENNReal.zero_rpow_of_neg (by linarith)] at h1
    exact lt_irrefl _ h1
  set G : Ω → ℝ := fun ω => (Z ω ^ (-s)).toReal with hG
  have hGi : Integrable G P := integrable_toReal_of_lintegral_ne_top hmeas hne
  have hGint : ∫ ω, G ω ∂P ≤ K := by
    rw [hG, integral_toReal hmeas hlt]
    exact ENNReal.toReal_le_of_le_ofReal hK hmom
  have hGeq : ∀ ω, G ω = (Z ω).toReal ^ (-s) := fun ω => (ENNReal.toReal_rpow _ _).symm
  have hc : 0 ≤ s ^ s * Real.exp (-s) * lam ^ (-s) := by positivity
  calc ∫ ω, Real.exp (-(lam * (Z ω).toReal)) ∂P
      ≤ ∫ ω, (s ^ s * Real.exp (-s) * lam ^ (-s)) * G ω ∂P := by
        refine integral_mono_of_nonneg (ae_of_all _ fun ω => (Real.exp_pos _).le)
          (hGi.const_mul _) ?_
        filter_upwards [hpos] with ω h1
        rw [hGeq ω]
        have := exp_neg_le_rpow_neg (mul_pos hlam h1) hs
        rw [Real.mul_rpow hlam.le h1.le] at this
        calc Real.exp (-(lam * (Z ω).toReal))
            ≤ s ^ s * Real.exp (-s) * (lam ^ (-s) * (Z ω).toReal ^ (-s)) := this
          _ = _ := by ring
    _ = (s ^ s * Real.exp (-s) * lam ^ (-s)) * ∫ ω, G ω ∂P := integral_const_mul _ _
    _ ≤ (s ^ s * Real.exp (-s) * lam ^ (-s)) * K := mul_le_mul_of_nonneg_left hGint hc
    _ = s ^ s * Real.exp (-s) * K * lam ^ (-s) := by ring

end Laplace

end LatticeProb
