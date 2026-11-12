import Mathlib

/-!
# From a geometric family of tail bounds to a polynomial tail

Suppose a family of events `T 𝕣 c`, indexed by a scale `𝕣 > 0` and a multiplier `c`, satisfies for every small `ε`
the bound
`P(T 𝕣 (A ε^{-a})) ≤ K ε^{e₁} + C₄ ε^{e₂}`
with `a > 0` and exponents `e₁, e₂ ≥ m a`. Choosing `ε = (A / c)^{1/a}`, so that `A ε^{-a} = c`, gives for all large
`c` the polynomial tail `P(T 𝕣 c) ≤ K₀ c^{-m}` with `K₀ = (|K| + |C₄|) A^m`, uniformly in `𝕣`.
-/

namespace LatticeProb

open MeasureTheory Set
open scoped ENNReal

/-- **Polynomial tail from a one-parameter family of tail bounds.** The multiplier `c` is related to the parameter `ε`
by `c = A ε^{-a}`; the exponents `e₁, e₂` of the two error terms are at least `m a`. -/
theorem exists_polynomial_tail_of_scale_family {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (T : ℝ → ℝ → Set Ω) {A a ε₁ K C₄ e₁ e₂ m : ℝ} (hA : 0 < A) (ha : 0 < a) (hε₁ : 0 < ε₁)
    (he₁ : m * a ≤ e₁) (he₂ : m * a ≤ e₂)
    (h : ∀ 𝕣 : ℝ, 0 < 𝕣 → ∀ ε ∈ Ioo (0 : ℝ) ε₁,
      P (T 𝕣 (A * ε ^ (-a))) ≤ ENNReal.ofReal (K * ε ^ e₁) + ENNReal.ofReal (C₄ * ε ^ e₂)) :
    ∃ C₀ K₀ : ℝ, 0 < C₀ ∧ ∀ c : ℝ, C₀ ≤ c → ∀ 𝕣 : ℝ, 0 < 𝕣 →
      P (T 𝕣 c) ≤ ENNReal.ofReal (K₀ * c ^ (-m)) := by
  have hεa : 0 < ε₁ ^ a := Real.rpow_pos_of_pos hε₁ a
  set C₀ : ℝ := max (A * ε₁ ^ (-a)) A + 1 with hC₀
  have hC₀A : A < C₀ := by
    have := le_max_right (A * ε₁ ^ (-a)) A
    linarith
  have hC₀ε : A * ε₁ ^ (-a) < C₀ := by
    have := le_max_left (A * ε₁ ^ (-a)) A
    linarith
  refine ⟨C₀, (|K| + |C₄|) * A ^ m, hA.trans hC₀A, ?_⟩
  intro c hc 𝕣 h𝕣
  have hcA : A < c := lt_of_lt_of_le hC₀A hc
  have hcpos : 0 < c := hA.trans hcA
  have hAc : 0 < A / c := div_pos hA hcpos
  set ε : ℝ := (A / c) ^ (1 / a) with hε
  have hεpos : 0 < ε := Real.rpow_pos_of_pos hAc _
  have hε1 : ε < 1 :=
    Real.rpow_lt_one hAc.le ((div_lt_one hcpos).2 hcA) (by positivity)
  have hεa' : ε ^ a = A / c := by
    rw [hε, ← Real.rpow_mul hAc.le, one_div_mul_cancel ha.ne', Real.rpow_one]
  have hεε₁ : ε < ε₁ := by
    have h1 : A * (ε₁ ^ a)⁻¹ < c := by
      have := hC₀ε
      rw [Real.rpow_neg hε₁.le] at this
      exact lt_of_lt_of_le this hc
    rw [mul_inv_lt_iff₀ hεa] at h1
    have h2 : ε ^ a < ε₁ ^ a := by
      rw [hεa', div_lt_iff₀ hcpos]
      linarith
    exact (Real.rpow_lt_rpow_iff hεpos.le hε₁.le ha).1 h2
  have hAε : A * ε ^ (-a) = c := by
    rw [Real.rpow_neg hεpos.le, hεa', inv_div]
    field_simp
  have hbound := h 𝕣 h𝕣 ε ⟨hεpos, hεε₁⟩
  rw [hAε] at hbound
  refine hbound.trans ?_
  have hpow : ε ^ (m * a) = A ^ m * c ^ (-m) := by
    rw [mul_comm, Real.rpow_mul hεpos.le, hεa', Real.div_rpow hA.le hcpos.le, Real.rpow_neg hcpos.le,
      div_eq_mul_inv]
  have hK : K * ε ^ e₁ ≤ |K| * (A ^ m * c ^ (-m)) := by
    rw [← hpow]
    calc K * ε ^ e₁ ≤ |K| * ε ^ e₁ := mul_le_mul_of_nonneg_right (le_abs_self K) (Real.rpow_nonneg hεpos.le _)
      _ ≤ |K| * ε ^ (m * a) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hεpos hε1.le he₁) (abs_nonneg K)
  have hC : C₄ * ε ^ e₂ ≤ |C₄| * (A ^ m * c ^ (-m)) := by
    rw [← hpow]
    calc C₄ * ε ^ e₂ ≤ |C₄| * ε ^ e₂ := mul_le_mul_of_nonneg_right (le_abs_self C₄) (Real.rpow_nonneg hεpos.le _)
      _ ≤ |C₄| * ε ^ (m * a) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hεpos hε1.le he₂) (abs_nonneg C₄)
  have hnn : 0 ≤ A ^ m * c ^ (-m) := mul_nonneg (Real.rpow_nonneg hA.le _) (Real.rpow_nonneg hcpos.le _)
  calc ENNReal.ofReal (K * ε ^ e₁) + ENNReal.ofReal (C₄ * ε ^ e₂)
      ≤ ENNReal.ofReal (|K| * (A ^ m * c ^ (-m))) + ENNReal.ofReal (|C₄| * (A ^ m * c ^ (-m))) :=
        add_le_add (ENNReal.ofReal_le_ofReal hK) (ENNReal.ofReal_le_ofReal hC)
    _ = ENNReal.ofReal ((|K| + |C₄|) * A ^ m * c ^ (-m)) := by
        rw [← ENNReal.ofReal_add (mul_nonneg (abs_nonneg K) hnn) (mul_nonneg (abs_nonneg C₄) hnn)]
        congr 1
        ring

end LatticeProb
