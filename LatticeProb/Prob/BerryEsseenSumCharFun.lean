/-
# Non-identically distributed Berry–Esseen: the product of characteristic functions

This file is route A2/A4 of the multivariate Berry–Esseen chain (`scratch/pk/mvbe-route.md`).  For
a finite family of centred probability laws `ν i` on `ℝ` with finite third absolute moments and
total variance `∑ σ_i² = 1`, write `ρ_i = ∫ |z|³ dν_i` and `ρ = ∑ ρ_i`.  The Gaussian
characteristic function is the product of the factors `exp (-σ_i² t²/2)`, and the telescoping
bound `LatticeProb.norm_prod_sub_prod_le_sum_exp` compares the two products.

* `LatticeProb.norm_prod_charFun_sub_gaussian_le` — for `ρ |t| ≤ 1/8`,
  `‖∏ φ_i t - exp (-t²/2)‖ ≤ 4 ρ |t|³ exp (-t²/3)`.

The summands are not identically distributed, so `σ_i² t² ≤ 2` cannot be assumed on the whole
window.  The indices with `σ_i² t² > 1` are handled separately: by Lyapunov (`σ_i³ ≤ ρ_i`) they
carry at most `ρ |t|³ ≤ t²/8` of the total variance `t²`, and their factors are only bounded by
`1`; the remaining indices carry the Gaussian decay used in the exponent.
-/
import Mathlib
import LatticeProb.Prob.BerryEsseenCharFun
import LatticeProb.Prob.ProdSubProd

open MeasureTheory ProbabilityTheory

namespace LatticeProb

/-- Lyapunov's inequality in terms of the standard deviation: for a centred probability law with
finite third absolute moment, `√(variance id ν) ^ 3 ≤ ∫ |z|³ dν`. -/
private theorem sqrt_variance_pow_three_le {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (h3 : Integrable (fun z : ℝ => |z| ^ 3) ν) :
    Real.sqrt (variance id ν) ^ 3 ≤ ∫ z, |z| ^ 3 ∂ν := by
  have h := variance_rpow_three_halves_le hmean h3
  rw [Real.rpow_div_two_eq_sqrt _ (variance_nonneg _ _), Real.rpow_ofNat] at h
  exact h

/-- Pointwise estimate for a small index: if `v t² ≤ 1` and `√v ^ 3 ≤ r`, then
`v² t⁴ ≤ r |t|³`. -/
private theorem sq_mul_pow_four_le {v r t : ℝ} (hv : 0 ≤ v) (hr : Real.sqrt v ^ 3 ≤ r)
    (h : v * t ^ 2 ≤ 1) : v ^ 2 * t ^ 4 ≤ r * |t| ^ 3 := by
  set x : ℝ := Real.sqrt v * |t| with hx
  have hx0 : 0 ≤ x := by positivity
  have hx2 : x ^ 2 = v * t ^ 2 := by
    rw [hx, mul_pow, Real.sq_sqrt hv, sq_abs]
  have hx1 : x ≤ 1 := by nlinarith
  have hx3 : x ^ 3 ≤ r * |t| ^ 3 := by
    rw [hx, mul_pow]
    exact mul_le_mul_of_nonneg_right hr (by positivity)
  have h4 : v ^ 2 * t ^ 4 = x ^ 4 := by
    have : x ^ 4 = (x ^ 2) ^ 2 := by ring
    rw [this, hx2]
    ring
  rw [h4]
  nlinarith [mul_nonneg (pow_nonneg hx0 3) (sub_nonneg.2 hx1)]

/-- Pointwise estimate for a large index: if `1 < v t²` and `√v ^ 3 ≤ r`, then
`v t² ≤ r |t|³`. -/
private theorem mul_sq_le_of_one_lt {v r t : ℝ} (hv : 0 ≤ v) (hr : Real.sqrt v ^ 3 ≤ r)
    (h : 1 < v * t ^ 2) : v * t ^ 2 ≤ r * |t| ^ 3 := by
  set x : ℝ := Real.sqrt v * |t| with hx
  have hx0 : 0 ≤ x := by positivity
  have hx2 : x ^ 2 = v * t ^ 2 := by
    rw [hx, mul_pow, Real.sq_sqrt hv, sq_abs]
  have hx1 : 1 ≤ x := by nlinarith
  have hx3 : x ^ 3 ≤ r * |t| ^ 3 := by
    rw [hx, mul_pow]
    exact mul_le_mul_of_nonneg_right hr (by positivity)
  nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.2 hx1)]

/-- The norm of a Gaussian factor `exp (-y)` with `y` a real number cast to `ℂ`. -/
private theorem norm_exp_neg_ofReal (y : ℝ) : ‖Complex.exp (-(y : ℂ))‖ = Real.exp (-y) := by
  rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal]

/-- The exponents `u k = -(v k t²/2) + r k |t|³/6` (kept only for `v k t² ≤ 1`, and replaced by
`0` otherwise) sum over any set of indices omitting `i` to at most `1/2 - 5 t²/12`, given that the
variances sum to `1`, `√(v k) ^ 3 ≤ r k` and `|t| ∑ r ≤ 1/8`. -/
private theorem sum_erase_expo_le {ι : Type*} [Fintype ι] [DecidableEq ι] (v r : ι → ℝ)
    (hv0 : ∀ i, 0 ≤ v i) (hr : ∀ i, Real.sqrt (v i) ^ 3 ≤ r i) (hvsum : ∑ i, v i = 1)
    {t : ℝ} (ht : |t| * ∑ i, r i ≤ 1 / 8) (i : ι) :
    ∑ k ∈ Finset.univ.erase i,
      (if v k * t ^ 2 ≤ 1 then -(v k * t ^ 2 / 2) + r k * |t| ^ 3 / 6 else 0) ≤
      1 / 2 - 5 * t ^ 2 / 12 := by
  have hr0 : ∀ k, 0 ≤ r k := fun k => le_trans (by positivity) (hr k)
  set c : ι → ℝ := fun k => if v k * t ^ 2 ≤ 1 then v k * t ^ 2 else 0 with hc
  have hrt : ∀ k, 0 ≤ r k * |t| ^ 3 := fun k => by have := hr0 k; positivity
  have hu : ∀ k, (if v k * t ^ 2 ≤ 1 then -(v k * t ^ 2 / 2) + r k * |t| ^ 3 / 6 else 0)
      ≤ -(c k / 2) + r k * |t| ^ 3 / 6 := by
    intro k
    have := hrt k
    by_cases h : v k * t ^ 2 ≤ 1
    · simp only [hc, if_pos h]
      linarith
    · simp only [hc, if_neg h]
      linarith
  have hcle : c i ≤ 1 := by
    by_cases h : v i * t ^ 2 ≤ 1
    · simp only [hc, if_pos h]
      exact h
    · simp only [hc, if_neg h]
      norm_num
  have hdiff : ∀ k, v k * t ^ 2 - c k ≤ r k * |t| ^ 3 := by
    intro k
    have := hrt k
    by_cases h : v k * t ^ 2 ≤ 1
    · simp only [hc, if_pos h]
      linarith
    · simp only [hc, if_neg h]
      have h' : 1 < v k * t ^ 2 := not_le.mp h
      have := mul_sq_le_of_one_lt (hv0 k) (hr k) h'
      linarith
  have hsumdiff : ∑ k, (v k * t ^ 2 - c k) ≤ (∑ k, r k) * |t| ^ 3 := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun k _ => hdiff k
  have hsumw : ∑ k, v k * t ^ 2 = t ^ 2 := by
    rw [← Finset.sum_mul, hvsum, one_mul]
  have hrho : (∑ k, r k) * |t| ^ 3 ≤ t ^ 2 / 8 := by
    calc (∑ k, r k) * |t| ^ 3 = (|t| * ∑ k, r k) * |t| ^ 2 := by ring
      _ ≤ 1 / 8 * |t| ^ 2 := mul_le_mul_of_nonneg_right ht (sq_nonneg _)
      _ = t ^ 2 / 8 := by rw [sq_abs]; ring
  have hC : t ^ 2 - t ^ 2 / 8 ≤ ∑ k, c k := by
    rw [Finset.sum_sub_distrib, hsumw] at hsumdiff
    linarith
  have hsplit : ∑ k ∈ Finset.univ.erase i, c k = ∑ k, c k - c i :=
    Finset.sum_erase_eq_sub (Finset.mem_univ i)
  have hrsub : ∑ k ∈ Finset.univ.erase i, r k * |t| ^ 3 / 6 ≤ ∑ k, r k * |t| ^ 3 / 6 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset i Finset.univ)
      (fun k _ _ => by have := hrt k; positivity)
  have hrall : ∑ k, r k * |t| ^ 3 / 6 = (∑ k, r k) * |t| ^ 3 / 6 := by
    rw [← Finset.sum_div, ← Finset.sum_mul]
  calc ∑ k ∈ Finset.univ.erase i,
        (if v k * t ^ 2 ≤ 1 then -(v k * t ^ 2 / 2) + r k * |t| ^ 3 / 6 else 0)
      ≤ ∑ k ∈ Finset.univ.erase i, (-(c k / 2) + r k * |t| ^ 3 / 6) :=
        Finset.sum_le_sum fun k _ => hu k
    _ = -(1 / 2) * ∑ k ∈ Finset.univ.erase i, c k
          + ∑ k ∈ Finset.univ.erase i, r k * |t| ^ 3 / 6 := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ ≤ 1 / 2 - 5 * t ^ 2 / 12 := by
        rw [hsplit]
        nlinarith

/-- The abstract form of the product estimate: for complex families `a b` whose moduli obey the
single-summand estimates, `‖∏ a - ∏ b‖ ≤ 4 (∑ r) |t|³ exp (-t²/3)`. -/
private theorem norm_prod_sub_prod_abstract {ι : Type*} [Fintype ι] (a b : ι → ℂ)
    (v r : ι → ℝ) (hv0 : ∀ i, 0 ≤ v i) (hr : ∀ i, Real.sqrt (v i) ^ 3 ≤ r i)
    (hvsum : ∑ i, v i = 1) {t : ℝ} (ht : |t| * ∑ i, r i ≤ 1 / 8)
    (ha : ∀ i, v i * t ^ 2 ≤ 1 → ‖a i‖ ≤ Real.exp (-(v i * t ^ 2 / 2) + r i * |t| ^ 3 / 6))
    (ha1 : ∀ i, ‖a i‖ ≤ 1)
    (hdiff : ∀ i, v i * t ^ 2 ≤ 1 → ‖a i - b i‖ ≤ r i * |t| ^ 3 / 6 + v i ^ 2 * t ^ 4 / 8)
    (hb : ∀ i, ‖b i‖ = Real.exp (-(v i * t ^ 2 / 2))) :
    ‖∏ i, a i - ∏ i, b i‖ ≤ 4 * (∑ i, r i) * |t| ^ 3 * Real.exp (-(t ^ 2 / 3)) := by
  classical
  have hr0 : ∀ k, 0 ≤ r k := fun k => le_trans (by positivity) (hr k)
  have hrt : ∀ k, 0 ≤ r k * |t| ^ 3 := fun k => by have := hr0 k; positivity
  have hw0 : ∀ k, 0 ≤ v k * t ^ 2 := fun k => mul_nonneg (hv0 k) (sq_nonneg t)
  set u : ι → ℝ := fun k =>
    if v k * t ^ 2 ≤ 1 then -(v k * t ^ 2 / 2) + r k * |t| ^ 3 / 6 else 0 with hu
  have hau : ∀ k ∈ (Finset.univ : Finset ι), ‖a k‖ ≤ Real.exp (u k) := by
    intro k _
    by_cases h : v k * t ^ 2 ≤ 1
    · simp only [hu, if_pos h]
      exact ha k h
    · simp only [hu, if_neg h, Real.exp_zero]
      exact ha1 k
  have hbu : ∀ k ∈ (Finset.univ : Finset ι), ‖b k‖ ≤ Real.exp (u k) := by
    intro k _
    rw [hb k]
    have := hrt k
    have := hw0 k
    by_cases h : v k * t ^ 2 ≤ 1
    · simp only [hu, if_pos h]
      exact Real.exp_le_exp.mpr (by linarith)
    · simp only [hu, if_neg h, Real.exp_zero]
      exact Real.exp_le_one_iff.mpr (by linarith)
  have hdiff2 : ∀ k, ‖a k - b k‖ ≤ 2 * r k * |t| ^ 3 := by
    intro k
    have := hrt k
    by_cases h : v k * t ^ 2 ≤ 1
    · have h1 := hdiff k h
      have h2 := sq_mul_pow_four_le (hv0 k) (hr k) h
      linarith
    · have h1 : 1 < v k * t ^ 2 := not_le.mp h
      have h2 := mul_sq_le_of_one_lt (hv0 k) (hr k) h1
      have h3 : ‖a k - b k‖ ≤ 2 := by
        calc ‖a k - b k‖ ≤ ‖a k‖ + ‖b k‖ := norm_sub_le _ _
          _ ≤ 1 + 1 := by
            refine add_le_add (ha1 k) ?_
            rw [hb k]
            exact Real.exp_le_one_iff.mpr (by linarith [hw0 k])
          _ = 2 := by norm_num
      linarith
  have hexp_half : Real.exp (1 / 2) ≤ 2 := by
    have h1 := Real.exp_one_lt_d9
    have h2 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    have h3 := Real.exp_pos (1 / 2)
    by_contra hcon
    have hcon' := not_le.mp hcon
    nlinarith
  have hE : Real.exp (1 / 2 - 5 * t ^ 2 / 12) ≤ 2 * Real.exp (-(t ^ 2 / 3)) := by
    rw [show 1 / 2 - 5 * t ^ 2 / 12 = 1 / 2 + (-(5 * t ^ 2 / 12)) by ring, Real.exp_add]
    exact mul_le_mul hexp_half (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg t]))
      (Real.exp_pos _).le (by norm_num)
  have h1 := norm_prod_sub_prod_le_sum_exp Finset.univ a b u hau hbu
  have hrsum : 0 ≤ ∑ i, r i := Finset.sum_nonneg fun i _ => hr0 i
  calc ‖∏ i, a i - ∏ i, b i‖
      ≤ ∑ i, ‖a i - b i‖ * Real.exp (∑ k ∈ Finset.univ.erase i, u k) := h1
    _ ≤ ∑ i, 2 * r i * |t| ^ 3 * Real.exp (1 / 2 - 5 * t ^ 2 / 12) := by
        refine Finset.sum_le_sum fun i _ => ?_
        refine mul_le_mul (hdiff2 i) (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le ?_
        · exact sum_erase_expo_le v r hv0 hr hvsum ht i
        · have := hrt i
          nlinarith
    _ = 2 * (∑ i, r i) * |t| ^ 3 * Real.exp (1 / 2 - 5 * t ^ 2 / 12) := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ 2 * (∑ i, r i) * |t| ^ 3 * (2 * Real.exp (-(t ^ 2 / 3))) :=
        mul_le_mul_of_nonneg_left hE (by positivity)
    _ = 4 * (∑ i, r i) * |t| ^ 3 * Real.exp (-(t ^ 2 / 3)) := by ring

/-- Characteristic-function comparison for sums of non-identically distributed summands.  Let `ν i`
be centred probability laws on `ℝ` with finite third absolute moments and `∑ σ_i² = 1`, and put
`ρ = ∑ ∫ |z|³ dν_i`.  For `|t| ρ ≤ 1/8`,
`‖∏ φ_i t - exp (-t²/2)‖ ≤ 4 ρ |t|³ exp (-t²/3)`. -/
theorem norm_prod_charFun_sub_gaussian_le {ι : Type*} [Fintype ι] (ν : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] (hmean : ∀ i, ∫ z, z ∂(ν i) = 0)
    (h3 : ∀ i, Integrable (fun z : ℝ => |z| ^ 3) (ν i))
    (hvar : ∑ i, variance id (ν i) = 1) {t : ℝ}
    (ht : |t| * ∑ i, ∫ z, |z| ^ 3 ∂(ν i) ≤ 1 / 8) :
    ‖∏ i, charFun (ν i) t - Complex.exp (-((t ^ 2 / 2 : ℝ) : ℂ))‖ ≤
      4 * (∑ i, ∫ z, |z| ^ 3 ∂(ν i)) * |t| ^ 3 * Real.exp (-(t ^ 2 / 3)) := by
  have hprod : Complex.exp (-((t ^ 2 / 2 : ℝ) : ℂ)) =
      ∏ i, Complex.exp (-((variance id (ν i) * t ^ 2 / 2 : ℝ) : ℂ)) := by
    rw [← Complex.exp_sum]
    congr 1
    rw [Finset.sum_neg_distrib, ← Complex.ofReal_sum, ← Finset.sum_div, ← Finset.sum_mul, hvar,
      one_mul]
  rw [hprod]
  exact norm_prod_sub_prod_abstract (fun i => charFun (ν i) t)
    (fun i => Complex.exp (-((variance id (ν i) * t ^ 2 / 2 : ℝ) : ℂ)))
    (fun i => variance id (ν i)) (fun i => ∫ z, |z| ^ 3 ∂(ν i))
    (fun i => variance_nonneg id (ν i)) (fun i => sqrt_variance_pow_three_le (hmean i) (h3 i))
    hvar ht
    (fun i hi => charFun_norm_le_exp_of_sq_le (hmean i) (h3 i) t (by linarith))
    (fun i => norm_charFun_le_one t)
    (fun i _ => charFun_sub_exp_le (hmean i) (h3 i) t)
    (fun i => norm_exp_neg_ofReal _)

end LatticeProb
