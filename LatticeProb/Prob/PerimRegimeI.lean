import Mathlib
import LatticeProb.Prob.PerimCoord
import LatticeProb.Prob.PerimTilt

/-!
# Regime I (small `t`) of the two-regime arithmetic for the orthant perimeter bound (packet Q8a)

With `H = √(2 log m)` and `t₀ = 1/(2 (1 + H))`, we prove, for `m ≥ 2`, `h : Fin m → ℝ` and
`0 < t ≤ t₀`, that the right-hand side of the tilted Cauchy-Schwarz chain `perim_tilt_chain`,
`Rhs h t = e² e^{-U} √(min 1 Q) √(2Q + 2t²E2 + 4E4 + 4e E2²)`, satisfies
`Rhs h t ≤ 1000 (1 + H) t` (hence also `≤ 1000 (1 + H)² t`).

Route: density-type bounds `Q ≤ 0.887 t Θ`, `E2 ≤ 0.4432 t Θ`, `E4 ≤ 0.665 t Θ` with
`Θ = ∑ φ(h_j⁺)`; for small coordinates (`h_j < H`) `φ(h_j⁺) ≤ 10 (1 + H) u_j` (hazard bound
and `u ≥ 0.632 Φ̄(h + t)`), for big coordinates `∑ φ(h_j) ≤ 2/5`; so `Θ ≤ 10 (1 + H) U + 2/5`
and `e^{-U} Θ` is controlled by `U e^{-U} ≤ 1`, `U² e^{-U} ≤ 2`.
-/

open MeasureTheory ProbabilityTheory Set Finset

namespace LatticeProb

/-! ### Elementary exponential bounds -/

lemma perimR1_exp_one_sq_le : Real.exp 1 ^ 2 ≤ 37 / 5 := by
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h0 : 0 < Real.exp 1 := Real.exp_pos 1
  nlinarith

lemma perimR1_exp_one_le : Real.exp 1 ≤ 3 := by
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  linarith

lemma perimR1_exp_neg_mul_le (U : ℝ) : Real.exp (-U) * U ≤ 1 := by
  have h1 : U + 1 ≤ Real.exp U := Real.add_one_le_exp U
  have h2 : Real.exp (-U) * Real.exp U = 1 := by rw [← Real.exp_add]; simp
  have h3 : 0 ≤ Real.exp (-U) := (Real.exp_pos _).le
  nlinarith

lemma perimR1_exp_neg_mul_sq_le {U : ℝ} (hU : 0 ≤ U) : Real.exp (-U) * U ^ 2 ≤ 2 := by
  have h1 : 1 + U + U ^ 2 / 2 ≤ Real.exp U := Real.quadratic_le_exp_of_nonneg hU
  have h2 : Real.exp (-U) * Real.exp U = 1 := by rw [← Real.exp_add]; simp
  have h3 : 0 ≤ Real.exp (-U) := (Real.exp_pos _).le
  nlinarith [sq_nonneg U]

lemma perimR1_exp_neg_le_one {U : ℝ} (hU : 0 ≤ U) : Real.exp (-U) ≤ 1 := by
  rw [Real.exp_le_one_iff]; linarith

/-! ### The pure arithmetic of Regime I -/

/-- The arithmetic core of Regime I: from the density-type bounds and `Θ ≤ 10 B U + 2/5` with
`t B ≤ 1/2`, the right-hand side of the chain is at most `1000 B t`. -/
theorem perimR1_arith {U Θ Q E2 E4 t B : ℝ} (hU : 0 ≤ U) (hΘ : 0 ≤ Θ) (ht : 0 < t)
    (hB : 1 ≤ B) (htB : t * B ≤ 1 / 2) (hQ0 : 0 ≤ Q) (hE20 : 0 ≤ E2)
    (hQ : Q ≤ 887 / 1000 * (t * Θ)) (hE2 : E2 ≤ 4432 / 10000 * (t * Θ))
    (hE4 : E4 ≤ 665 / 1000 * (t * Θ)) (hΘU : Θ ≤ 10 * B * U + 2 / 5) :
    Real.exp 1 ^ 2 * Real.exp (-U) * √(min 1 Q) *
      √(2 * Q + 2 * t ^ 2 * E2 + 4 * E4 + 4 * Real.exp 1 * E2 ^ 2) ≤ 1000 * B * t := by
  set Y : ℝ := t * Θ with hYdef
  have hY : 0 ≤ Y := mul_nonneg ht.le hΘ
  have ht2 : t ≤ 1 / 2 := by nlinarith
  have hYU : Y ≤ 5 * U + 1 / 5 := by
    have h1 : Y ≤ t * (10 * B * U + 2 / 5) := mul_le_mul_of_nonneg_left hΘU ht.le
    have h2 : t * (10 * B * U + 2 / 5) = 10 * (t * B) * U + 2 / 5 * t := by ring
    have h3 : 10 * (t * B) * U ≤ 5 * U := by nlinarith
    nlinarith
  -- the first square root
  have hmin : √(min 1 Q) ≤ √Y := by
    apply Real.sqrt_le_sqrt
    exact (min_le_right 1 Q).trans (hQ.trans (by nlinarith))
  -- the second square root
  have he3 : Real.exp 1 ≤ 3 := perimR1_exp_one_le
  have hE2sq : E2 ^ 2 ≤ (4432 / 10000 * Y) ^ 2 := by
    apply pow_le_pow_left₀ hE20 hE2
  have hS : 2 * Q + 2 * t ^ 2 * E2 + 4 * E4 + 4 * Real.exp 1 * E2 ^ 2 ≤ Y * (5 + 3 * Y) := by
    have h1 : 2 * t ^ 2 * E2 ≤ 2 * (1 / 4) * E2 := by
      have : t ^ 2 ≤ 1 / 4 := by nlinarith
      nlinarith
    have h2 : 4 * Real.exp 1 * E2 ^ 2 ≤ 4 * 3 * (4432 / 10000 * Y) ^ 2 := by
      have := Real.exp_pos 1
      calc 4 * Real.exp 1 * E2 ^ 2 ≤ 4 * 3 * E2 ^ 2 := by nlinarith [sq_nonneg E2]
        _ ≤ 4 * 3 * (4432 / 10000 * Y) ^ 2 := by nlinarith
    nlinarith
  have hS0 : 0 ≤ 5 + 3 * Y := by linarith
  have hsq : √(2 * Q + 2 * t ^ 2 * E2 + 4 * E4 + 4 * Real.exp 1 * E2 ^ 2)
      ≤ √Y * √(5 + 3 * Y) := by
    rw [← Real.sqrt_mul hY]
    exact Real.sqrt_le_sqrt hS
  have hroot : √(5 + 3 * Y) ≤ 3 + 5 * U := by
    rw [Real.sqrt_le_iff]
    constructor
    · linarith
    · nlinarith
  have hYY : √Y * √Y = Y := Real.mul_self_sqrt hY
  -- the product of the two square roots
  have hprod : √(min 1 Q) *
      √(2 * Q + 2 * t ^ 2 * E2 + 4 * E4 + 4 * Real.exp 1 * E2 ^ 2) ≤ Y * (3 + 5 * U) := by
    have hm0 : 0 ≤ √(min 1 Q) := Real.sqrt_nonneg _
    have hs0 : 0 ≤ √Y := Real.sqrt_nonneg _
    calc √(min 1 Q) * √(2 * Q + 2 * t ^ 2 * E2 + 4 * E4 + 4 * Real.exp 1 * E2 ^ 2)
        ≤ √Y * (√Y * √(5 + 3 * Y)) :=
          mul_le_mul hmin hsq (Real.sqrt_nonneg _) hs0
      _ = Y * √(5 + 3 * Y) := by rw [← mul_assoc, hYY]
      _ ≤ Y * (3 + 5 * U) := mul_le_mul_of_nonneg_left hroot hY
  -- the exponential factor
  set E : ℝ := Real.exp (-U) with hEdef
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hEU : E * U ≤ 1 := perimR1_exp_neg_mul_le U
  have hEU2 : E * U ^ 2 ≤ 2 := perimR1_exp_neg_mul_sq_le hU
  have hE1 : E ≤ 1 := perimR1_exp_neg_le_one hU
  have hB0 : 0 ≤ B := by linarith
  have hkey : E * Θ * (3 + 5 * U) ≤ 134 * B := by
    have h1 : E * Θ * (3 + 5 * U) ≤ E * (10 * B * U + 2 / 5) * (3 + 5 * U) := by
      have : 0 ≤ 3 + 5 * U := by linarith
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hΘU hE0) this
    have h2 : E * (10 * B * U + 2 / 5) * (3 + 5 * U)
        = 30 * B * (E * U) + 50 * B * (E * U ^ 2) + 6 / 5 * E + 2 * (E * U) := by ring
    have h3 : B * (E * U) ≤ B * 1 := mul_le_mul_of_nonneg_left hEU hB0
    have h4 : B * (E * U ^ 2) ≤ B * 2 := mul_le_mul_of_nonneg_left hEU2 hB0
    nlinarith
  have he2 : Real.exp 1 ^ 2 ≤ 37 / 5 := perimR1_exp_one_sq_le
  have hfinal : Real.exp 1 ^ 2 * E * (Y * (3 + 5 * U)) ≤ 1000 * B * t := by
    have h1 : E * (Y * (3 + 5 * U)) = t * (E * Θ * (3 + 5 * U)) := by
      rw [hYdef]; ring
    have h2 : E * (Y * (3 + 5 * U)) ≤ t * (134 * B) := by
      rw [h1]; exact mul_le_mul_of_nonneg_left hkey ht.le
    have h3 : 0 ≤ E * (Y * (3 + 5 * U)) :=
      mul_nonneg hE0 (mul_nonneg hY (by linarith))
    calc Real.exp 1 ^ 2 * E * (Y * (3 + 5 * U))
        = Real.exp 1 ^ 2 * (E * (Y * (3 + 5 * U))) := by ring
      _ ≤ 37 / 5 * (t * (134 * B)) := by
          apply mul_le_mul he2 h2 h3 (by norm_num)
      _ ≤ 1000 * B * t := by nlinarith
  have hE'0 : 0 ≤ Real.exp 1 ^ 2 * E := mul_nonneg (sq_nonneg _) hE0
  calc Real.exp 1 ^ 2 * E * √(min 1 Q) *
        √(2 * Q + 2 * t ^ 2 * E2 + 4 * E4 + 4 * Real.exp 1 * E2 ^ 2)
      = Real.exp 1 ^ 2 * E * (√(min 1 Q) *
        √(2 * Q + 2 * t ^ 2 * E2 + 4 * E4 + 4 * Real.exp 1 * E2 ^ 2)) := by ring
    _ ≤ Real.exp 1 ^ 2 * E * (Y * (3 + 5 * U)) := mul_le_mul_of_nonneg_left hprod hE'0
    _ ≤ 1000 * B * t := hfinal

/-! ### One small coordinate -/

/-- For a coordinate `h ≤ H` and `t (1 + H) ≤ 1/2`: `φ(h₊) ≤ 10 (1 + H) u(h,t)`. -/
theorem perimR1_phi_le_small {H h t : ℝ} (hH : 0 ≤ H) (hhH : h ≤ H) (ht : 0 < t)
    (htH : t * (1 + H) ≤ 1 / 2) :
    gaussianPDFReal 0 1 (max h 0) ≤ 10 * (1 + H) * perimCU h t := by
  have hu := perimCU_ge_tail_add h ht
  have ht2 : t ≤ 1 / 2 := by nlinarith
  have hT0 : 0 ≤ perimCTail (h + t) := perimCTail_nonneg _
  by_cases hc : h + t ≤ 0
  · have hmax : max h 0 = 0 := max_eq_right (by linarith)
    rw [hmax]
    have h1 := perimCTail_ge_half hc
    have h2 := perimC_phi_zero_le_half
    nlinarith
  · rw [not_le] at hc
    have hkey : gaussianPDFReal 0 1 (max h 0) ≤ Real.exp 1 * gaussianPDFReal 0 1 (h + t) := by
      have hsq : (h + t) ^ 2 - (max h 0) ^ 2 ≤ 2 := by
        rcases le_or_gt 0 h with h0 | h0
        · rw [max_eq_left h0]
          have : h * t ≤ 1 / 2 := by nlinarith
          nlinarith
        · rw [max_eq_right h0.le]
          nlinarith
      have hexp : Real.exp (-(max h 0) ^ 2 / 2) ≤ Real.exp 1 * Real.exp (-(h + t) ^ 2 / 2) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        linarith
      rw [perimC_phi_eq, perimC_phi_eq]
      have hc0 : 0 ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by positivity
      calc (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(max h 0) ^ 2 / 2)
          ≤ (Real.sqrt (2 * Real.pi))⁻¹ * (Real.exp 1 * Real.exp (-(h + t) ^ 2 / 2)) :=
            mul_le_mul_of_nonneg_left hexp hc0
        _ = Real.exp 1 * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(h + t) ^ 2 / 2)) := by ring
    have hhaz := perimC_phi_le_mul_tail (h + t)
    have hmx : max (h + t) 0 = h + t := max_eq_left hc.le
    rw [hmx] at hhaz
    have he3 : Real.exp 1 ≤ 3 := perimR1_exp_one_le
    have hphi0 : 0 ≤ gaussianPDFReal 0 1 (h + t) := (perimC_phi_pos _).le
    have h1 : gaussianPDFReal 0 1 (max h 0) ≤ 3 * ((1 + (h + t)) * perimCTail (h + t)) := by
      calc gaussianPDFReal 0 1 (max h 0) ≤ Real.exp 1 * gaussianPDFReal 0 1 (h + t) := hkey
        _ ≤ 3 * gaussianPDFReal 0 1 (h + t) := mul_le_mul_of_nonneg_right he3 hphi0
        _ ≤ 3 * ((1 + (h + t)) * perimCTail (h + t)) := by linarith
    have h2 : (1 + (h + t)) * perimCTail (h + t) ≤ 2 * (1 + H) * perimCTail (h + t) :=
      mul_le_mul_of_nonneg_right (by linarith) hT0
    have h3 : 0 ≤ 1 + H := by linarith
    have h4 : (1 + H) * (632 / 1000 * perimCTail (h + t)) ≤ (1 + H) * perimCU h t :=
      mul_le_mul_of_nonneg_left hu h3
    nlinarith

/-! ### Summation over coordinates -/

lemma perimR1_Usum_eq {m : ℕ} (h : Fin m → ℝ) (t : ℝ) :
    perimUsum h t = ∑ j, perimCU (h j) t := rfl

lemma perimR1_Qsum_eq {m : ℕ} (h : Fin m → ℝ) (t : ℝ) :
    perimQsum h t = ∑ j, perimCQ (h j) t := rfl

lemma perimR1_E2sum_eq {m : ℕ} (h : Fin m → ℝ) (t : ℝ) :
    perimE2sum h t = ∑ j, perimCE2 (h j) t := rfl

lemma perimR1_E4sum_eq {m : ℕ} (h : Fin m → ℝ) (t : ℝ) :
    perimE4sum h t = ∑ j, perimCE4 (h j) t := rfl

/-- `Θ ≤ 10 (1 + H) U + 2/5` for `H = √(2 log m)`, `t (1 + H) ≤ 1/2`. -/
theorem perimR1_theta_le {m : ℕ} (hm : 2 ≤ m) (h : Fin m → ℝ) {t : ℝ} (ht : 0 < t)
    (htH : t * (1 + perimCBigLevel m) ≤ 1 / 2) :
    ∑ j, gaussianPDFReal 0 1 (max (h j) 0)
      ≤ 10 * (1 + perimCBigLevel m) * perimUsum h t + 2 / 5 := by
  have hH : 0 ≤ perimCBigLevel m := perimCBigLevel_nonneg m
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => perimCBigLevel m ≤ h j)]
  have hbig : ∑ j ∈ univ.filter (fun j => perimCBigLevel m ≤ h j),
      gaussianPDFReal 0 1 (max (h j) 0) ≤ 2 / 5 := by
    calc ∑ j ∈ univ.filter (fun j => perimCBigLevel m ≤ h j), gaussianPDFReal 0 1 (max (h j) 0)
        = ∑ j ∈ univ.filter (fun j => perimCBigLevel m ≤ h j), gaussianPDFReal 0 1 (h j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mem_filter] at hj
          rw [max_eq_left (hH.trans hj.2)]
      _ ≤ 2 / 5 := perimC_sum_big_phi_le_two_fifths (Fintype.card_fin m) hm h
  have hsmall : ∑ j ∈ univ.filter (fun j => ¬ perimCBigLevel m ≤ h j),
      gaussianPDFReal 0 1 (max (h j) 0) ≤ 10 * (1 + perimCBigLevel m) * perimUsum h t := by
    calc ∑ j ∈ univ.filter (fun j => ¬ perimCBigLevel m ≤ h j), gaussianPDFReal 0 1 (max (h j) 0)
        ≤ ∑ j ∈ univ.filter (fun j => ¬ perimCBigLevel m ≤ h j),
            10 * (1 + perimCBigLevel m) * perimCU (h j) t := by
          apply Finset.sum_le_sum
          intro j hj
          rw [Finset.mem_filter] at hj
          exact perimR1_phi_le_small hH (not_le.mp hj.2).le ht htH
      _ ≤ ∑ j, 10 * (1 + perimCBigLevel m) * perimCU (h j) t := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro j _ _
          exact mul_nonneg (by linarith) (perimCU_nonneg _ _)
      _ = 10 * (1 + perimCBigLevel m) * perimUsum h t := by
          rw [← Finset.mul_sum, perimR1_Usum_eq]
  linarith

/-! ### The right-hand side of the tilt chain and the Regime I bound -/

/-- The right-hand side of `perim_tilt_chain`:
`e² e^{-U} √(min 1 Q) √(2Q + 2t²E2 + 4E4 + 4e E2²)`. -/
noncomputable def perimR1Rhs {m : ℕ} (h : Fin m → ℝ) (t : ℝ) : ℝ :=
  Real.exp 1 ^ 2 * Real.exp (-perimUsum h t) * √(min 1 (perimQsum h t)) *
    √(2 * perimQsum h t + 2 * t ^ 2 * perimE2sum h t + 4 * perimE4sum h t
      + 4 * Real.exp 1 * perimE2sum h t ^ 2)

/-- The threshold `t₀ = 1 / (2 (1 + H))` of Regime I, with `H = √(2 log m)`. -/
noncomputable def perimR1T0 (m : ℕ) : ℝ := 1 / (2 * (1 + √(2 * Real.log m)))

lemma perimR1T0_pos (m : ℕ) : 0 < perimR1T0 m := by
  unfold perimR1T0
  have : 0 ≤ √(2 * Real.log (m : ℝ)) := Real.sqrt_nonneg _
  positivity

/-- **Regime I.**  For `m ≥ 2`, `h : Fin m → ℝ` and `0 < t ≤ 1 / (2 (1 + H))`, `H = √(2 log m)`:
`Rhs h t ≤ 1000 (1 + H) t`. -/
theorem perimR1_rhs_le {m : ℕ} (hm : 2 ≤ m) (h : Fin m → ℝ) {t : ℝ} (ht : 0 < t)
    (ht0 : t ≤ perimR1T0 m) :
    perimR1Rhs h t ≤ 1000 * (1 + √(2 * Real.log m)) * t := by
  have hHdef : perimCBigLevel m = √(2 * Real.log m) := rfl
  have hH1 : 1 ≤ perimCBigLevel m := perimCBigLevel_ge_one hm
  have hH0 : 0 ≤ perimCBigLevel m := perimCBigLevel_nonneg m
  have hB0 : 0 < 1 + perimCBigLevel m := by linarith
  have htB : t * (1 + perimCBigLevel m) ≤ 1 / 2 := by
    have h1 : t ≤ 1 / (2 * (1 + perimCBigLevel m)) := ht0
    have h2 := (le_div_iff₀ (by positivity : 0 < 2 * (1 + perimCBigLevel m))).mp h1
    linarith
  set Θ : ℝ := ∑ j, gaussianPDFReal 0 1 (max (h j) 0) with hΘdef
  have hΘ0 : 0 ≤ Θ := Finset.sum_nonneg fun j _ => (perimC_phi_pos _).le
  have hΘU := perimR1_theta_le hm h ht htB
  have hQ : perimQsum h t ≤ 887 / 1000 * (t * Θ) := by
    rw [perimR1_Qsum_eq, hΘdef, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => perimCQ_le_density (h j) ht
  have hE2 : perimE2sum h t ≤ 4432 / 10000 * (t * Θ) := by
    rw [perimR1_E2sum_eq, hΘdef, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => perimCE2_le_density (h j) ht
  have hE4 : perimE4sum h t ≤ 665 / 1000 * (t * Θ) := by
    rw [perimR1_E4sum_eq, hΘdef, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => perimCE4_le_density (h j) ht
  have hU0 : 0 ≤ perimUsum h t := Finset.sum_nonneg fun j _ => perimU_nonneg t (h j)
  have hQ0 : 0 ≤ perimQsum h t := Finset.sum_nonneg fun j _ => perimQ_nonneg t (h j)
  have hE20 : 0 ≤ perimE2sum h t := Finset.sum_nonneg fun j _ => perimE2_nonneg t (h j)
  rw [← hHdef]
  exact perimR1_arith hU0 hΘ0 ht (by linarith) htB hQ0 hE20 hQ hE2 hE4 hΘU

/-- **Corollary (the form with `(1 + H)²`).** -/
theorem perimR1_rhs_le_sq {m : ℕ} (hm : 2 ≤ m) (h : Fin m → ℝ) {t : ℝ} (ht : 0 < t)
    (ht0 : t ≤ perimR1T0 m) :
    perimR1Rhs h t ≤ 1000 * (1 + √(2 * Real.log m)) ^ 2 * t := by
  refine (perimR1_rhs_le hm h ht ht0).trans ?_
  have hH1 : 1 ≤ perimCBigLevel m := perimCBigLevel_ge_one hm
  have hHdef : perimCBigLevel m = √(2 * Real.log m) := rfl
  rw [← hHdef]
  have : 1 + perimCBigLevel m ≤ (1 + perimCBigLevel m) ^ 2 := by nlinarith
  nlinarith

/-- `perimR1Rhs` is exactly the right-hand side of `perim_tilt_chain`; hence under the
second-moment hypothesis `hG3` of the chain, `Psi t ≤ 1000 (1 + H) t` in Regime I. -/
theorem perimR1_psi_le {m : ℕ} (hm : 2 ≤ m) (h : Fin m → ℝ) {t : ℝ} (ht : 0 < t)
    (ht0 : t ≤ perimR1T0 m)
    (hG3 : ∫ x, perimTV h x ^ 2 * perimTilt h t x ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
      ≤ 2 * ∫ x, perimTK h x * perimTilt h t x ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
        + 2 * ∫ x, perimTN2 h x * perimTilt h t x ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
        + 4 * ∫ x, (perimTN2 h x / t ^ 2) ^ 2 * perimTilt h t x
            ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)) :
    perimPsi h t ≤ 1000 * (1 + √(2 * Real.log m)) * t :=
  (perim_tilt_chain h ht hG3).trans (perimR1_rhs_le hm h ht ht0)

end LatticeProb
