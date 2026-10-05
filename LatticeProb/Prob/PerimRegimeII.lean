import Mathlib
import LatticeProb.Prob.PerimCoord
import LatticeProb.Prob.PerimTilt

/-!
# Regime II (large `t`) of the two-regime arithmetic for the orthant perimeter bound (packet Q8b)

Let `H = √(2 log m)` (`m ≥ 2`), `D = 1 + H` and `t₀ = 1 / (2 D)`.  For `t ≥ t₀` we bound the
right-hand side of the tilt chain
`Rhs h t = e ^ 2 * exp (-U) * √(min 1 Q) * √(2 Q + 2 t ^ 2 E2 + 4 E4 + 4 e E2 ^ 2)`
by `32 * (1 + H) * t`, using only the `U`-type per-coordinate bounds `E2 ≤ U`, `E4 ≤ 0.648 U`,
`Q ≤ κ U + 1/2` with `κ = 2 (1 + 4 (1 + H) ^ 2 t ^ 2)` (small coordinates use the activity bound
`Φ̄ (h_j) ≤ κ u_j`, big coordinates `h_j ≥ H` contribute `∑ Φ̄ (h_j) ≤ 1/2`).
-/

namespace LatticeProb

open Finset

/-! ### The abstract real inequality -/

/-- **Regime II, pure arithmetic.**  If `D ≥ 2`, `2 D t ≥ 1`, `0 ≤ E2 ≤ U`, `0 ≤ E4 ≤ 0.648 U`,
`0 ≤ Q ≤ (2 + 8 D² t²) U + 1/2`, then the tilt-chain right-hand side is `≤ 32 D t`. -/
theorem perimR2_core {U Q E2 E4 t D : ℝ} (hD : 2 ≤ D) (ht : 0 < t) (htD : 1 ≤ 2 * D * t)
    (hU : 0 ≤ U) (hQ : 0 ≤ Q) (hE2 : 0 ≤ E2) (hE4 : 0 ≤ E4)
    (h2 : E2 ≤ U) (h4 : E4 ≤ 648 / 1000 * U)
    (hQU : Q ≤ (2 + 8 * D ^ 2 * t ^ 2) * U + 1 / 2) :
    Real.exp 1 ^ 2 * Real.exp (-U) * √(min 1 Q) *
      √(2 * Q + 2 * t ^ 2 * E2 + 4 * E4 + 4 * Real.exp 1 * E2 ^ 2) ≤ 32 * D * t := by
  set e : ℝ := Real.exp 1 with he
  set E : ℝ := Real.exp (-U) with hEdef
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = D ^ 2 * t ^ 2 := ⟨_, rfl⟩
  set Rad : ℝ := 2 * Q + 2 * t ^ 2 * E2 + 4 * E4 + 4 * e * E2 ^ 2 with hRad
  have he_pos : 0 < e := Real.exp_pos 1
  have he_lt : e < 272 / 100 := by
    have := Real.exp_one_lt_d9
    rw [he]; norm_num at this ⊢; linarith
  have he_gt : 2 < e := by
    have := Real.exp_one_gt_d9
    rw [he]; norm_num at this ⊢; linarith
  have hE_pos : 0 < E := Real.exp_pos _
  have hE_le : E ≤ 1 := by
    rw [hEdef]; exact Real.exp_le_one_iff.mpr (by linarith)
  -- `P ≥ 1/4` and `P ≥ 4 t²`
  have hP4 : 1 ≤ 4 * P := by
    rw [hP]
    have : (1 : ℝ) ≤ (2 * D * t) ^ 2 := by nlinarith
    nlinarith
  have hPt : 4 * t ^ 2 ≤ P := by
    have hD2 : (4 : ℝ) ≤ D ^ 2 := by nlinarith
    rw [hP]; exact mul_le_mul_of_nonneg_right hD2 (sq_nonneg t)
  have hQU' : Q ≤ (2 + 8 * P) * U + 1 / 2 := by
    rw [hP]; linarith [hQU]
  have hE2sq : E2 ^ 2 ≤ U ^ 2 := pow_le_pow_left₀ hE2 h2 2
  -- the radicand is nonnegative
  have hRad0 : 0 ≤ Rad := by
    rw [hRad]; positivity
  -- step 1: radicand bound
  have hRadB : Rad ≤ P * (43 * U + 16 * e * U ^ 2 + 4) := by
    have k1 : 0 ≤ (4 * P - 1) * U := mul_nonneg (by linarith) hU
    have k2 : 0 ≤ (P - 4 * t ^ 2) * U := mul_nonneg (by linarith) hU
    have k3 : 0 ≤ (4 * P - 1) * (e * U ^ 2) := mul_nonneg (by linarith) (by positivity)
    have k4 : 4 * e * E2 ^ 2 ≤ 4 * e * U ^ 2 := by
      have := mul_le_mul_of_nonneg_left hE2sq (by positivity : (0 : ℝ) ≤ 4 * e)
      exact this
    have k5 : 2 * t ^ 2 * E2 ≤ 2 * t ^ 2 * U :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have k6 : 2 * ((2 + 8 * P) * U + 1 / 2) = 4 * U + 16 * (P * U) + 1 := by ring
    rw [hRad]
    nlinarith [k1, k2, k3, k4, k5, hQU', h4, k6]
  -- step 2: the exponential inequalities
  have hA : e * U * E ^ 2 ≤ 1 / 2 := by
    have h1 := Real.add_one_le_exp (2 * U - 1)
    have h2' : E ^ 2 = Real.exp (-(2 * U)) := by
      rw [hEdef, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    have h3 : Real.exp (2 * U - 1) * Real.exp (-(2 * U)) * e = 1 := by
      rw [he, ← Real.exp_add, ← Real.exp_add,
        show 2 * U - 1 + -(2 * U) + 1 = 0 by ring, Real.exp_zero]
    have h4' : 0 ≤ Real.exp (-(2 * U)) * e := by positivity
    have h5 := mul_le_mul_of_nonneg_right h1 h4'
    rw [h2']
    nlinarith [h5, h3]
  have hB : e * U * E ≤ 1 := by
    have h1 := Real.add_one_le_exp (U - 1)
    have h3 : Real.exp (U - 1) * E * e = 1 := by
      rw [hEdef, he, ← Real.exp_add, ← Real.exp_add,
        show U - 1 + -U + 1 = 0 by ring, Real.exp_zero]
    have h4' : 0 ≤ E * e := by positivity
    have h5 := mul_le_mul_of_nonneg_right h1 h4'
    nlinarith [h5, h3]
  have hB2 : (e * U * E) ^ 2 ≤ 1 := by
    have h0 : 0 ≤ e * U * E := by positivity
    nlinarith
  -- step 3: assemble
  have hmain : e ^ 4 * E ^ 2 * Rad ≤ (32 * D * t) ^ 2 := by
    have hX : e ^ 4 * E ^ 2 * Rad ≤ e ^ 4 * E ^ 2 * (P * (43 * U + 16 * e * U ^ 2 + 4)) :=
      mul_le_mul_of_nonneg_left hRadB (by positivity)
    have hY : e ^ 4 * E ^ 2 * (P * (43 * U + 16 * e * U ^ 2 + 4))
        = P * (43 * e ^ 3 * (e * U * E ^ 2) + 16 * e ^ 3 * (e * U * E) ^ 2
          + 4 * e ^ 4 * E ^ 2) := by ring
    have hZ : 43 * e ^ 3 * (e * U * E ^ 2) + 16 * e ^ 3 * (e * U * E) ^ 2
          + 4 * e ^ 4 * E ^ 2 ≤ 43 * e ^ 3 * (1 / 2) + 16 * e ^ 3 * 1 + 4 * e ^ 4 * 1 := by
      have a1 : 43 * e ^ 3 * (e * U * E ^ 2) ≤ 43 * e ^ 3 * (1 / 2) :=
        mul_le_mul_of_nonneg_left hA (by positivity)
      have a2 : 16 * e ^ 3 * (e * U * E) ^ 2 ≤ 16 * e ^ 3 * 1 :=
        mul_le_mul_of_nonneg_left hB2 (by positivity)
      have a3 : 4 * e ^ 4 * E ^ 2 ≤ 4 * e ^ 4 * 1 := by
        exact mul_le_mul_of_nonneg_left (pow_le_one₀ hE_pos.le hE_le) (by positivity)
      linarith
    have he3 : e ^ 3 ≤ (272 / 100 : ℝ) ^ 3 := pow_le_pow_left₀ he_pos.le he_lt.le 3
    have he4 : e ^ 4 ≤ (272 / 100 : ℝ) ^ 4 := pow_le_pow_left₀ he_pos.le he_lt.le 4
    have hnum : 43 * e ^ 3 * (1 / 2) + 16 * e ^ 3 * 1 + 4 * e ^ 4 * 1 ≤ 1024 := by
      norm_num at he3 he4
      linarith
    have hP0 : 0 ≤ P := by rw [hP]; positivity
    calc e ^ 4 * E ^ 2 * Rad ≤ P * (43 * e ^ 3 * (e * U * E ^ 2)
            + 16 * e ^ 3 * (e * U * E) ^ 2 + 4 * e ^ 4 * E ^ 2) := hX.trans hY.le
      _ ≤ P * 1024 := mul_le_mul_of_nonneg_left (hZ.trans hnum) hP0
      _ = (32 * D * t) ^ 2 := by rw [hP]; ring
  -- step 4: drop `min 1 Q` and take square roots
  have hmin : √(min 1 Q) ≤ 1 := Real.sqrt_le_one.mpr (min_le_left _ _)
  have hsRad : 0 ≤ √Rad := Real.sqrt_nonneg _
  have hstep1 : e ^ 2 * E * √(min 1 Q) * √Rad ≤ e ^ 2 * E * √Rad := by
    have h0 : 0 ≤ e ^ 2 * E := by positivity
    calc e ^ 2 * E * √(min 1 Q) * √Rad = (e ^ 2 * E * √Rad) * √(min 1 Q) := by ring
      _ ≤ (e ^ 2 * E * √Rad) * 1 :=
          mul_le_mul_of_nonneg_left hmin (mul_nonneg h0 hsRad)
      _ = e ^ 2 * E * √Rad := by ring
  have hstep2 : e ^ 2 * E * √Rad ≤ 32 * D * t := by
    have h0 : 0 ≤ e ^ 2 * E * √Rad := by positivity
    have h1 : 0 ≤ 32 * D * t := by positivity
    refine (sq_le_sq₀ h0 h1).mp ?_
    have : (e ^ 2 * E * √Rad) ^ 2 = e ^ 4 * E ^ 2 * Rad := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hRad0]; ring
    rw [this]; exact hmain
  exact hstep1.trans hstep2

/-! ### The right-hand side of the tilt chain and the per-coordinate sums -/

/-- The right-hand side of `perim_tilt_chain`. -/
noncomputable def perimR2Rhs {m : ℕ} (h : Fin m → ℝ) (t : ℝ) : ℝ :=
  Real.exp 1 ^ 2 * Real.exp (-perimUsum h t) * √(min 1 (perimQsum h t)) *
    √(2 * perimQsum h t + 2 * t ^ 2 * perimE2sum h t + 4 * perimE4sum h t
      + 4 * Real.exp 1 * perimE2sum h t ^ 2)

/-- The regime boundary `t₀ = 1 / (2 (1 + H))`, `H = √(2 log m)`. -/
noncomputable def perimR2T0 (m : ℕ) : ℝ := 1 / (2 * (1 + √(2 * Real.log m)))

/-- `E2 ≤ U` (P1, summed). -/
theorem perimR2_E2sum_le {m : ℕ} (h : Fin m → ℝ) (t : ℝ) :
    perimE2sum h t ≤ perimUsum h t :=
  Finset.sum_le_sum fun j _ => perimCE2_le_perimCU (h j) t

/-- `E4 ≤ 0.648 U` (P2, summed). -/
theorem perimR2_E4sum_le {m : ℕ} (h : Fin m → ℝ) (t : ℝ) :
    perimE4sum h t ≤ 648 / 1000 * perimUsum h t := by
  have : perimE4sum h t ≤ ∑ j, 648 / 1000 * perimU t (h j) :=
    Finset.sum_le_sum fun j _ => perimCE4_le_perimCU (h j) t
  rw [← Finset.mul_sum] at this
  exact this

/-- One coordinate: `q_j ≤ κ u_j + (Φ̄ (h_j) if h_j ≥ H, else 0)`, `κ = 2 (1 + 4 (1+H)² t²)`. -/
theorem perimR2_q_le {H : ℝ} (hH : 0 ≤ H) (c : ℝ) {t : ℝ} (ht : 0 < t) :
    perimQ t c ≤ (2 + 8 * (1 + H) ^ 2 * t ^ 2) * perimU t c +
      (if H ≤ c then perimCTail c else 0) := by
  have hq : perimQ t c ≤ perimCTail c := perimCQ_le_perimCTail c t
  have hu : 0 ≤ perimU t c := perimCU_nonneg c t
  have hκ : 0 ≤ 2 + 8 * (1 + H) ^ 2 * t ^ 2 := by positivity
  by_cases hc : H ≤ c
  · rw [if_pos hc]
    have := mul_nonneg hκ hu
    linarith
  · rw [if_neg hc]
    have hcH : c ≤ H := (not_le.mp hc).le
    have hmax : max c 0 ≤ H := max_le hcH hH
    have h1 : perimCTail c ≤ 2 * (1 + 4 * (1 + max c 0) ^ 2 * t ^ 2) * perimU t c :=
      perimCTail_le_mul_perimCU c ht
    have h2 : (1 + max c 0) ^ 2 ≤ (1 + H) ^ 2 :=
      pow_le_pow_left₀ (by have := le_max_right c 0; linarith) (by linarith) 2
    have h3 : 2 * (1 + 4 * (1 + max c 0) ^ 2 * t ^ 2) ≤ 2 + 8 * (1 + H) ^ 2 * t ^ 2 := by
      have := mul_le_mul_of_nonneg_right h2 (sq_nonneg t)
      nlinarith
    have h4 := mul_le_mul_of_nonneg_right h3 hu
    linarith

/-- `Q ≤ κ U + 1/2` with `κ = 2 + 8 (1+H)² t²`, `H = √(2 log m)`: small coordinates by the
activity bound, big coordinates by the total tail bound. -/
theorem perimR2_Qsum_le {m : ℕ} (hm : 2 ≤ m) (h : Fin m → ℝ) {t : ℝ} (ht : 0 < t) :
    perimQsum h t ≤
      (2 + 8 * (1 + √(2 * Real.log m)) ^ 2 * t ^ 2) * perimUsum h t + 1 / 2 := by
  have hH : 0 ≤ √(2 * Real.log m) := Real.sqrt_nonneg _
  have hbig : ∑ j ∈ Finset.univ.filter (fun j => perimCBigLevel m ≤ h j), perimCTail (h j)
      ≤ 1 / 2 := perimC_sum_big_tail_le (by simp) hm h
  have hsum : perimQsum h t ≤ ∑ j, ((2 + 8 * (1 + √(2 * Real.log m)) ^ 2 * t ^ 2) *
        perimU t (h j) + (if √(2 * Real.log m) ≤ h j then perimCTail (h j) else 0)) :=
    Finset.sum_le_sum fun j _ => perimR2_q_le hH (h j) ht
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_filter] at hsum
  have : perimUsum h t = ∑ j, perimU t (h j) := rfl
  rw [this]
  exact hsum.trans (by
    have hb : ∑ j ∈ Finset.univ.filter (fun j => √(2 * Real.log m) ≤ h j), perimCTail (h j)
        ≤ 1 / 2 := hbig
    linarith)

/-! ### Regime II -/

/-- **Regime II.**  For `m ≥ 2`, every `h` and every `t ≥ t₀ = 1 / (2 (1 + H))`, `H = √(2 log m)`:
`Rhs h t ≤ 32 * (1 + H) * t`. -/
theorem perimR2_rhs_le {m : ℕ} (hm : 2 ≤ m) (h : Fin m → ℝ) {t : ℝ}
    (ht : 1 / (2 * (1 + √(2 * Real.log m))) ≤ t) :
    perimR2Rhs h t ≤ 32 * (1 + √(2 * Real.log m)) * t := by
  have hH1 : 1 ≤ √(2 * Real.log m) := perimCBigLevel_ge_one hm
  have hD : 2 ≤ 1 + √(2 * Real.log m) := by linarith
  have hDpos : 0 < 2 * (1 + √(2 * Real.log m)) := by linarith
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
  have htD : 1 ≤ 2 * (1 + √(2 * Real.log m)) * t := by
    rw [div_le_iff₀ hDpos] at ht
    linarith
  have hQ : 0 ≤ perimQsum h t := Finset.sum_nonneg fun j _ => perimQ_nonneg t (h j)
  have hE2 : 0 ≤ perimE2sum h t := Finset.sum_nonneg fun j _ => perimE2_nonneg t (h j)
  have hE4 : 0 ≤ perimE4sum h t := Finset.sum_nonneg fun j _ => perimE4_nonneg t (h j)
  have hU : 0 ≤ perimUsum h t := Finset.sum_nonneg fun j _ => perimU_nonneg t (h j)
  exact perimR2_core hD ht0 htD hU hQ hE2 hE4 (perimR2_E2sum_le h t) (perimR2_E4sum_le h t)
    (perimR2_Qsum_le hm h ht0)

/-- The same bound with the weaker polylog slack `(1 + H) ^ 2`. -/
theorem perimR2_rhs_le_sq {m : ℕ} (hm : 2 ≤ m) (h : Fin m → ℝ) {t : ℝ}
    (ht : 1 / (2 * (1 + √(2 * Real.log m))) ≤ t) :
    perimR2Rhs h t ≤ 32 * (1 + √(2 * Real.log m)) ^ 2 * t := by
  have hH1 : 1 ≤ √(2 * Real.log m) := perimCBigLevel_ge_one hm
  have hDpos : 0 < 2 * (1 + √(2 * Real.log m)) := by linarith
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
  refine (perimR2_rhs_le hm h ht).trans ?_
  have h1 : 1 + √(2 * Real.log m) ≤ (1 + √(2 * Real.log m)) ^ 2 := by nlinarith
  have := mul_le_mul_of_nonneg_right h1 ht0.le
  nlinarith

/-- **Regime II for the perimeter functional.**  Combined with `perim_tilt_chain`: under the
Stein second-moment hypothesis (G3), `Psi t ≤ 32 (1 + H) t` for all `t ≥ t₀`. -/
theorem perimR2_psi_le {m : ℕ} (hm : 2 ≤ m) (h : Fin m → ℝ) {t : ℝ}
    (ht : 1 / (2 * (1 + √(2 * Real.log m))) ≤ t)
    (hG3 : ∫ x, perimTV h x ^ 2 * perimTilt h t x ∂(MeasureTheory.Measure.pi fun _ : Fin m =>
          ProbabilityTheory.gaussianReal 0 1)
      ≤ 2 * ∫ x, perimTK h x * perimTilt h t x ∂(MeasureTheory.Measure.pi fun _ : Fin m =>
          ProbabilityTheory.gaussianReal 0 1)
        + 2 * ∫ x, perimTN2 h x * perimTilt h t x ∂(MeasureTheory.Measure.pi fun _ : Fin m =>
          ProbabilityTheory.gaussianReal 0 1)
        + 4 * ∫ x, (perimTN2 h x / t ^ 2) ^ 2 * perimTilt h t x
            ∂(MeasureTheory.Measure.pi fun _ : Fin m => ProbabilityTheory.gaussianReal 0 1)) :
    perimPsi h t ≤ 32 * (1 + √(2 * Real.log m)) * t := by
  have hH1 : 1 ≤ √(2 * Real.log m) := perimCBigLevel_ge_one hm
  have hDpos : 0 < 2 * (1 + √(2 * Real.log m)) := by linarith
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
  exact (perim_tilt_chain h ht0 hG3).trans (perimR2_rhs_le hm h ht)

end LatticeProb
