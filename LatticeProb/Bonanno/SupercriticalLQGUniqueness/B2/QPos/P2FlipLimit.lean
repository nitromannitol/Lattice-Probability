/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P2FlipLimit at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P2FlipBox

 







set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.QPos

open WiredConductances

theorem sqrt_pow_twenty_div_four (N : ℝ) (hN : 0 ≤ N) :
    Real.sqrt (N ^ 20 / 4) = N ^ 10 / 2 := by
  rw [show N ^ 20 / 4 = (N ^ 10 / 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]

theorem sqrt_sq_div_pow_twenty (j N : ℝ) (hj : 0 ≤ j) (hN : 0 < N) :
    Real.sqrt (j ^ 2 / N ^ 20) = j / N ^ 10 := by
  rw [show j ^ 2 / N ^ 20 = (j / N ^ 10) ^ 2 by field_simp, Real.sqrt_sq (by positivity)]

theorem inv_pow_le_inv {N : ℝ} (hN : 1 ≤ N) (k : ℕ) (hk : 1 ≤ k) : 1 / N ^ k ≤ 1 / N := by
  apply one_div_le_one_div_of_le (by linarith)
  calc N = N ^ 1 := (pow_one N).symm
    _ ≤ N ^ k := pow_le_pow_right₀ hN hk

 
theorem interior_part_le {t : ℝ} (ht : 0 ≤ t) {N : ℕ} (hN : 1 ≤ N) :
    (((N ^ 20 : ℕ) : ℝ) + 1) * tInt ((N ^ 20 : ℕ) : ℝ) t ≤ 256 * dgffConductance * t / N := by
  have hc := dgffConductance_pos
  have hN0 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  unfold tInt
  push_cast
  rw [sqrt_pow_twenty_div_four N hNp.le]
  have h1 : ((N : ℝ) ^ 20 + 1) ≤ 2 * (N : ℝ) ^ 20 := by
    have : (1 : ℝ) ≤ (N : ℝ) ^ 20 := one_le_pow₀ hN0
    linarith
  have hval : 4 * (N : ℝ) ^ 20 * dgffConductance * t / (((N : ℝ) ^ 20 / 4) ^ 2 * ((N : ℝ) ^ 10 / 2)) =
      128 * dgffConductance * t / ((N : ℝ) ^ 20 * (N : ℝ) ^ 10) := by
    field_simp; ring
  rw [hval]
  calc ((N : ℝ) ^ 20 + 1) * (128 * dgffConductance * t / ((N : ℝ) ^ 20 * (N : ℝ) ^ 10))
      ≤ 2 * (N : ℝ) ^ 20 * (128 * dgffConductance * t / ((N : ℝ) ^ 20 * (N : ℝ) ^ 10)) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = 256 * dgffConductance * t * (1 / (N : ℝ) ^ 10) := by field_simp; ring
    _ ≤ 256 * dgffConductance * t * (1 / N) :=
        mul_le_mul_of_nonneg_left (inv_pow_le_inv hN0 10 (by norm_num)) (by positivity)
    _ = 256 * dgffConductance * t / N := by ring

 
theorem near_part_le {t : ℝ} (ht : 0 < t) {N : ℕ} (hN : 1 ≤ N) :
    ∑ j ∈ Finset.Ico (1 : ℕ) (N ^ 18 + 1),
        Real.exp (-(4 * ((N ^ 20 : ℕ) : ℝ) * dgffConductance * t / (1 + 4 * (j : ℝ)))) ≤
      (Nat.factorial 10 : ℝ) * (5 / (4 * dgffConductance * t)) ^ 10 / N := by
  have hc := dgffConductance_pos
  have hN0 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  set x : ℝ := 4 * dgffConductance * t / 5 * (N : ℝ) ^ 2 with hx
  have hxpos : 0 < x := by positivity
  have hterm : ∀ j ∈ Finset.Ico (1 : ℕ) (N ^ 18 + 1),
      Real.exp (-(4 * ((N ^ 20 : ℕ) : ℝ) * dgffConductance * t / (1 + 4 * (j : ℝ)))) ≤ Real.exp (-x) := by
    intro j hj
    simp only [Finset.mem_Ico] at hj
    rw [Real.exp_le_exp, neg_le_neg_iff]
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj.1
    have hjJ : (j : ℝ) ≤ (N : ℝ) ^ 18 := by exact_mod_cast (show j ≤ N ^ 18 by omega)
    have hden : 1 + 4 * (j : ℝ) ≤ 5 * (N : ℝ) ^ 18 := by
      have : (1 : ℝ) ≤ (N : ℝ) ^ 18 := one_le_pow₀ hN0
      linarith
    push_cast
    rw [hx, le_div_iff₀ (by positivity)]
    calc 4 * dgffConductance * t / 5 * (N : ℝ) ^ 2 * (1 + 4 * (j : ℝ))
        ≤ 4 * dgffConductance * t / 5 * (N : ℝ) ^ 2 * (5 * (N : ℝ) ^ 18) :=
          mul_le_mul_of_nonneg_left hden (by positivity)
      _ = 4 * (N : ℝ) ^ 20 * dgffConductance * t := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Nat.card_Ico, Nat.add_sub_cancel, nsmul_eq_mul]
  have he := exp_neg_le_pow_ten hxpos
  push_cast
  calc (N : ℝ) ^ 18 * Real.exp (-x) ≤ (N : ℝ) ^ 18 * ((Nat.factorial 10 : ℝ) / x ^ 10) :=
        mul_le_mul_of_nonneg_left he (by positivity)
    _ = (Nat.factorial 10 : ℝ) * (5 / (4 * dgffConductance * t)) ^ 10 * (1 / (N : ℝ) ^ 2) := by
        rw [hx]; field_simp
    _ ≤ (Nat.factorial 10 : ℝ) * (5 / (4 * dgffConductance * t)) ^ 10 * (1 / N) :=
        mul_le_mul_of_nonneg_left (inv_pow_le_inv hN0 2 (by norm_num)) (by positivity)
    _ = _ := by ring

 
theorem far_part_le {t : ℝ} (ht : 0 ≤ t) {N : ℕ} (hN : 1 ≤ N) :
    ∑ j ∈ Finset.Ico (N ^ 18 + 1) (N ^ 20),
        4 * ((N ^ 20 : ℕ) : ℝ) * dgffConductance * t /
          (((j : ℝ) ^ 2 / ((N ^ 20 : ℕ) : ℝ)) ^ 2 * Real.sqrt ((j : ℝ) ^ 2 / ((N ^ 20 : ℕ) : ℝ))) ≤
      4 * dgffConductance * t / N := by
  have hc := dgffConductance_pos
  have hN0 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hterm : ∀ j ∈ Finset.Ico (N ^ 18 + 1) (N ^ 20),
      4 * ((N ^ 20 : ℕ) : ℝ) * dgffConductance * t /
          (((j : ℝ) ^ 2 / ((N ^ 20 : ℕ) : ℝ)) ^ 2 * Real.sqrt ((j : ℝ) ^ 2 / ((N ^ 20 : ℕ) : ℝ))) =
        4 * dgffConductance * t * (N : ℝ) ^ 70 * (1 / (j : ℝ) ^ 5) := by
    intro j hj
    simp only [Finset.mem_Ico] at hj
    have hjp : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
    push_cast
    rw [sqrt_sq_div_pow_twenty j N hjp.le hNp]
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have htail := sum_Ico_inv_pow_five_le (J := N ^ 18) (M := N ^ 20) (Nat.one_le_pow _ _ hN)
  push_cast at htail
  calc 4 * dgffConductance * t * (N : ℝ) ^ 70 * ∑ j ∈ Finset.Ico (N ^ 18 + 1) (N ^ 20),
        (1 : ℝ) / (j : ℝ) ^ 5
      ≤ 4 * dgffConductance * t * (N : ℝ) ^ 70 * (1 / ((N : ℝ) ^ 18) ^ 4) :=
        mul_le_mul_of_nonneg_left htail (by positivity)
    _ = 4 * dgffConductance * t * (1 / (N : ℝ) ^ 2) := by field_simp
    _ ≤ 4 * dgffConductance * t * (1 / N) :=
        mul_le_mul_of_nonneg_left (inv_pow_le_inv hN0 2 (by norm_num)) (by positivity)
    _ = _ := by ring

 
theorem bpart_le {u : ℝ} (hu : 0 < u) {N : ℕ} (hN : 1 ≤ N) :
    Real.exp (-2 * (((N ^ 20 : ℕ) : ℝ) * dgffConductance) * u ^ 2) ≤
      1 / (2 * dgffConductance * u ^ 2) / N := by
  have hc := dgffConductance_pos
  have hN0 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hx : 0 < 2 * (((N ^ 20 : ℕ) : ℝ) * dgffConductance) * u ^ 2 := by positivity
  have h1 : Real.exp (-2 * (((N ^ 20 : ℕ) : ℝ) * dgffConductance) * u ^ 2) ≤
      1 / (2 * (((N ^ 20 : ℕ) : ℝ) * dgffConductance) * u ^ 2) := by
    rw [show -2 * (((N ^ 20 : ℕ) : ℝ) * dgffConductance) * u ^ 2 =
      -(2 * (((N ^ 20 : ℕ) : ℝ) * dgffConductance) * u ^ 2) by ring, Real.exp_neg,
      ← one_div]
    apply one_div_le_one_div_of_le hx
    linarith [Real.add_one_le_exp (2 * (((N ^ 20 : ℕ) : ℝ) * dgffConductance) * u ^ 2)]
  refine h1.trans ?_
  push_cast
  rw [div_div]
  apply one_div_le_one_div_of_le (by positivity)
  have : (N : ℝ) ≤ (N : ℝ) ^ 20 := by
    calc (N : ℝ) = N ^ 1 := (pow_one _).symm
      _ ≤ N ^ 20 := pow_le_pow_right₀ hN0 (by norm_num)
  nlinarith [sq_nonneg u, mul_pos hc (sq_pos_of_pos hu)]

 
theorem etaBox_small (n : ℕ) {u : ℝ} (hu : 0 < u) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℕ, ∃ hM : 2 ≤ M, etaBox n M hM u ≤ ε := by
  have hc := dgffConductance_pos
  set t := u ^ 2 / 2 with htdef
  have ht : 0 < t := by positivity
  set H : ℝ := (Fintype.card (BoxHE n) : ℝ)
  have hH : 0 ≤ H := Nat.cast_nonneg _
  set K : ℝ := 2 * H * (256 * dgffConductance * t +
    (Nat.factorial 10 : ℝ) * (5 / (4 * dgffConductance * t)) ^ 10 + 4 * dgffConductance * t +
      1 / (2 * dgffConductance * u ^ 2))
  have hK : 0 ≤ K := by positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (K / ε + 2)
  have hN2 : 2 ≤ N := by
    have : (2 : ℝ) < N := by have := div_nonneg hK hε.le; linarith
    exact_mod_cast this.le
  have hN1 : 1 ≤ N := by omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hM : 2 ≤ N ^ 20 := le_trans hN2 (by
    calc N = N ^ 1 := (pow_one N).symm
      _ ≤ N ^ 20 := Nat.pow_le_pow_right (by omega) (by norm_num))
  refine ⟨N ^ 20, hM, ?_⟩
  refine (etaBox_le (N ^ 20) hM hu (N ^ 18)).trans ?_
  have hsplit : ∑ j ∈ Finset.Ico 1 (N ^ 20), tBdry ((N ^ 20 : ℕ) : ℝ) t (N ^ 18) j =
      ∑ j ∈ Finset.Ico (1 : ℕ) (N ^ 18 + 1),
        Real.exp (-(4 * ((N ^ 20 : ℕ) : ℝ) * dgffConductance * t / (1 + 4 * (j : ℝ)))) +
      ∑ j ∈ Finset.Ico (N ^ 18 + 1) (N ^ 20),
        4 * ((N ^ 20 : ℕ) : ℝ) * dgffConductance * t /
          (((j : ℝ) ^ 2 / ((N ^ 20 : ℕ) : ℝ)) ^ 2 *
            Real.sqrt ((j : ℝ) ^ 2 / ((N ^ 20 : ℕ) : ℝ))) := by
    have h18 : N ^ 18 + 1 ≤ N ^ 20 := by
      have : N ^ 18 < N ^ 20 := Nat.pow_lt_pow_right (by omega) (by norm_num)
      omega
    rw [← Finset.sum_Ico_consecutive _ (show 1 ≤ N ^ 18 + 1 by omega) h18]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.mem_Ico] at hj
      unfold tBdry
      rw [if_pos (by omega)]
    · apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.mem_Ico] at hj
      unfold tBdry
      rw [if_neg (by omega)]
  rw [hsplit]
  have h1 := interior_part_le ht.le hN1 (t := t)
  have h2 := near_part_le ht hN1
  have h3 := far_part_le ht.le hN1
  have h4 := bpart_le hu hN1
  have hbound : 2 * H * ((((N ^ 20 : ℕ) : ℝ) + 1) * tInt ((N ^ 20 : ℕ) : ℝ) t +
      (∑ j ∈ Finset.Ico (1 : ℕ) (N ^ 18 + 1),
        Real.exp (-(4 * ((N ^ 20 : ℕ) : ℝ) * dgffConductance * t / (1 + 4 * (j : ℝ)))) +
      ∑ j ∈ Finset.Ico (N ^ 18 + 1) (N ^ 20),
        4 * ((N ^ 20 : ℕ) : ℝ) * dgffConductance * t /
          (((j : ℝ) ^ 2 / ((N ^ 20 : ℕ) : ℝ)) ^ 2 *
            Real.sqrt ((j : ℝ) ^ 2 / ((N ^ 20 : ℕ) : ℝ)))) +
      Real.exp (-2 * (((N ^ 20 : ℕ) : ℝ) * dgffConductance) * u ^ 2)) ≤ K / N := by
    have hsum := add_le_add (add_le_add h1 (add_le_add h2 h3)) h4
    have : 2 * H * ((256 * dgffConductance * t / N +
        ((Nat.factorial 10 : ℝ) * (5 / (4 * dgffConductance * t)) ^ 10 / N +
          4 * dgffConductance * t / N)) + 1 / (2 * dgffConductance * u ^ 2) / N) = K / N := by
      simp only [K]; field_simp; ring
    rw [← this]
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  refine le_trans (le_of_eq ?_) (hbound.trans ?_)
  · push_cast; ring
  · rw [div_le_iff₀ hNp]
    have : K / ε < N := by linarith
    rw [div_lt_iff₀ hε] at this
    linarith

end SupercriticalLQGUniqueness.B2.QPos
