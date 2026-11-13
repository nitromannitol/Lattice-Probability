/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P4Gradient at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P4Coupling

 











set_option autoImplicit false
noncomputable section

open Finset

namespace SupercriticalLQGUniqueness.B2.QPos.P4

open P3

theorem sqrt_div_ge_one {d m : ℝ} (hm : 0 < m) (hdm : m ≤ d) : 1 ≤ Real.sqrt (d / m) := by
  rw [Real.one_le_sqrt]
  rw [le_div_iff₀ hm]; linarith

 
theorem harmonic_diff_even (U : Finset (ℤ × ℤ)) {H : ℤ × ℤ → ℝ}
    (hH : ∀ a ∈ U, H a = avg H a) {M : ℝ} (hM : ∀ c, |H c| ≤ M)
    {x y : ℤ × ℤ} (hpar : (du (x, y)) % 2 = 0)
    (d : ℕ) (hd1 : |x.1 - y.1| ≤ d) (hd2 : |x.2 - y.2| ≤ d)
    (m : ℕ) (hm : 1 ≤ m)
    (hbx : ∀ c : ℤ × ℤ, |c.1 - x.1| < m → |c.2 - x.2| < m → c ∈ U)
    (hby : ∀ c : ℤ × ℤ, |c.1 - y.1| < m → |c.2 - y.2| < m → c ∈ U) :
    |H x - H y| ≤ 24 * M * Real.sqrt (d / m) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have htriv : |H x - H y| ≤ 2 * M := by
    have := abs_sub (H x) (H y); linarith [hM x, hM y]
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · subst hd0
    have hx : x = y := by
      have h1 := abs_le.mp hd1
      have h2 := abs_le.mp hd2
      push_cast at h1 h2
      apply Prod.ext <;> omega
    subst hx
    simp only [sub_self, abs_zero]
    positivity
  by_cases hdm : m ≤ d
  · have := sqrt_div_ge_one hmpos (by exact_mod_cast hdm : (m : ℝ) ≤ d)
    nlinarith
  push_neg at hdm
  
  obtain ⟨i, hi⟩ : ∃ i, du (x, y) = 2 * i := ⟨du (x, y) / 2, by omega⟩
  obtain ⟨j, hj⟩ : ∃ j, dv (x, y) = 2 * j := by
    refine ⟨dv (x, y) / 2, ?_⟩
    have : dv (x, y) % 2 = 0 := by
      simp only [du] at hpar; simp only [dv]; omega
    omega
  have hiabs : |(i : ℝ)| ≤ d := by
    have : |i| ≤ d := by
      simp only [du] at hi
      rw [abs_le] at hd1 hd2 ⊢
      constructor <;> omega
    exact_mod_cast this
  have hjabs : |(j : ℝ)| ≤ d := by
    have : |j| ≤ d := by
      simp only [dv] at hj
      rw [abs_le] at hd1 hd2 ⊢
      constructor <;> omega
    exact_mod_cast this
  
  set A : ℕ := Nat.sqrt (d * m) + 1 with hAdef
  have hA1 : 1 ≤ A := by omega
  have hdm1 : (1 : ℝ) ≤ (d : ℝ) * m := by
    have : 1 ≤ d * m := Nat.one_le_iff_ne_zero.mpr (by positivity)
    exact_mod_cast this
  set s : ℝ := Real.sqrt ((d : ℝ) * m)
  have hs1 : 1 ≤ s := by rw [Real.one_le_sqrt]; exact hdm1
  have hss : s * s = (d : ℝ) * m := Real.mul_self_sqrt (by positivity)
  have hAge : s ≤ A := by
    have h1 : d * m < (Nat.sqrt (d * m) + 1) * (Nat.sqrt (d * m) + 1) :=
      Nat.lt_succ_sqrt (d * m)
    have h2 : (d : ℝ) * m < (A : ℝ) * A := by
      rw [hAdef]; exact_mod_cast h1
    have hA0 : (0 : ℝ) ≤ A := by positivity
    nlinarith [Real.sqrt_nonneg ((d : ℝ) * m)]
  have hAle : (A : ℝ) ≤ 2 * s := by
    have h1 : Nat.sqrt (d * m) * Nat.sqrt (d * m) ≤ d * m := Nat.sqrt_le (d * m)
    have h2 : ((Nat.sqrt (d * m) : ℕ) : ℝ) * (Nat.sqrt (d * m)) ≤ (d : ℝ) * m := by
      exact_mod_cast h1
    have h3 : ((Nat.sqrt (d * m) : ℕ) : ℝ) ≤ s := by
      rw [Real.le_sqrt (by positivity) (by positivity)]
      nlinarith
    rw [hAdef]; push_cast; linarith
  have hmain := harmonic_diff_le U hH hM i j hi hj (m : ℤ) (by exact_mod_cast hm)
    (by exact_mod_cast hbx) (by exact_mod_cast hby) A hA1
  have hApos : (0 : ℝ) < A := by exact_mod_cast hA1
  
  have hsq : Real.sqrt (d / m) * s = d := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show (d : ℝ) / m * (d * m) = d * d by field_simp]
    exact Real.sqrt_mul_self (by positivity)
  have hdA : (d : ℝ) / A ≤ Real.sqrt (d / m) := by
    rw [div_le_iff₀ hApos]
    have : (d : ℝ) = Real.sqrt (d / m) * s := hsq.symm
    calc (d : ℝ) = Real.sqrt (d / m) * s := this
      _ ≤ Real.sqrt (d / m) * A := by gcongr
  have hA2 : 2 * ((A : ℝ) ^ 2) / ((m : ℝ) ^ 2) ≤ 8 * Real.sqrt (d / m) := by
    have h1 : (A : ℝ) ^ 2 ≤ 4 * (d * m) := by nlinarith
    have h2 : 2 * ((A : ℝ) ^ 2) / ((m : ℝ) ^ 2) ≤ 8 * (d / m) := by
      rw [div_le_iff₀ (by positivity)]
      have : 8 * ((d : ℝ) / m) * (m : ℝ) ^ 2 = 8 * (d * m) := by field_simp
      rw [this]; linarith
    have h3 : (d : ℝ) / m ≤ Real.sqrt (d / m) := by
      have hle : (d : ℝ) / m ≤ 1 := by
        rw [div_le_one hmpos]; exact_mod_cast hdm.le
      have h0 : (0 : ℝ) ≤ d / m := by positivity
      rw [Real.le_sqrt h0 h0]
      nlinarith
    linarith
  have hiA : 2 * |(i : ℝ)| / A ≤ 2 * Real.sqrt (d / m) := by
    have : 2 * |(i : ℝ)| / A ≤ 2 * ((d : ℝ) / A) := by
      rw [mul_div_assoc]; gcongr
    linarith
  have hjA : 2 * |(j : ℝ)| / A ≤ 2 * Real.sqrt (d / m) := by
    have : 2 * |(j : ℝ)| / A ≤ 2 * ((d : ℝ) / A) := by
      rw [mul_div_assoc]; gcongr
    linarith
  simp only [Int.cast_natCast] at hmain
  calc |H x - H y| ≤ 2 * M * (2 * |(i : ℝ)| / A + 2 * |(j : ℝ)| / A +
        2 * ((A : ℝ) ^ 2) / ((m : ℝ) ^ 2)) := hmain
    _ ≤ 2 * M * (2 * Real.sqrt (d / m) + 2 * Real.sqrt (d / m) + 8 * Real.sqrt (d / m)) := by
        gcongr
    _ = 24 * M * Real.sqrt (d / m) := by ring

 


theorem harmonic_diff_sqrt (U : Finset (ℤ × ℤ)) {H : ℤ × ℤ → ℝ}
    (hH : ∀ a ∈ U, H a = avg H a) {M : ℝ} (hM : ∀ c, |H c| ≤ M)
    {x y : ℤ × ℤ} (d : ℕ) (hd1 : |x.1 - y.1| ≤ d) (hd2 : |x.2 - y.2| ≤ d)
    (m : ℕ) (hm : 2 ≤ m)
    (hbx : ∀ c : ℤ × ℤ, |c.1 - x.1| < m → |c.2 - x.2| < m → c ∈ U)
    (hby : ∀ c : ℤ × ℤ, |c.1 - y.1| < m → |c.2 - y.2| < m → c ∈ U) :
    |H x - H y| ≤ 48 * M * Real.sqrt (d / m) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  by_cases hpar : (du (x, y)) % 2 = 0
  · have := harmonic_diff_even U hH hM hpar d hd1 hd2 m (by omega) hbx hby
    have h2 : 24 * M * Real.sqrt (d / m) ≤ 48 * M * Real.sqrt (d / m) := by
      have := Real.sqrt_nonneg ((d : ℝ) / m); nlinarith
    linarith
  
  have hyU : y ∈ U := hby y (by simp; omega) (by simp; omega)
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · exfalso
    apply hpar
    subst hd0
    unfold du
    have h1' := abs_le.mp hd1
    have h2' := abs_le.mp hd2
    push_cast at h1' h2'
    have h1 : x.1 = y.1 := by omega
    have h2 : x.2 = y.2 := by omega
    rw [h1, h2]; simp
  have hstep : ∀ s : Bool × Bool,
      |H x - H (y + stepVec s)| ≤ 24 * M * Real.sqrt ((2 * d : ℕ) / (m - 1 : ℕ)) := by
    intro s
    have hs1 : |(stepVec s).1| ≤ 1 := by rcases s with ⟨_ | _, _ | _⟩ <;> simp [stepVec]
    have hs2 : |(stepVec s).2| ≤ 1 := by rcases s with ⟨_ | _, _ | _⟩ <;> simp [stepVec]
    have hsadd := stepVec_add s
    have hpar' : (du (x, y + stepVec s)) % 2 = 0 := by
      simp only [du, Prod.fst_add, Prod.snd_add] at hpar hsadd ⊢
      have : sgn s.1 = 1 ∨ sgn s.1 = -1 := by rcases s with ⟨_ | _, _⟩ <;> simp [sgn]
      omega
    apply harmonic_diff_even U hH hM hpar' (2 * d) _ _ (m - 1) (by omega)
    · intro c h1 h2
      apply hbx c
      · push_cast [Nat.cast_sub (show 1 ≤ m by omega)] at h1; omega
      · push_cast [Nat.cast_sub (show 1 ≤ m by omega)] at h2; omega
    · intro c h1 h2
      apply hby c
      · push_cast [Nat.cast_sub (show 1 ≤ m by omega)] at h1
        simp only [Prod.fst_add] at h1
        rw [abs_lt] at h1 ⊢; rw [abs_le] at hs1; constructor <;> omega
      · push_cast [Nat.cast_sub (show 1 ≤ m by omega)] at h2
        simp only [Prod.snd_add] at h2
        rw [abs_lt] at h2 ⊢; rw [abs_le] at hs2; constructor <;> omega
    · simp only [Prod.fst_add]; push_cast
      rw [abs_le] at hd1 hs1 ⊢; constructor <;> omega
    · simp only [Prod.snd_add]; push_cast
      rw [abs_le] at hd2 hs2 ⊢; constructor <;> omega
  have hroot : Real.sqrt ((2 * d : ℕ) / (m - 1 : ℕ)) ≤ 2 * Real.sqrt (d / m) := by
    have hm1 : (0 : ℝ) < (m - 1 : ℕ) := by
      have : 0 < m - 1 := by omega
      exact_mod_cast this
    have hle : ((2 * d : ℕ) : ℝ) / (m - 1 : ℕ) ≤ 4 * (d / m) := by
      have hmm : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
      rw [show 4 * ((d : ℝ) / m) = (4 * d) / m by ring]
      rw [div_le_div_iff₀ hm1 hmpos, hmm]
      push_cast
      have hd0 : (0 : ℝ) ≤ d := by positivity
      nlinarith
    calc Real.sqrt ((2 * d : ℕ) / (m - 1 : ℕ)) ≤ Real.sqrt (4 * (d / m)) := Real.sqrt_le_sqrt hle
      _ = 2 * Real.sqrt (d / m) := by
        rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num)]
  have hHy : H y = (∑ s : Bool × Bool, H (y + stepVec s)) / 4 := hH y hyU
  have hdiff : H x - H y = (∑ s : Bool × Bool, (H x - H (y + stepVec s))) / 4 := by
    rw [hHy, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_bool,
      nsmul_eq_mul]
    ring
  rw [hdiff, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  have hsum : |∑ s : Bool × Bool, (H x - H (y + stepVec s))| ≤
      ∑ _s : Bool × Bool, 24 * M * (2 * Real.sqrt (d / m)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s _ => ?_)
    refine (hstep s).trans ?_
    gcongr
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_bool,
    nsmul_eq_mul] at hsum
  have : (0 : ℝ) ≤ M * Real.sqrt (d / m) := by positivity
  linarith

end SupercriticalLQGUniqueness.B2.QPos.P4
