/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P4Gambler at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import Mathlib

 













set_option autoImplicit false
noncomputable section

open Finset

namespace SupercriticalLQGUniqueness.B2.QPos.P4

 
def gam (h : ℤ → ℝ) (i : ℤ) : ℝ := if i = 0 then h 0 else (h (i + 1) + h (i - 1)) / 2

 
def gamA (A : ℤ) (h : ℤ → ℝ) (i : ℤ) : ℝ :=
  if i = 0 ∨ A ≤ |i| then h i else (h (i + 1) + h (i - 1)) / 2

theorem gam_of_zero (h : ℤ → ℝ) : gam h 0 = h 0 := if_pos rfl

theorem gam_of_ne (h : ℤ → ℝ) {i : ℤ} (hi : i ≠ 0) : gam h i = (h (i + 1) + h (i - 1)) / 2 :=
  if_neg hi

theorem gamA_of_frozen (A : ℤ) (h : ℤ → ℝ) {i : ℤ} (hi : i = 0 ∨ A ≤ |i|) : gamA A h i = h i :=
  if_pos hi

theorem gamA_of_mid (A : ℤ) (h : ℤ → ℝ) {i : ℤ} (hi : ¬ (i = 0 ∨ A ≤ |i|)) :
    gamA A h i = (h (i + 1) + h (i - 1)) / 2 := if_neg hi

theorem gamA_mono (A : ℤ) {f g : ℤ → ℝ} (h : ∀ i, f i ≤ g i) (i : ℤ) :
    gamA A f i ≤ gamA A g i := by
  by_cases hi : i = 0 ∨ A ≤ |i|
  · rw [gamA_of_frozen A _ hi, gamA_of_frozen A _ hi]; exact h i
  · rw [gamA_of_mid A _ hi, gamA_of_mid A _ hi]; linarith [h (i + 1), h (i - 1)]

theorem gamAIter_mono (A : ℤ) (t : ℕ) {f g : ℤ → ℝ} (h : ∀ i, f i ≤ g i) (i : ℤ) :
    (gamA A)^[t] f i ≤ (gamA A)^[t] g i := by
  induction t generalizing i with
  | zero => exact h i
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact gamA_mono A ih i

theorem gamAIter_add (A : ℤ) (t : ℕ) (f g : ℤ → ℝ) (i : ℤ) :
    (gamA A)^[t] (fun j => f j + g j) i = (gamA A)^[t] f i + (gamA A)^[t] g i := by
  induction t generalizing i with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply']
    have hfun : (gamA A)^[t] (fun j => f j + g j) =
        fun j => (gamA A)^[t] f j + (gamA A)^[t] g j := funext ih
    rw [hfun]
    by_cases hi : i = 0 ∨ A ≤ |i|
    · rw [gamA_of_frozen A _ hi, gamA_of_frozen A _ hi, gamA_of_frozen A _ hi]
    · rw [gamA_of_mid A _ hi, gamA_of_mid A _ hi, gamA_of_mid A _ hi]; ring

theorem gamAIter_smul (A : ℤ) (t : ℕ) (r : ℝ) (f : ℤ → ℝ) (i : ℤ) :
    (gamA A)^[t] (fun j => r * f j) i = r * (gamA A)^[t] f i := by
  induction t generalizing i with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have hfun : (gamA A)^[t] (fun j => r * f j) = fun j => r * (gamA A)^[t] f j := funext ih
    rw [hfun]
    by_cases hi : i = 0 ∨ A ≤ |i|
    · rw [gamA_of_frozen A _ hi, gamA_of_frozen A _ hi]
    · rw [gamA_of_mid A _ hi, gamA_of_mid A _ hi]; ring

theorem gamAIter_nonneg (A : ℤ) (t : ℕ) {f : ℤ → ℝ} (h : ∀ i, 0 ≤ f i) (i : ℤ) :
    0 ≤ (gamA A)^[t] f i := by
  induction t generalizing i with
  | zero => exact h i
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    by_cases hi : i = 0 ∨ A ≤ |i|
    · rw [gamA_of_frozen A _ hi]; exact ih i
    · rw [gamA_of_mid A _ hi]; linarith [ih (i + 1), ih (i - 1)]

theorem gamIter_le_one (t : ℕ) {f : ℤ → ℝ} (h : ∀ i, f i ≤ 1) (i : ℤ) :
    gam^[t] f i ≤ 1 := by
  induction t generalizing i with
  | zero => exact h i
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    by_cases hi : i = 0
    · subst hi; rw [gam_of_zero]; exact ih 0
    · rw [gam_of_ne _ hi]; linarith [ih (i + 1), ih (i - 1)]

theorem gamIter_zero (t : ℕ) (f : ℤ → ℝ) : gam^[t] f 0 = f 0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', gam_of_zero]
    exact ih

theorem gamAIter_frozen (A : ℤ) (t : ℕ) (f : ℤ → ℝ) {i : ℤ} (hi : i = 0 ∨ A ≤ |i|) :
    (gamA A)^[t] f i = f i := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', gamA_of_frozen A _ hi]
    exact ih

 
def nz (j : ℤ) : ℝ := if j = 0 then 0 else 1

theorem nz_le_one (j : ℤ) : nz j ≤ 1 := by unfold nz; split_ifs <;> norm_num
theorem nz_nonneg (j : ℤ) : 0 ≤ nz j := by unfold nz; split_ifs <;> norm_num

 
theorem gamIter_le_gamAIter (A : ℤ) (t : ℕ) (i : ℤ) :
    gam^[t] nz i ≤ (gamA A)^[t] nz i := by
  induction t generalizing i with
  | zero => exact le_rfl
  | succ t ih =>
    by_cases h0 : i = 0
    · subst h0
      rw [gamIter_zero, gamAIter_frozen A _ nz (Or.inl rfl)]
    · by_cases hA : A ≤ |i|
      · rw [gamAIter_frozen A _ nz (Or.inr hA)]
        have hnz : nz i = 1 := by unfold nz; rw [if_neg h0]
        rw [hnz]
        exact gamIter_le_one (t + 1) nz_le_one i
      · rw [Function.iterate_succ_apply', Function.iterate_succ_apply', gam_of_ne _ h0,
          gamA_of_mid A _ (by tauto)]
        linarith [ih (i + 1), ih (i - 1)]

 
def ruinFn (A : ℤ) (i : ℤ) : ℝ := (min |i| A : ℤ) / (A : ℝ)

theorem gamA_ruinFn (A : ℤ) (hA : 1 ≤ A) (i : ℤ) : gamA A (ruinFn A) i = ruinFn A i := by
  by_cases h : i = 0 ∨ A ≤ |i|
  · rw [gamA_of_frozen A _ h]
  · rw [gamA_of_mid A _ h]
    push_neg at h
    obtain ⟨h0, hlt⟩ := h
    unfold ruinFn
    have hApos : (0 : ℝ) < A := by exact_mod_cast (show (0 : ℤ) < A by omega)
    rcases lt_or_gt_of_ne h0 with hneg | hpos
    · have hlt' : -i < A := by rw [abs_of_neg hneg] at hlt; exact hlt
      have e1 : min |i + 1| A = -(i + 1) := by
        rw [abs_of_nonpos (by omega)]; omega
      have e2 : min |i - 1| A = -(i - 1) := by
        rw [abs_of_neg (by omega)]
        rw [abs_of_neg hneg] at hlt
        omega
      have e3 : min |i| A = -i := by rw [abs_of_neg hneg]; omega
      rw [e1, e2, e3]
      field_simp
      push_cast
      ring
    · have e1 : min |i + 1| A = i + 1 := by
        rw [abs_of_pos (by omega)]
        rw [abs_of_pos hpos] at hlt
        omega
      have e2 : min |i - 1| A = i - 1 := by
        rw [abs_of_nonneg (by omega)]; omega
      have e3 : min |i| A = i := by rw [abs_of_pos hpos]; omega
      rw [e1, e2, e3]
      field_simp
      push_cast
      ring

theorem gamAIter_ruinFn (A : ℤ) (hA : 1 ≤ A) (t : ℕ) : (gamA A)^[t] (ruinFn A) = ruinFn A := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ', Function.comp_apply, ih]
    funext i
    exact gamA_ruinFn A hA i

 
def occFn (A : ℤ) (i : ℤ) : ℝ := max 0 (((|i| * (A - |i|) : ℤ) : ℝ))

 
def midInd (A : ℤ) (i : ℤ) : ℝ := if i = 0 ∨ A ≤ |i| then 0 else 1

theorem occFn_nonneg (A i : ℤ) : 0 ≤ occFn A i := le_max_left _ _

theorem occFn_of_le {A i : ℤ} (h : |i| ≤ A) :
    occFn A i = (((|i| * (A - |i|) : ℤ) : ℝ)) := by
  unfold occFn
  apply max_eq_right
  have : 0 ≤ |i| * (A - |i|) := mul_nonneg (abs_nonneg i) (by omega)
  exact_mod_cast this

theorem midInd_le_occ_sub (A : ℤ) (i : ℤ) :
    midInd A i ≤ occFn A i - gamA A (occFn A) i := by
  by_cases h : i = 0 ∨ A ≤ |i|
  · rw [gamA_of_frozen A _ h]
    unfold midInd; rw [if_pos h]; simp
  · rw [gamA_of_mid A _ h]
    unfold midInd; rw [if_neg h]
    push_neg at h
    obtain ⟨h0, hlt⟩ := h
    rcases lt_or_gt_of_ne h0 with hneg | hpos
    · have ha : |i| = -i := abs_of_neg hneg
      have ha1 : |i + 1| = -(i + 1) := abs_of_nonpos (by omega)
      have ha2 : |i - 1| = -(i - 1) := abs_of_neg (by omega)
      rw [ha] at hlt
      rw [occFn_of_le (by omega), occFn_of_le (by omega), occFn_of_le (by omega)]
      rw [ha, ha1, ha2]
      have : ((((-i) * (A - -i) : ℤ) : ℝ)) -
          (((((-(i + 1)) * (A - -(i + 1)) : ℤ) : ℝ)) +
            ((((-(i - 1)) * (A - -(i - 1)) : ℤ) : ℝ))) / 2 = 1 := by
        push_cast; ring
      linarith
    · have ha : |i| = i := abs_of_pos hpos
      have ha1 : |i + 1| = i + 1 := abs_of_pos (by omega)
      have ha2 : |i - 1| = i - 1 := abs_of_nonneg (by omega)
      rw [ha] at hlt
      rw [occFn_of_le (by omega), occFn_of_le (by omega), occFn_of_le (by omega)]
      rw [ha, ha1, ha2]
      have : (((i * (A - i) : ℤ) : ℝ)) -
          ((((i + 1) * (A - (i + 1)) : ℤ) : ℝ) +
            ((((i - 1) * (A - (i - 1)) : ℤ) : ℝ))) / 2 = 1 := by
        push_cast; ring
      linarith

theorem gamA_midInd_le (A : ℤ) (i : ℤ) : gamA A (midInd A) i ≤ midInd A i := by
  by_cases h : i = 0 ∨ A ≤ |i|
  · rw [gamA_of_frozen A _ h]
  · rw [gamA_of_mid A _ h]
    unfold midInd
    rw [if_neg h]
    have h1 : midInd A (i + 1) ≤ 1 := by unfold midInd; split_ifs <;> norm_num
    have h2 : midInd A (i - 1) ≤ 1 := by unfold midInd; split_ifs <;> norm_num
    unfold midInd at h1 h2
    linarith

theorem gamAIter_midInd_anti (A : ℤ) (t : ℕ) (i : ℤ) :
    (gamA A)^[t + 1] (midInd A) i ≤ (gamA A)^[t] (midInd A) i := by
  rw [Function.iterate_succ_apply]
  exact gamAIter_mono A t (gamA_midInd_le A) i

 
theorem sum_gamAIter_midInd_le (A : ℤ) (t : ℕ) (i : ℤ) :
    ∑ s ∈ range t, (gamA A)^[s] (midInd A) i ≤ occFn A i := by
  have key : ∀ t : ℕ, ∀ i : ℤ,
      ∑ s ∈ range t, (gamA A)^[s] (midInd A) i ≤ occFn A i - (gamA A)^[t] (occFn A) i := by
    intro t
    induction t with
    | zero => intro i; simp
    | succ t ih =>
      intro i
      rw [sum_range_succ]
      have h1 := ih i
      have h2 : (gamA A)^[t] (midInd A) i ≤
          (gamA A)^[t] (occFn A) i - (gamA A)^[t] (gamA A (occFn A)) i := by
        have := gamAIter_mono A t (midInd_le_occ_sub A) i
        have e := gamAIter_add A t (occFn A) (fun j => -1 * gamA A (occFn A) j) i
        rw [gamAIter_smul] at e
        have e' : (gamA A)^[t] (fun j => occFn A j - gamA A (occFn A) j) i =
            (gamA A)^[t] (occFn A) i - (gamA A)^[t] (gamA A (occFn A)) i := by
          rw [show (fun j => occFn A j - gamA A (occFn A) j) =
              (fun j => occFn A j + -1 * gamA A (occFn A) j) by funext j; ring, e]
          ring
        linarith
      rw [← Function.iterate_succ_apply] at h2
      linarith
  have := key t i
  have h0 : 0 ≤ (gamA A)^[t] (occFn A) i := gamAIter_nonneg A t (occFn_nonneg A) i
  linarith

theorem ruinFn_nonneg (A : ℤ) (hA : 1 ≤ A) (j : ℤ) : 0 ≤ ruinFn A j := by
  unfold ruinFn
  have hApos : (0 : ℝ) < A := by exact_mod_cast (show (0 : ℤ) < A by omega)
  apply div_nonneg _ hApos.le
  exact_mod_cast le_min (abs_nonneg j) (by omega)

theorem nz_le_far_add_mid (A : ℤ) (hA : 1 ≤ A) (j : ℤ) :
    nz j ≤ ruinFn A j + midInd A j := by
  have hr := ruinFn_nonneg A hA j
  have hApos : (0 : ℝ) < A := by exact_mod_cast (show (0 : ℤ) < A by omega)
  by_cases h1 : j = 0
  · unfold nz; rw [if_pos h1]
    unfold midInd; rw [if_pos (Or.inl h1)]
    linarith
  · unfold nz; rw [if_neg h1]
    by_cases h2 : A ≤ |j|
    · unfold midInd; rw [if_pos (Or.inr h2)]
      unfold ruinFn
      rw [min_eq_right h2, div_self hApos.ne']
      norm_num
    · unfold midInd; rw [if_neg (by tauto)]
      linarith

theorem gamAIter_midInd_anti' (A : ℤ) (i : ℤ) (s k : ℕ) :
    (gamA A)^[s + k] (midInd A) i ≤ (gamA A)^[s] (midInd A) i := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    have := gamAIter_midInd_anti A (s + k) i
    rw [show s + (k + 1) = s + k + 1 by ring]
    exact this.trans ih

 
theorem gamIter_nz_le (A : ℕ) (hA : 1 ≤ A) (i : ℤ) :
    gam^[A ^ 2] nz i ≤ 2 * |(i : ℝ)| / A := by
  set Az : ℤ := (A : ℤ)
  have hAz : 1 ≤ Az := by simp only [Az]; exact_mod_cast hA
  have hApos : (0 : ℝ) < A := by exact_mod_cast hA
  have h1 := gamIter_le_gamAIter Az (A ^ 2) i
  have h2 : (gamA Az)^[A ^ 2] nz i ≤
      (gamA Az)^[A ^ 2] (ruinFn Az) i + (gamA Az)^[A ^ 2] (midInd Az) i := by
    rw [← gamAIter_add]
    exact gamAIter_mono Az _ (nz_le_far_add_mid Az hAz) i
  rw [gamAIter_ruinFn Az hAz] at h2
  
  have hfar : ruinFn Az i ≤ |(i : ℝ)| / A := by
    unfold ruinFn
    have : ((min |i| Az : ℤ) : ℝ) ≤ |(i : ℝ)| := by
      have := min_le_left |i| Az
      have h' : ((min |i| Az : ℤ) : ℝ) ≤ ((|i| : ℤ) : ℝ) := by exact_mod_cast this
      simpa using h'
    simp only [Az]
    push_cast
    gcongr
    simpa using this
  
  have hmid : (gamA Az)^[A ^ 2] (midInd Az) i ≤ |(i : ℝ)| / A := by
    have hs := sum_gamAIter_midInd_le Az (A ^ 2) i
    have hanti : ∀ s ∈ range (A ^ 2),
        (gamA Az)^[A ^ 2] (midInd Az) i ≤ (gamA Az)^[s] (midInd Az) i := by
      intro s hs'
      have hle : s ≤ A ^ 2 := (mem_range.mp hs').le
      have := gamAIter_midInd_anti' Az i s (A ^ 2 - s)
      rwa [Nat.add_sub_cancel' hle] at this
    have hsum : ((A ^ 2 : ℕ) : ℝ) * (gamA Az)^[A ^ 2] (midInd Az) i ≤ occFn Az i := by
      have := Finset.sum_le_sum hanti
      rw [sum_const, card_range, nsmul_eq_mul] at this
      linarith
    have hocc : occFn Az i ≤ |(i : ℝ)| * A := by
      unfold occFn
      apply max_le
      · positivity
      · have h0 : (0 : ℤ) ≤ |i| := abs_nonneg _
        have hle : |i| * (Az - |i|) ≤ |i| * Az := by nlinarith
        have : (((|i| * (Az - |i|) : ℤ) : ℝ)) ≤ ((|i| * Az : ℤ) : ℝ) := by exact_mod_cast hle
        refine this.trans (le_of_eq ?_)
        simp only [Az]
        push_cast
        rfl
    have hA2 : ((A ^ 2 : ℕ) : ℝ) = (A : ℝ) * A := by push_cast; ring
    rw [hA2] at hsum
    rw [le_div_iff₀ hApos]
    nlinarith
  calc gam^[A ^ 2] nz i ≤ (gamA Az)^[A ^ 2] nz i := h1
    _ ≤ ruinFn Az i + (gamA Az)^[A ^ 2] (midInd Az) i := h2
    _ ≤ |(i : ℝ)| / A + |(i : ℝ)| / A := add_le_add hfar hmid
    _ = 2 * |(i : ℝ)| / A := by ring

end SupercriticalLQGUniqueness.B2.QPos.P4
