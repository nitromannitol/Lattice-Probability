/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P7DST at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib

 







set_option autoImplicit false
noncomputable section

open Real Finset

namespace SupercriticalLQGUniqueness.B2.QPos.P7

 
lemma sum_cos_mul_two_sin (M : ℕ) (x : ℝ) :
    (∑ j ∈ range M, Real.cos (j * x)) * (2 * Real.sin (x / 2)) =
      Real.sin ((M - 1 / 2) * x) + Real.sin (x / 2) := by
  induction M with
  | zero =>
    simp only [range_zero, sum_empty, zero_mul, CharP.cast_eq_zero, zero_sub]
    rw [show -(1 / 2 : ℝ) * x = -(x / 2) by ring, Real.sin_neg]; ring
  | succ M ih =>
    rw [sum_range_succ, add_mul, ih]
    have h1 : (((M : ℝ) + 1 / 2) * x - ((M : ℝ) - 1 / 2) * x) / 2 = x / 2 := by ring
    have h2 : (((M : ℝ) + 1 / 2) * x + ((M : ℝ) - 1 / 2) * x) / 2 = M * x := by ring
    have h3 := Real.sin_sub_sin (((M : ℝ) + 1 / 2) * x) (((M : ℝ) - 1 / 2) * x)
    rw [h1, h2] at h3
    push_cast
    rw [show ((M : ℝ) + 1 - 1 / 2) = (M : ℝ) + 1 / 2 by ring]
    linarith

 
lemma sum_cos_eq (M : ℕ) (hM : 0 < M) (m : ℤ) :
    ∑ j ∈ range M, Real.cos (j * (m * π / M)) =
      if (2 * M : ℤ) ∣ m then (M : ℝ) else (1 - Real.cos (m * π)) / 2 := by
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  split_ifs with h
  · obtain ⟨r, rfl⟩ := h
    have hone : ∀ j ∈ range M,
        Real.cos (j * ((((2 * M * r : ℤ)) : ℝ) * π / M)) = 1 := by
      intro j _
      have : (j : ℝ) * ((((2 * M * r : ℤ)) : ℝ) * π / M) = ((j * r : ℤ) : ℝ) * (2 * π) := by
        push_cast; field_simp
      rw [this, Real.cos_int_mul_two_pi]
    rw [sum_congr rfl hone]; simp
  · have hs : Real.sin (m * π / M / 2) ≠ 0 := by
      intro h0
      rw [Real.sin_eq_zero_iff] at h0
      obtain ⟨r, hr⟩ := h0
      apply h
      refine ⟨r, ?_⟩
      have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
      have : (m : ℝ) = 2 * M * r := by
        field_simp at hr
        linarith
      exact_mod_cast this
    have key := sum_cos_mul_two_sin M (m * π / M)
    have hsin : Real.sin ((M - 1 / 2) * (m * π / M)) =
        -Real.cos (m * π) * Real.sin (m * π / M / 2) := by
      have : ((M : ℝ) - 1 / 2) * (m * π / M) = m * π - m * π / M / 2 := by
        field_simp
      rw [this, Real.sin_sub, Real.sin_int_mul_pi]; ring
    rw [hsin] at key
    have key' : (∑ j ∈ range M, Real.cos (j * (m * π / M))) * Real.sin (m * π / M / 2) =
        ((1 - Real.cos (m * π)) / 2) * Real.sin (m * π / M / 2) := by linarith
    exact mul_right_cancel₀ hs key'

 
def sites1 (N : ℕ) : Finset ℤ := Icc (-((N : ℤ) - 1)) ((N : ℤ) - 1)

 
def modes (N : ℕ) : Finset ℤ := Icc (1 : ℤ) (2 * N - 1)

 
def dsin (N : ℕ) (k a : ℤ) : ℝ := Real.sin (k * π * (a + N) / (2 * N))

lemma dsin_neg_boundary (N : ℕ) (k : ℤ) : dsin N k (-N) = 0 := by
  simp [dsin]

lemma dsin_pos_boundary (N : ℕ) (hN : 0 < N) (k : ℤ) : dsin N k N = 0 := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold dsin
  rw [show (k : ℝ) * π * ((N : ℤ) + N) / (2 * N) = k * π by push_cast; field_simp; ring]
  exact Real.sin_int_mul_pi k

 
lemma sum_sites1_eq (N : ℕ) (f : ℤ → ℝ) (hf : f (-N) = 0) :
    ∑ a ∈ sites1 N, f a = ∑ j ∈ range (2 * N), f ((j : ℤ) - N) := by
  have hrange : ∑ j ∈ range (2 * N), f ((j : ℤ) - N) =
      ∑ a ∈ Ico (-(N : ℤ)) N, f a := by
    refine sum_nbij' (fun j => (j : ℤ) - N) (fun a => (a + N).toNat) ?_ ?_ ?_ ?_ ?_
    · intro j hj
      simp only [mem_range] at hj
      simp only [mem_Ico]; omega
    · intro a ha
      simp only [mem_Ico] at ha
      simp only [mem_range]; omega
    · intro j _; simp
    · intro a ha
      simp only [mem_Ico] at ha
      show ((a + N).toNat : ℤ) - N = a
      omega
    · intro j _; rfl
  rw [hrange]
  have hsplit : Ico (-(N : ℤ)) N = insert (-(N : ℤ)) (sites1 N) ∨ N = 0 := by
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · exact Or.inr h0
    · left
      ext a; simp only [mem_Ico, mem_insert, sites1, mem_Icc]; omega
  rcases hsplit with hs | h0
  · rw [hs, sum_insert]
    · rw [hf, zero_add]
    · simp [sites1]
  · subst h0; simp [sites1]

 
lemma sin_mul_sin' (x y : ℝ) :
    Real.sin x * Real.sin y = (Real.cos (x - y) - Real.cos (x + y)) / 2 := by
  rw [Real.cos_sub, Real.cos_add]; ring

 

theorem dsin_orth (N : ℕ) (hN : 0 < N) (k l : ℤ) :
    ∑ a ∈ sites1 N, dsin N k a * dsin N l a =
      N * ((if (4 * N : ℤ) ∣ k - l then (1 : ℝ) else 0) -
        (if (4 * N : ℤ) ∣ k + l then (1 : ℝ) else 0)) := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [sum_sites1_eq N _ (by simp [dsin])]
  have hterm : ∀ j ∈ range (2 * N), dsin N k ((j : ℤ) - N) * dsin N l ((j : ℤ) - N) =
      (Real.cos (j * (((k - l : ℤ) : ℝ) * π / ((2 * N : ℕ) : ℝ))) -
        Real.cos (j * (((k + l : ℤ) : ℝ) * π / ((2 * N : ℕ) : ℝ)))) / 2 := by
    intro j _
    unfold dsin
    rw [sin_mul_sin']
    congr 3 <;> push_cast <;> field_simp <;> ring
  rw [sum_congr rfl hterm, ← sum_div, sum_sub_distrib,
    sum_cos_eq (2 * N) (by omega), sum_cos_eq (2 * N) (by omega)]
  have h4 : ((2 * ((2 * N : ℕ) : ℤ)) : ℤ) = 4 * N := by push_cast; ring
  rw [h4]
  have hpar : Real.cos (((k + l : ℤ) : ℝ) * π) = Real.cos (((k - l : ℤ) : ℝ) * π) := by
    have : (((k + l : ℤ) : ℝ) * π) = ((k - l : ℤ) : ℝ) * π + (l : ℤ) * (2 * π) := by
      push_cast; ring
    rw [this, Real.cos_add_int_mul_two_pi]
  have heven : ∀ m : ℤ, (4 * N : ℤ) ∣ m → Real.cos ((m : ℝ) * π) = 1 := by
    intro m ⟨r, hr⟩
    have : (m : ℝ) * π = ((N * r : ℤ) : ℝ) * (2 * π) * 2 := by
      rw [hr]; push_cast; ring
    rw [this, show ((N * r : ℤ) : ℝ) * (2 * π) * 2 = ((2 * (N * r) : ℤ) : ℝ) * (2 * π) by
      push_cast; ring, Real.cos_int_mul_two_pi]
  split_ifs with h1 h2 h2
  · push_cast; ring
  · rw [hpar, heven _ h1]; push_cast; ring
  · rw [← hpar, heven _ h2]; push_cast; ring
  · rw [hpar]; ring

 
theorem dsin_orth_modes (N : ℕ) (hN : 0 < N) {k l : ℤ} (hk : k ∈ modes N)
    (hl : l ∈ modes N) :
    ∑ a ∈ sites1 N, dsin N k a * dsin N l a = if k = l then (N : ℝ) else 0 := by
  rw [dsin_orth N hN]
  simp only [modes, mem_Icc] at hk hl
  have hsum : ¬ (4 * N : ℤ) ∣ k + l := by
    rintro ⟨r, hr⟩
    rcases lt_trichotomy r 0 with h | h | h
    · nlinarith
    · subst h; omega
    · nlinarith
  by_cases hkl : k = l
  · subst hkl; simp [hsum]
  · have hdiff : ¬ (4 * N : ℤ) ∣ k - l := by
      rintro ⟨r, hr⟩
      rcases lt_trichotomy r 0 with h | h | h
      · nlinarith
      · subst h; omega
      · nlinarith
    simp [hsum, hdiff, hkl]

 
lemma sum_modes_eq (N : ℕ) (f : ℤ → ℝ) :
    ∑ k ∈ modes N, f k = ∑ j ∈ sites1 N, f (j + N) := by
  refine sum_nbij' (fun k => k - N) (fun j => j + N) ?_ ?_ ?_ ?_ ?_
  · intro k hk; simp only [modes, mem_Icc] at hk
    simp only [sites1, mem_Icc]; omega
  · intro j hj; simp only [sites1, mem_Icc] at hj
    simp only [modes, mem_Icc]; omega
  · intro k _; simp
  · intro j _; simp
  · intro k _; simp

 
theorem dsin_complete (N : ℕ) (hN : 0 < N) {a b : ℤ} (ha : a ∈ sites1 N)
    (hb : b ∈ sites1 N) :
    ∑ k ∈ modes N, dsin N k a * dsin N k b = if a = b then (N : ℝ) else 0 := by
  classical
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  let S : Matrix (sites1 N) (sites1 N) ℝ := fun x j => dsin N (j.1 + N) x.1
  have hSTS : ((N : ℝ)⁻¹ • S.transpose) * S = 1 := by
    ext j j'
    rw [Matrix.smul_mul, Matrix.smul_apply, Matrix.mul_apply]
    have hj : j.1 + N ∈ modes N := by
      have := j.2; simp only [sites1, mem_Icc] at this; simp only [modes, mem_Icc]; omega
    have hj' : j'.1 + N ∈ modes N := by
      have := j'.2; simp only [sites1, mem_Icc] at this; simp only [modes, mem_Icc]; omega
    have hsum : ∑ x : sites1 N, S.transpose j x * S x j' =
        ∑ x ∈ sites1 N, dsin N (j.1 + N) x * dsin N (j'.1 + N) x := by
      rw [← sum_coe_sort (sites1 N)]; rfl
    rw [hsum, dsin_orth_modes N hN hj hj']
    by_cases hjj : j = j'
    · subst hjj; simp [hN']
    · have : j.1 + N ≠ j'.1 + N := fun h => hjj (Subtype.ext (by linarith))
      simp [hjj, this]
  have hSST := mul_eq_one_comm.mp hSTS
  have hab := congrFun (congrFun hSST ⟨a, ha⟩) ⟨b, hb⟩
  rw [Matrix.mul_smul, Matrix.smul_apply, Matrix.mul_apply] at hab
  rw [sum_modes_eq]
  have hsum : ∑ j : sites1 N, S ⟨a, ha⟩ j * S.transpose j ⟨b, hb⟩ =
      ∑ j ∈ sites1 N, dsin N (j + N) a * dsin N (j + N) b := by
    rw [← sum_coe_sort (sites1 N)]; rfl
  rw [hsum] at hab
  by_cases h : a = b
  · subst h
    simp only [Matrix.one_apply_eq, smul_eq_mul] at hab
    rw [ite_eq_left_iff.mpr (fun h => absurd rfl h)]
    field_simp at hab ⊢
    linarith
  · have hne : (⟨a, ha⟩ : sites1 N) ≠ ⟨b, hb⟩ := fun h' => h (congrArg Subtype.val h')
    rw [Matrix.one_apply_ne hne, smul_eq_mul] at hab
    rw [ite_eq_right_iff.mpr (fun h' => absurd h' h)]
    have := mul_eq_zero.mp hab
    rcases this with h0 | h0
    · exact absurd h0 (inv_ne_zero hN')
    · exact h0

 
theorem dsin_add_one_add_sub_one (N : ℕ) (k a : ℤ) :
    dsin N k (a + 1) + dsin N k (a - 1) =
      2 * Real.cos (k * π / (2 * N)) * dsin N k a := by
  unfold dsin
  have e1 : (k : ℝ) * π * (((a + 1 : ℤ) : ℝ) + N) / (2 * N) =
      k * π * (a + N) / (2 * N) + k * π / (2 * N) := by push_cast; ring
  have e2 : (k : ℝ) * π * (((a - 1 : ℤ) : ℝ) + N) / (2 * N) =
      k * π * (a + N) / (2 * N) - k * π / (2 * N) := by push_cast; ring
  rw [e1, e2, Real.sin_add, Real.sin_sub]; ring

lemma abs_dsin_le (N : ℕ) (k a : ℤ) : |dsin N k a| ≤ 1 := Real.abs_sin_le_one _

 
lemma dsin_add_period (N : ℕ) (hN : 0 < N) (k m a : ℤ) :
    dsin N (k + 4 * N * m) a = dsin N k a := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold dsin
  have : (((k + 4 * N * m : ℤ)) : ℝ) * π * (a + N) / (2 * N) =
      k * π * (a + N) / (2 * N) + ((m * (a + N) : ℤ) : ℝ) * (2 * π) := by
    push_cast; field_simp; ring
  rw [this, Real.sin_add_int_mul_two_pi]

lemma dsin_neg_freq (N : ℕ) (k a : ℤ) : dsin N (-k) a = -dsin N k a := by
  unfold dsin
  rw [show ((-k : ℤ) : ℝ) * π * (a + N) / (2 * N) = -(k * π * (a + N) / (2 * N)) by
    push_cast; ring, Real.sin_neg]

end SupercriticalLQGUniqueness.B2.QPos.P7
