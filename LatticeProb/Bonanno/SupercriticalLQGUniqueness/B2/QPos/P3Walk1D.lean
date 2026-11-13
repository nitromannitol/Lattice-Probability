/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P3Walk1D at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import Mathlib

 









set_option autoImplicit false
noncomputable section

open Finset

namespace SupercriticalLQGUniqueness.B2.QPos.P3

 
def sgn (b : Bool) : ℤ := if b then 1 else -1

@[simp] theorem sgn_true : sgn true = 1 := rfl
@[simp] theorem sgn_false : sgn false = -1 := rfl

theorem abs_sgn (b : Bool) : |sgn b| = 1 := by cases b <;> simp [sgn]

 
def ext {α : Type*} [Inhabited α] {N : ℕ} (ω : Fin N → α) (i : ℕ) : α :=
  if h : i < N then ω ⟨i, h⟩ else default

theorem ext_cons_zero {α : Type*} [Inhabited α] {N : ℕ} (s : α) (ω : Fin N → α) :
    ext (Fin.cons s ω : Fin (N + 1) → α) 0 = s := by
  simp [ext]

theorem ext_cons_succ {α : Type*} [Inhabited α] {N : ℕ} (s : α) (ω : Fin N → α)
    (i : ℕ) : ext (Fin.cons s ω : Fin (N + 1) → α) (i + 1) = ext ω i := by
  unfold ext
  by_cases h : i < N
  · have h' : i + 1 < N + 1 := by omega
    rw [dif_pos h', dif_pos h]
    have : (⟨i + 1, h'⟩ : Fin (N + 1)) = Fin.succ ⟨i, h⟩ := rfl
    rw [this, Fin.cons_succ]
  · have h' : ¬ i + 1 < N + 1 := by omega
    rw [dif_neg h', dif_neg h]

theorem ext_append {α : Type*} [Inhabited α] {a b : ℕ} (σ : Fin a → α) (τ : Fin b → α)
    (i : ℕ) : ext (Fin.append σ τ) i = if i < a then ext σ i else ext τ (i - a) := by
  unfold ext
  by_cases hia : i < a
  · have h' : i < a + b := by omega
    rw [if_pos hia, dif_pos h', dif_pos hia]
    have : (⟨i, h'⟩ : Fin (a + b)) = Fin.castAdd b ⟨i, hia⟩ := rfl
    rw [this, Fin.append_left]
  · rw [if_neg hia]
    by_cases hib : i < a + b
    · have h2 : i - a < b := by omega
      rw [dif_pos hib, dif_pos h2]
      have : (⟨i, hib⟩ : Fin (a + b)) = Fin.natAdd a ⟨i - a, h2⟩ := by
        ext; simp; omega
      rw [this, Fin.append_right]
    · have h2 : ¬ i - a < b := by omega
      rw [dif_neg hib, dif_neg h2]

 
def psum {N : ℕ} (σ : Fin N → Bool) (k : ℕ) : ℤ := ∑ i ∈ range k, sgn (ext σ i)

@[simp] theorem psum_zero {N : ℕ} (σ : Fin N → Bool) : psum σ 0 = 0 := by
  simp [psum]

theorem psum_succ {N : ℕ} (σ : Fin N → Bool) (k : ℕ) :
    psum σ (k + 1) = psum σ k + sgn (ext σ k) := by
  simp [psum, sum_range_succ]

theorem psum_cons_succ {N : ℕ} (s : Bool) (σ : Fin N → Bool) (k : ℕ) :
    psum (Fin.cons s σ : Fin (N + 1) → Bool) (k + 1) = sgn s + psum σ k := by
  unfold psum
  rw [sum_range_succ']
  simp only [ext_cons_succ, ext_cons_zero]
  ring

theorem psum_append_of_le {a b : ℕ} (σ : Fin a → Bool) (τ : Fin b → Bool) {k : ℕ}
    (hk : k ≤ a) : psum (Fin.append σ τ) k = psum σ k := by
  unfold psum
  apply sum_congr rfl
  intro i hi
  have : i < a := lt_of_lt_of_le (mem_range.mp hi) hk
  rw [ext_append, if_pos this]

theorem psum_append_add {a b : ℕ} (σ : Fin a → Bool) (τ : Fin b → Bool) (k : ℕ) :
    psum (Fin.append σ τ) (a + k) = psum σ a + psum τ k := by
  unfold psum
  rw [sum_range_add]
  congr 1
  · apply sum_congr rfl
    intro i hi
    rw [ext_append, if_pos (mem_range.mp hi)]
  · apply sum_congr rfl
    intro i _
    rw [ext_append, if_neg (by omega)]
    congr 2
    omega

theorem abs_psum_le {N : ℕ} (σ : Fin N → Bool) (k : ℕ) : |psum σ k| ≤ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [psum_succ]
    have := abs_sgn (ext σ k)
    calc |psum σ k + sgn (ext σ k)| ≤ |psum σ k| + |sgn (ext σ k)| := abs_add_le _ _
      _ ≤ (k : ℤ) + 1 := by omega
      _ = ((k + 1 : ℕ) : ℤ) := by push_cast; ring

theorem psum_parity {N : ℕ} (σ : Fin N → Bool) (k : ℕ) :
    ∃ j : ℕ, j ≤ k ∧ psum σ k = 2 * (j : ℤ) - k := by
  induction k with
  | zero => exact ⟨0, le_rfl, by simp⟩
  | succ k ih =>
    obtain ⟨j, hj, hpj⟩ := ih
    rw [psum_succ, hpj]
    cases ext σ k
    · exact ⟨j, by omega, by simp; push_cast; ring⟩
    · exact ⟨j + 1, by omega, by simp; push_cast; ring⟩

 
theorem sum_cons {α : Type*} [Fintype α] {M : Type*} [AddCommMonoid M] (N : ℕ)
    (f : (Fin (N + 1) → α) → M) :
    ∑ ω, f ω = ∑ s : α, ∑ σ : Fin N → α, f (Fin.cons s σ) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv (fun _ => α)) _ _ (fun _ => rfl)).symm

 
theorem sum_append {α : Type*} [Fintype α] {M : Type*} [AddCommMonoid M] (a b : ℕ)
    (f : (Fin (a + b) → α) → M) :
    ∑ ω, f ω = ∑ σ : Fin a → α, ∑ τ : Fin b → α, f (Fin.append σ τ) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.appendEquiv a b) _ _ (fun _ => rfl)).symm

theorem card_fun_bool (N : ℕ) : Fintype.card (Fin N → Bool) = 2 ^ N := by
  simp

 
theorem sum_sq_psum (N : ℕ) (x : ℤ) :
    ∑ σ : Fin N → Bool, (x + psum σ N) ^ 2 = 2 ^ N * (x ^ 2 + N) := by
  induction N generalizing x with
  | zero => simp
  | succ N ih =>
    rw [sum_cons]
    simp only [psum_cons_succ, Fintype.sum_bool, sgn_true, sgn_false]
    have h1 := ih (x + 1)
    have h2 := ih (x + -1)
    simp only [← add_assoc]
    rw [h1, h2]
    push_cast
    ring

theorem kolmogorov_aux (a : ℤ) (ha : 0 ≤ a) (N : ℕ) (x : ℤ) :
    0 ≤ ∑ σ : Fin N → Bool, ((x + psum σ N) ^ 2 -
      a ^ 2 * (if ∃ k ≤ N, a ≤ |x + psum σ k| then 1 else 0)) := by
  classical
  induction N generalizing x with
  | zero =>
    simp only [Finset.univ_unique, sum_singleton, psum_zero, add_zero]
    split_ifs with h
    · obtain ⟨k, hk, hak⟩ := h
      have : k = 0 := by omega
      subst this
      simp at hak
      nlinarith [abs_nonneg x, sq_abs x]
    · nlinarith [sq_nonneg x]
  | succ N ih =>
    by_cases hx : a ≤ |x|
    · have hev : ∀ σ : Fin (N + 1) → Bool, ∃ k ≤ N + 1, a ≤ |x + psum σ k| :=
        fun σ => ⟨0, Nat.zero_le _, by simpa using hx⟩
      simp only [hev, if_true, mul_one]
      rw [sum_sub_distrib, sum_sq_psum]
      simp only [sum_const, card_univ, card_fun_bool, nsmul_eq_mul]
      push_cast
      have : a ^ 2 ≤ x ^ 2 := by nlinarith [abs_nonneg x, sq_abs x]
      nlinarith [pow_pos (show (0 : ℤ) < 2 by norm_num) (N + 1)]
    · rw [sum_cons]
      have hiff : ∀ (s : Bool) (σ : Fin N → Bool),
          (∃ k ≤ N + 1, a ≤ |x + psum (Fin.cons s σ : Fin (N + 1) → Bool) k|) ↔
            (∃ k ≤ N, a ≤ |(x + sgn s) + psum σ k|) := by
        intro s σ
        constructor
        · rintro ⟨k, hk, hak⟩
          cases k with
          | zero => exact absurd (by simpa using hak) hx
          | succ k =>
            refine ⟨k, by omega, ?_⟩
            rw [psum_cons_succ] at hak
            simpa [add_assoc] using hak
        · rintro ⟨k, hk, hak⟩
          refine ⟨k + 1, by omega, ?_⟩
          rw [psum_cons_succ]
          simpa [add_assoc] using hak
      have hrw : ∀ (s : Bool) (σ : Fin N → Bool),
          ((x + psum (Fin.cons s σ : Fin (N + 1) → Bool) (N + 1)) ^ 2 -
            a ^ 2 * (if ∃ k ≤ N + 1,
              a ≤ |x + psum (Fin.cons s σ : Fin (N + 1) → Bool) k| then 1 else 0)) =
          (((x + sgn s) + psum σ N) ^ 2 -
            a ^ 2 * (if ∃ k ≤ N, a ≤ |(x + sgn s) + psum σ k| then 1 else 0)) := by
        intro s σ
        rw [psum_cons_succ, if_congr (hiff s σ) rfl rfl, add_assoc]
      simp only [hrw]
      exact sum_nonneg (fun s _ => ih (x + sgn s))

 
theorem kolmogorov (a : ℤ) (ha : 0 ≤ a) (N : ℕ) :
    a ^ 2 * ((univ.filter fun σ : Fin N → Bool => ∃ k ≤ N, a ≤ |psum σ k|).card : ℤ) ≤
      2 ^ N * N := by
  classical
  have h := kolmogorov_aux a ha N 0
  simp only [zero_add] at h
  rw [sum_sub_distrib, ← mul_sum, sum_boole] at h
  have h2 := sum_sq_psum N 0
  simp only [zero_add] at h2
  rw [h2] at h
  simpa using h

 
theorem card_filter_cons (N : ℕ) (P : (Fin (N + 1) → Bool) → Prop) [DecidablePred P] :
    (univ.filter P).card = (univ.filter fun σ : Fin N → Bool => P (Fin.cons true σ)).card +
      (univ.filter fun σ : Fin N → Bool => P (Fin.cons false σ)).card := by
  classical
  rw [card_eq_sum_ones, sum_filter, sum_cons, Fintype.sum_bool, ← sum_filter, ← sum_filter,
    ← card_eq_sum_ones, ← card_eq_sum_ones]

 
theorem card_psum_eq (N k : ℕ) :
    ((univ.filter fun σ : Fin N → Bool => psum σ N = 2 * (k : ℤ) - N).card) =
      N.choose k := by
  classical
  induction N generalizing k with
  | zero =>
    cases k with
    | zero => simp
    | succ k =>
      simp only [Nat.choose_zero_succ, card_eq_zero, filter_eq_empty_iff]
      intro σ _
      simp
      omega
  | succ N ih =>
    rw [card_filter_cons]
    simp only [psum_cons_succ, sgn_true, sgn_false]
    cases k with
    | zero =>
      have h0 : (univ.filter fun σ : Fin N → Bool =>
          1 + psum σ N = 2 * ((0 : ℕ) : ℤ) - ((N + 1 : ℕ) : ℤ)) = ∅ := by
        apply filter_eq_empty_iff.mpr
        intro σ _
        have := abs_psum_le σ N
        push_cast
        intro h
        rw [abs_le] at this
        omega
      have h1 : (univ.filter fun σ : Fin N → Bool =>
          -1 + psum σ N = 2 * ((0 : ℕ) : ℤ) - ((N + 1 : ℕ) : ℤ)) =
          (univ.filter fun σ : Fin N → Bool => psum σ N = 2 * ((0 : ℕ) : ℤ) - N) := by
        apply filter_congr
        intro σ _
        push_cast
        constructor <;> intro h <;> omega
      rw [h0, h1, ih 0]
      simp
    | succ k =>
      have h0 : (univ.filter fun σ : Fin N → Bool =>
          1 + psum σ N = 2 * ((k + 1 : ℕ) : ℤ) - ((N + 1 : ℕ) : ℤ)) =
          (univ.filter fun σ : Fin N → Bool => psum σ N = 2 * (k : ℤ) - N) := by
        apply filter_congr
        intro σ _
        push_cast
        constructor <;> intro h <;> omega
      have h1 : (univ.filter fun σ : Fin N → Bool =>
          -1 + psum σ N = 2 * ((k + 1 : ℕ) : ℤ) - ((N + 1 : ℕ) : ℤ)) =
          (univ.filter fun σ : Fin N → Bool => psum σ N = 2 * ((k + 1 : ℕ) : ℤ) - N) := by
        apply filter_congr
        intro σ _
        push_cast
        constructor <;> intro h <;> omega
      rw [h0, h1, ih k, ih (k + 1), Nat.choose_succ_succ', add_comm]

 

theorem card_psum_eq_le_middle (N : ℕ) (v : ℤ) :
    ((univ.filter fun σ : Fin N → Bool => psum σ N = v).card) ≤ N.choose (N / 2) := by
  classical
  by_cases hv : ∃ k : ℕ, v = 2 * (k : ℤ) - N
  · obtain ⟨k, rfl⟩ := hv
    rw [card_psum_eq]
    exact Nat.choose_le_middle k N
  · have : (univ.filter fun σ : Fin N → Bool => psum σ N = v) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro σ _ h
      obtain ⟨j, _, hj⟩ := psum_parity σ N
      exact hv ⟨j, by rw [← h, hj]⟩
    rw [this]
    simp

end SupercriticalLQGUniqueness.B2.QPos.P3
