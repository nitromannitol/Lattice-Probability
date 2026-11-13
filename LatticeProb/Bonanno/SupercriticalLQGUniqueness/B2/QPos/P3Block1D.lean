/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P3Block1D at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P3Local1D

 








set_option autoImplicit false
noncomputable section

open Finset

namespace SupercriticalLQGUniqueness.B2.QPos.P3

 
theorem card_filter_append (a b : ℕ) (P : (Fin (a + b) → Bool) → Prop) [DecidablePred P] :
    ((univ.filter P).card : ℝ) =
      ∑ σ : Fin a → Bool, ((univ.filter fun τ : Fin b → Bool => P (Fin.append σ τ)).card : ℝ) := by
  classical
  have h : (univ.filter P).card =
      ∑ σ : Fin a → Bool, (univ.filter fun τ : Fin b → Bool => P (Fin.append σ τ)).card := by
    rw [card_eq_sum_ones, sum_filter, sum_append]
    apply sum_congr rfl
    intro σ _
    rw [card_eq_sum_ones, sum_filter]
  rw [h]
  push_cast
  rfl

 
def BlockGood (j t : ℕ) (a : ℕ → ℤ) (x₀ : ℤ) (m : ℕ) (σ : Fin (t * m) → Bool) : Prop :=
  ∀ i < m, |x₀ + psum σ (t * (i + 1)) - a (i + 1)| ≤ j ∧
    ∀ k ≤ t, |psum σ (t * i + k) - psum σ (t * i)| < 128 * j

theorem blockGood_append (j t : ℕ) (a : ℕ → ℤ) (x₀ : ℤ) (m : ℕ)
    (σ : Fin (t * m) → Bool) (τ : Fin t → Bool) (hσ : BlockGood j t a x₀ m σ)
    (hτ : |(x₀ + psum σ (t * m) - a m) + psum τ t - (a (m + 1) - a m)| ≤ j ∧
      ∀ k ≤ t, |psum τ k| < 128 * j) :
    BlockGood j t a x₀ (m + 1) (Fin.append σ τ : Fin (t * m + t) → Bool) := by
  intro i hi
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · obtain ⟨h1, h2⟩ := hσ i hi
    have hle : t * (i + 1) ≤ t * m := Nat.mul_le_mul_left t (by omega)
    refine ⟨?_, ?_⟩
    · rw [psum_append_of_le σ τ hle]; exact h1
    · intro k hk
      have hk1 : t * i + k ≤ t * m := by
        calc t * i + k ≤ t * i + t := by omega
          _ = t * (i + 1) := by ring
          _ ≤ t * m := hle
      have hk2 : t * i ≤ t * m := le_trans (Nat.le_add_right _ _) hk1
      rw [psum_append_of_le σ τ hk1, psum_append_of_le σ τ hk2]
      exact h2 k hk
  · refine ⟨?_, ?_⟩
    · show |x₀ + psum (Fin.append σ τ) (t * i + t) - a (i + 1)| ≤ j
      rw [psum_append_add]
      have h := hτ.1
      have e : x₀ + (psum σ (t * i) + psum τ t) - a (i + 1) =
          (x₀ + psum σ (t * i) - a i) + psum τ t - (a (i + 1) - a i) := by ring
      rw [e]; exact h
    · intro k hk
      rw [psum_append_add, psum_append_of_le σ τ le_rfl]
      have := hτ.2 k hk
      simpa using this

open Classical in
 
theorem multiBlock (j : ℕ) (hj : 0 < j) (a : ℕ → ℤ) (m : ℕ)
    (ha : ∀ i < m, |a (i + 1) - a i| ≤ j) (x₀ : ℤ) (hx₀ : |x₀ - a 0| ≤ j) :
    ((1 / 128 : ℝ) * 2 ^ (64 * j ^ 2)) ^ m ≤
      ((univ.filter fun σ : Fin (64 * j ^ 2 * m) → Bool =>
        BlockGood j (64 * j ^ 2) a x₀ m σ).card : ℝ) := by
  classical
  set t := 64 * j ^ 2 with ht
  induction m with
  | zero =>
    simp only [pow_zero]
    have : (univ.filter fun σ : Fin (t * 0) → Bool => BlockGood j t a x₀ 0 σ) = univ := by
      apply filter_true_of_mem
      intro σ _ i hi
      exact absurd hi (Nat.not_lt_zero _)
    rw [this, card_univ]
    simp
  | succ m ih =>
    have ih' := ih (fun i hi => ha i (by omega))
    have hsplit := card_filter_append (t * m) t
      (fun σ' => BlockGood j t a x₀ (m + 1) σ')
    refine le_of_le_of_eq ?_ hsplit.symm
    
    have hfib : ∀ σ : Fin (t * m) → Bool,
        (if BlockGood j t a x₀ m σ then (1 / 128 : ℝ) * 2 ^ t else 0) ≤
          ((univ.filter fun τ : Fin t → Bool =>
            BlockGood j t a x₀ (m + 1) (Fin.append σ τ)).card : ℝ) := by
      intro σ
      split_ifs with hσ
      · have hx : |x₀ + psum σ (t * m) - a m| ≤ j := by
          rcases m with _ | m
          · simpa using hx₀
          · have := (hσ m (by omega)).1
            exact this
        have hd : |a (m + 1) - a m| ≤ j := ha m (by omega)
        have hb := block1D j hj (x₀ + psum σ (t * m) - a m) (a (m + 1) - a m) hx hd
        calc (1 / 128 : ℝ) * 2 ^ t ≤ _ := hb
          _ ≤ _ := by
            exact_mod_cast card_le_card (by
              intro τ hτ
              simp only [mem_filter, mem_univ, true_and] at hτ ⊢
              exact blockGood_append j t a x₀ m σ τ hσ hτ)
      · positivity
    calc ((1 / 128 : ℝ) * 2 ^ t) ^ (m + 1)
        = ((1 / 128 : ℝ) * 2 ^ t) ^ m * ((1 / 128 : ℝ) * 2 ^ t) := pow_succ _ _
      _ ≤ ((univ.filter fun σ : Fin (t * m) → Bool =>
            BlockGood j t a x₀ m σ).card : ℝ) * ((1 / 128 : ℝ) * 2 ^ t) :=
          mul_le_mul_of_nonneg_right ih' (by positivity)
      _ = ∑ σ : Fin (t * m) → Bool,
            (if BlockGood j t a x₀ m σ then (1 / 128 : ℝ) * 2 ^ t else 0) := by
          rw [← sum_filter, sum_const, nsmul_eq_mul]
      _ ≤ _ := sum_le_sum (fun σ _ => hfib σ)

end SupercriticalLQGUniqueness.B2.QPos.P3
