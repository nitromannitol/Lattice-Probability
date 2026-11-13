/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P3Local1D at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P3Walk1D

 








set_option autoImplicit false
noncomputable section

open Finset

namespace SupercriticalLQGUniqueness.B2.QPos.P3

theorem choose_step (M l : ℕ) (hl : l ≤ M) :
    ((2 * M).choose (M + l + 1) : ℝ) * ((M + l + 1 : ℕ) : ℝ) =
      ((2 * M).choose (M + l) : ℝ) * ((M - l : ℕ) : ℝ) := by
  have h := Nat.choose_succ_right_eq (2 * M) (M + l)
  have h2 : 2 * M - (M + l) = M - l := by omega
  rw [h2] at h
  exact_mod_cast h

 
theorem choose_middle_ratio (M i : ℕ) (hi : i ≤ M) :
    ((2 * M).choose M : ℝ) * (1 - 2 * (i : ℝ) ^ 2 / ((M : ℝ) + i)) ≤
      ((2 * M).choose (M + i) : ℝ) := by
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · simp
  have hMi : (0 : ℝ) < (M : ℝ) + i := by positivity
  set ρ : ℝ := 1 - 2 * (i : ℝ) / ((M : ℝ) + i) with hρ
  have hρ0 : 0 ≤ ρ := by
    rw [hρ, sub_nonneg, div_le_one hMi]
    have : (i : ℝ) ≤ M := by exact_mod_cast hi
    linarith
  have hstep : ∀ l : ℕ, l < i →
      ((2 * M).choose (M + l) : ℝ) * ρ ≤ ((2 * M).choose (M + l + 1) : ℝ) := by
    intro l hl
    have hc := choose_step M l (by omega)
    have hpos : (0 : ℝ) < ((M + l + 1 : ℕ) : ℝ) := by positivity
    have hle : ρ * ((M + l + 1 : ℕ) : ℝ) ≤ ((M - l : ℕ) : ℝ) := by
      have hρ' : ρ = ((M : ℝ) - i) / ((M : ℝ) + i) := by
        rw [hρ]; field_simp; ring
      have hml : ((M - l : ℕ) : ℝ) = (M : ℝ) - l := by
        rw [Nat.cast_sub (by omega)]
      rw [hρ', hml, div_mul_eq_mul_div, div_le_iff₀ hMi]
      push_cast
      have hl' : (l : ℝ) + 1 ≤ i := by exact_mod_cast hl
      have hM0 : (0 : ℝ) ≤ M := by positivity
      have hprod : (0 : ℝ) ≤ (M : ℝ) * (2 * i - 2 * l - 1) :=
        mul_nonneg hM0 (by linarith)
      nlinarith
    have hC : (0 : ℝ) ≤ ((2 * M).choose (M + l) : ℝ) := by positivity
    calc ((2 * M).choose (M + l) : ℝ) * ρ
        = ((2 * M).choose (M + l) : ℝ) * (ρ * ((M + l + 1 : ℕ) : ℝ)) /
            ((M + l + 1 : ℕ) : ℝ) := by field_simp
      _ ≤ ((2 * M).choose (M + l) : ℝ) * ((M - l : ℕ) : ℝ) / ((M + l + 1 : ℕ) : ℝ) := by
          apply div_le_div_of_nonneg_right _ hpos.le
          exact mul_le_mul_of_nonneg_left hle hC
      _ = ((2 * M).choose (M + l + 1) : ℝ) := by
          rw [← hc]; field_simp
  have hind : ∀ l : ℕ, l ≤ i →
      ((2 * M).choose M : ℝ) * ρ ^ l ≤ ((2 * M).choose (M + l) : ℝ) := by
    intro l
    induction l with
    | zero => intro _; simp
    | succ l ih =>
      intro hl
      calc ((2 * M).choose M : ℝ) * ρ ^ (l + 1)
          = ((2 * M).choose M : ℝ) * ρ ^ l * ρ := by ring
        _ ≤ ((2 * M).choose (M + l) : ℝ) * ρ :=
            mul_le_mul_of_nonneg_right (ih (by omega)) hρ0
        _ ≤ ((2 * M).choose (M + l + 1) : ℝ) := hstep l (by omega)
        _ = ((2 * M).choose (M + (l + 1)) : ℝ) := by rw [add_assoc]
  have hbern : 1 - 2 * (i : ℝ) ^ 2 / ((M : ℝ) + i) ≤ ρ ^ i := by
    have h := one_add_mul_le_pow (a := -(2 * (i : ℝ) / ((M : ℝ) + i))) ?_ i
    · have : ρ = 1 + -(2 * (i : ℝ) / ((M : ℝ) + i)) := by rw [hρ]; ring
      rw [this]
      calc 1 - 2 * (i : ℝ) ^ 2 / ((M : ℝ) + i)
          = 1 + (i : ℝ) * -(2 * (i : ℝ) / ((M : ℝ) + i)) := by ring
        _ ≤ _ := h
    · have : 2 * (i : ℝ) / ((M : ℝ) + i) ≤ 2 := by
        rw [div_le_iff₀ hMi]
        have : (0 : ℝ) ≤ M := by positivity
        linarith
      linarith
  have hC0 : (0 : ℝ) ≤ ((2 * M).choose M : ℝ) := by positivity
  calc ((2 * M).choose M : ℝ) * (1 - 2 * (i : ℝ) ^ 2 / ((M : ℝ) + i))
      ≤ ((2 * M).choose M : ℝ) * ρ ^ i := mul_le_mul_of_nonneg_left hbern hC0
    _ ≤ _ := hind i le_rfl

 
theorem card_abs_psum_ge (N : ℕ) (a : ℤ) (ha : 0 < a) :
    a ^ 2 * ((univ.filter fun σ : Fin N → Bool => a ≤ |psum σ N|).card : ℤ) ≤ 2 ^ N * N := by
  classical
  have h2 : ∑ σ : Fin N → Bool, psum σ N ^ 2 = 2 ^ N * N := by
    have := sum_sq_psum N 0; simpa using this
  rw [← h2, ← sum_boole, mul_sum]
  apply sum_le_sum
  intro σ _
  split_ifs with h
  · have : a ^ 2 ≤ psum σ N ^ 2 := by
      nlinarith [abs_nonneg (psum σ N), sq_abs (psum σ N)]
    linarith
  · simp only [mul_zero]; positivity

 

theorem central_choose_lower (s : ℕ) (hs : 0 < s) (M : ℕ) (hM : 2 * M = s ^ 2) :
    (3 / 4 : ℝ) * 2 ^ (2 * M) ≤ (4 * (s : ℝ) + 1) * ((2 * M).choose M : ℝ) := by
  classical
  set t := 2 * M with ht
  
  have hfar := card_abs_psum_ge t (2 * s + 1) (by positivity)
  have hfarR : ((univ.filter fun σ : Fin t → Bool => (2 * (s : ℤ) + 1) ≤ |psum σ t|).card : ℝ)
      ≤ 2 ^ t / 4 := by
    have h1 : ((2 * (s : ℤ) + 1) ^ 2 : ℝ) *
        ((univ.filter fun σ : Fin t → Bool => (2 * (s : ℤ) + 1) ≤ |psum σ t|).card : ℝ)
        ≤ 2 ^ t * (t : ℝ) := by exact_mod_cast hfar
    have htR : (t : ℝ) = (s : ℝ) ^ 2 := by rw [ht]; exact_mod_cast hM
    rw [htR] at h1
    have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
    have hpos : (0 : ℝ) ≤ 2 ^ t := by positivity
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
    have hc0 : (0 : ℝ) ≤
        ((univ.filter fun σ : Fin t → Bool => (2 * (s : ℤ) + 1) ≤ |psum σ t|).card : ℝ) := by
      positivity
    push_cast at h1
    nlinarith
  
  have hnear : ((univ.filter fun σ : Fin t → Bool => |psum σ t| ≤ 2 * (s : ℤ)).card : ℝ) ≤
      (4 * (s : ℝ) + 1) * (t.choose (t / 2) : ℝ) := by
    have hfib : (univ.filter fun σ : Fin t → Bool => |psum σ t| ≤ 2 * (s : ℤ)).card =
        ∑ v ∈ Icc (-(2 * (s : ℤ))) (2 * s),
          ((univ.filter fun σ : Fin t → Bool => |psum σ t| ≤ 2 * (s : ℤ)).filter
            fun σ => psum σ t = v).card := by
      apply card_eq_sum_card_fiberwise
      intro σ hσ
      simp only [coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hσ
      simp only [coe_Icc, Set.mem_Icc]
      exact abs_le.mp hσ
    have hle : ∀ v ∈ Icc (-(2 * (s : ℤ))) (2 * s),
        ((univ.filter fun σ : Fin t → Bool => |psum σ t| ≤ 2 * (s : ℤ)).filter
            fun σ => psum σ t = v).card ≤ t.choose (t / 2) := by
      intro v _
      calc _ ≤ (univ.filter fun σ : Fin t → Bool => psum σ t = v).card := by
            apply card_le_card
            intro σ
            simp
        _ ≤ _ := card_psum_eq_le_middle t v
    have hcard : (Icc (-(2 * (s : ℤ))) (2 * s)).card = 4 * s + 1 := by
      simp only [Int.card_Icc]
      omega
    have := sum_le_sum hle
    rw [sum_const, hcard, smul_eq_mul] at this
    rw [hfib]
    exact_mod_cast this
  have htot : ((univ.filter fun σ : Fin t → Bool => |psum σ t| ≤ 2 * (s : ℤ)).card : ℝ) +
      ((univ.filter fun σ : Fin t → Bool => (2 * (s : ℤ) + 1) ≤ |psum σ t|).card : ℝ) =
        2 ^ t := by
    have : (univ.filter fun σ : Fin t → Bool => (2 * (s : ℤ) + 1) ≤ |psum σ t|) =
        univ.filter fun σ : Fin t → Bool => ¬ (|psum σ t| ≤ 2 * (s : ℤ)) := by
      apply filter_congr; intro σ _; constructor <;> intro h <;> omega
    rw [this]
    have h := card_filter_add_card_filter_not
      (s := (univ : Finset (Fin t → Bool))) (fun σ => |psum σ t| ≤ 2 * (s : ℤ))
    rw [card_univ, card_fun_bool] at h
    exact_mod_cast h
  have hmid : t / 2 = M := by omega
  rw [hmid] at hnear
  linarith

 

theorem card_psum_even_lower (M : ℕ) (i : ℤ) (hi : 8 * i ^ 2 ≤ M) :
    (3 / 4 : ℝ) * ((2 * M).choose M : ℝ) ≤
      ((univ.filter fun σ : Fin (2 * M) → Bool => psum σ (2 * M) = 2 * i).card : ℝ) := by
  classical
  have hiM : i.natAbs ≤ M := by
    have : (i.natAbs : ℤ) ^ 2 ≤ M := by
      rw [Int.natAbs_sq]; nlinarith
    have h2 : (i.natAbs : ℤ) ≤ (i.natAbs : ℤ) ^ 2 := by
      rcases Nat.eq_zero_or_pos i.natAbs with h | h
      · rw [h]; simp
      · nlinarith
    omega
  
  have hcount : ((univ.filter fun σ : Fin (2 * M) → Bool => psum σ (2 * M) = 2 * i).card) =
      (2 * M).choose (M + i.natAbs) := by
    rcases le_or_gt 0 i with h0 | h0
    · have hk := card_psum_eq (2 * M) (M + i.natAbs)
      have : (2 * ((M + i.natAbs : ℕ) : ℤ) - ((2 * M : ℕ) : ℤ)) = 2 * i := by
        push_cast; rw [abs_of_nonneg h0]; ring
      rw [this] at hk
      exact hk
    · have hk := card_psum_eq (2 * M) (M - i.natAbs)
      have : (2 * ((M - i.natAbs : ℕ) : ℤ) - ((2 * M : ℕ) : ℤ)) = 2 * i := by
        rw [Nat.cast_sub hiM]; push_cast; rw [abs_of_neg h0]; ring
      rw [this] at hk
      rw [hk]
      exact Nat.choose_symm_of_eq_add (by omega)
  rw [hcount]
  have hr := choose_middle_ratio M i.natAbs hiM
  have hbound : 2 * ((i.natAbs : ℕ) : ℝ) ^ 2 / ((M : ℝ) + i.natAbs) ≤ 1 / 4 := by
    rcases Nat.eq_zero_or_pos M with hM0 | hMpos
    · have : i.natAbs = 0 := by omega
      rw [this]; norm_num
    have hden : (0 : ℝ) < (M : ℝ) + i.natAbs := by positivity
    rw [div_le_iff₀ hden]
    have hsq : ((i.natAbs : ℕ) : ℝ) ^ 2 = (i : ℝ) ^ 2 := by
      rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
    rw [hsq]
    have hiR : 8 * (i : ℝ) ^ 2 ≤ M := by exact_mod_cast hi
    have : (0 : ℝ) ≤ i.natAbs := by positivity
    nlinarith
  have hC0 : (0 : ℝ) ≤ ((2 * M).choose M : ℝ) := by positivity
  calc (3 / 4 : ℝ) * ((2 * M).choose M : ℝ)
      ≤ ((2 * M).choose M : ℝ) * (1 - 2 * ((i.natAbs : ℕ) : ℝ) ^ 2 / ((M : ℝ) + i.natAbs)) := by
        nlinarith
    _ ≤ _ := hr

 

theorem card_window_lower (j : ℕ) (hj : 0 < j) (c : ℤ) (hc : |c| ≤ 2 * j) :
    (9 / 528 : ℝ) * 2 ^ (64 * j ^ 2) ≤
      ((univ.filter fun σ : Fin (64 * j ^ 2) → Bool =>
        |psum σ (64 * j ^ 2) - c| ≤ j).card : ℝ) := by
  classical
  set M := 32 * j ^ 2 with hM
  have ht : 64 * j ^ 2 = 2 * M := by rw [hM]; ring
  have hcent := central_choose_lower (8 * j) (by positivity) M (by rw [hM]; ring)
  set i₀ : ℤ := (c - j + 1) / 2 with hi₀
  have hi₀lo : c - j ≤ 2 * i₀ := by omega
  have hi₀hi : 2 * i₀ ≤ c - j + 1 := by omega
  
  have hsub : (Ico i₀ (i₀ + j)).biUnion (fun i =>
      univ.filter fun σ : Fin (64 * j ^ 2) → Bool => psum σ (64 * j ^ 2) = 2 * i) ⊆
      univ.filter fun σ : Fin (64 * j ^ 2) → Bool => |psum σ (64 * j ^ 2) - c| ≤ j := by
    intro σ hσ
    simp only [mem_biUnion, mem_Ico, mem_filter, mem_univ, true_and] at hσ ⊢
    obtain ⟨i, ⟨h1, h2⟩, h3⟩ := hσ
    rw [h3, abs_le]
    constructor <;> omega
  have hdisj : Set.PairwiseDisjoint (↑(Ico i₀ (i₀ + j))) (fun i =>
      univ.filter fun σ : Fin (64 * j ^ 2) → Bool => psum σ (64 * j ^ 2) = 2 * i) := by
    intro a _ b _ hab
    simp only [Function.onFun]
    rw [disjoint_filter]
    intro σ _ h1 h2
    apply hab
    omega
  have hcard := card_le_card hsub
  rw [card_biUnion hdisj] at hcard
  have hterm : ∀ i ∈ Ico i₀ (i₀ + j), (3 / 4 : ℝ) * ((2 * M).choose M : ℝ) ≤
      ((univ.filter fun σ : Fin (64 * j ^ 2) → Bool => psum σ (64 * j ^ 2) = 2 * i).card : ℝ) := by
    intro i hi
    simp only [mem_Ico] at hi
    have hab : |i| ≤ 2 * j := by rw [abs_le] at hc ⊢; constructor <;> omega
    have hi8 : 8 * i ^ 2 ≤ (M : ℤ) := by
      rw [hM]; push_cast
      have : i ^ 2 ≤ (2 * (j : ℤ)) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg i) hab 2
      nlinarith
    have := card_psum_even_lower M i hi8
    rw [ht]
    exact this
  have hsum : ((Ico i₀ (i₀ + j)).card : ℝ) * ((3 / 4 : ℝ) * ((2 * M).choose M : ℝ)) ≤
      ((univ.filter fun σ : Fin (64 * j ^ 2) → Bool => |psum σ (64 * j ^ 2) - c| ≤ j).card : ℝ) := by
    calc ((Ico i₀ (i₀ + j)).card : ℝ) * ((3 / 4 : ℝ) * ((2 * M).choose M : ℝ))
        = ∑ i ∈ Ico i₀ (i₀ + j), (3 / 4 : ℝ) * ((2 * M).choose M : ℝ) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ Ico i₀ (i₀ + j),
          ((univ.filter fun σ : Fin (64 * j ^ 2) → Bool => psum σ (64 * j ^ 2) = 2 * i).card : ℝ) :=
          sum_le_sum hterm
      _ ≤ _ := by exact_mod_cast hcard
  have hIco : ((Ico i₀ (i₀ + j)).card : ℝ) = j := by
    simp only [Int.card_Ico]
    have : i₀ + j - i₀ = (j : ℤ) := by ring
    rw [this]; simp
  rw [hIco] at hsum
  have h2M : (2 : ℝ) ^ (64 * j ^ 2) = 2 ^ (2 * M) := by rw [ht]
  rw [h2M]
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have h2t : (0 : ℝ) < 2 ^ (2 * M) := by positivity
  have hC : (0 : ℝ) ≤ ((2 * M).choose M : ℝ) := by positivity
  push_cast at hcent
  
  have hden : (0 : ℝ) < 4 * (8 * (j : ℝ)) + 1 := by positivity
  have hC' : (3 / 4 : ℝ) * 2 ^ (2 * M) / (4 * (8 * (j : ℝ)) + 1) ≤
      ((2 * M).choose M : ℝ) := by
    rw [div_le_iff₀ hden]; linarith
  have hfin : (9 / 528 : ℝ) * 2 ^ (2 * M) ≤
      (j : ℝ) * ((3 / 4 : ℝ) * ((3 / 4 : ℝ) * 2 ^ (2 * M) / (4 * (8 * (j : ℝ)) + 1))) := by
    rw [mul_div_assoc', mul_div_assoc', le_div_iff₀ hden]
    nlinarith
  calc (9 / 528 : ℝ) * 2 ^ (2 * M) ≤ _ := hfin
    _ ≤ (j : ℝ) * ((3 / 4 : ℝ) * ((2 * M).choose M : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hC' (by norm_num)
    _ ≤ _ := hsum

 
theorem block1D (j : ℕ) (hj : 0 < j) (x d : ℤ) (hx : |x| ≤ j) (hd : |d| ≤ j) :
    (1 / 128 : ℝ) * 2 ^ (64 * j ^ 2) ≤
      ((univ.filter fun σ : Fin (64 * j ^ 2) → Bool =>
        |x + psum σ (64 * j ^ 2) - d| ≤ j ∧
          ∀ k ≤ 64 * j ^ 2, |psum σ k| < 128 * j).card : ℝ) := by
  classical
  set t := 64 * j ^ 2 with ht
  have hc : |d - x| ≤ 2 * j := by
    rw [abs_le] at hx hd ⊢; constructor <;> omega
  have hwin := card_window_lower j hj (d - x) hc
  have hkol := kolmogorov (128 * j) (by positivity) t
  have hkolR : ((univ.filter fun σ : Fin t → Bool => ∃ k ≤ t, (128 * (j : ℤ)) ≤ |psum σ k|).card : ℝ)
      ≤ 2 ^ t / 256 := by
    have h1 : ((128 * (j : ℤ)) ^ 2 : ℝ) *
        ((univ.filter fun σ : Fin t → Bool => ∃ k ≤ t, (128 * (j : ℤ)) ≤ |psum σ k|).card : ℝ)
        ≤ 2 ^ t * (t : ℝ) := by exact_mod_cast hkol
    rw [ht] at h1
    push_cast at h1
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 256)]
    have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
    have hj2 : (0 : ℝ) < (j : ℝ) ^ 2 := by positivity
    have hc0 : (0 : ℝ) ≤
        ((univ.filter fun σ : Fin t → Bool => ∃ k ≤ t, (128 * (j : ℤ)) ≤ |psum σ k|).card : ℝ) := by
      positivity
    have : (128 * (j : ℝ)) ^ 2 = 16384 * (j : ℝ) ^ 2 := by ring
    rw [this] at h1
    nlinarith
  have hsplit : (univ.filter fun σ : Fin t → Bool => |psum σ t - (d - x)| ≤ j) ⊆
      (univ.filter fun σ : Fin t → Bool =>
        |x + psum σ t - d| ≤ j ∧ ∀ k ≤ t, |psum σ k| < 128 * j) ∪
      (univ.filter fun σ : Fin t → Bool => ∃ k ≤ t, (128 * (j : ℤ)) ≤ |psum σ k|) := by
    intro σ hσ
    simp only [mem_filter, mem_univ, true_and, mem_union] at hσ ⊢
    by_cases h : ∃ k ≤ t, (128 * (j : ℤ)) ≤ |psum σ k|
    · exact Or.inr h
    · left
      refine ⟨by rw [abs_le] at hσ ⊢; constructor <;> omega, ?_⟩
      intro k hk
      by_contra hcon
      exact h ⟨k, hk, by omega⟩
  have hc1 := card_le_card hsplit
  have hc2 := card_union_le
    (univ.filter fun σ : Fin t → Bool =>
        |x + psum σ t - d| ≤ j ∧ ∀ k ≤ t, |psum σ k| < 128 * j)
    (univ.filter fun σ : Fin t → Bool => ∃ k ≤ t, (128 * (j : ℤ)) ≤ |psum σ k|)
  have hc3 : ((univ.filter fun σ : Fin t → Bool => |psum σ t - (d - x)| ≤ j).card : ℝ) ≤
      ((univ.filter fun σ : Fin t → Bool =>
        |x + psum σ t - d| ≤ j ∧ ∀ k ≤ t, |psum σ k| < 128 * j).card : ℝ) +
      ((univ.filter fun σ : Fin t → Bool => ∃ k ≤ t, (128 * (j : ℤ)) ≤ |psum σ k|).card : ℝ) := by
    exact_mod_cast hc1.trans hc2
  have h2t : (0 : ℝ) ≤ 2 ^ t := by positivity
  linarith

end SupercriticalLQGUniqueness.B2.QPos.P3
