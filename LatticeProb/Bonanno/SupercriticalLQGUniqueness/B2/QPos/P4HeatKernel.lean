/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P4HeatKernel at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P4Green

 
















set_option autoImplicit false
noncomputable section

open Finset

namespace SupercriticalLQGUniqueness.B2.QPos.P4

open P3

 

 
theorem centralBinom_sq_le (n : ℕ) : (n.centralBinom) ^ 2 * (2 * n + 1) ≤ 16 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hrec := Nat.succ_mul_centralBinom_succ n
    have key : ((n + 1).centralBinom) ^ 2 * (2 * (n + 1) + 1) * (n + 1) ^ 2 ≤
        16 ^ (n + 1) * (n + 1) ^ 2 := by
      have h1 : ((n + 1).centralBinom) ^ 2 * (2 * (n + 1) + 1) * (n + 1) ^ 2 =
          4 * (2 * n + 1) * (2 * n + 3) * ((n.centralBinom) ^ 2 * (2 * n + 1)) := by
        have : ((n + 1) * (n + 1).centralBinom) ^ 2 =
            (2 * (2 * n + 1) * n.centralBinom) ^ 2 := by rw [hrec]
        nlinarith [this]
      rw [h1, pow_succ]
      have h2 : 4 * (2 * n + 1) * (2 * n + 3) ≤ 16 * (n + 1) ^ 2 := by nlinarith
      calc 4 * (2 * n + 1) * (2 * n + 3) * (n.centralBinom ^ 2 * (2 * n + 1))
          ≤ 4 * (2 * n + 1) * (2 * n + 3) * 16 ^ n := Nat.mul_le_mul_left _ ih
        _ ≤ 16 * (n + 1) ^ 2 * 16 ^ n := Nat.mul_le_mul_right _ h2
        _ = 16 ^ n * 16 * (n + 1) ^ 2 := by ring
    exact Nat.le_of_mul_le_mul_right key (by positivity)

 
theorem choose_half_sq_le (t : ℕ) : (t.choose (t / 2)) ^ 2 * (t + 1) ≤ 4 ^ t := by
  rcases Nat.even_or_odd' t with ⟨M, rfl | rfl⟩
  · have h : 2 * M / 2 = M := by omega
    rw [h, ← Nat.centralBinom_eq_two_mul_choose]
    have := centralBinom_sq_le M
    calc M.centralBinom ^ 2 * (2 * M + 1) ≤ 16 ^ M := this
      _ = 4 ^ (2 * M) := by rw [pow_mul]; norm_num
  · have h : (2 * M + 1) / 2 = M := by omega
    rw [h]
    have hcb : (M + 1).centralBinom = 2 * (2 * M + 1).choose M := by
      rw [Nat.centralBinom_eq_two_mul_choose]
      have : 2 * (M + 1) = (2 * M + 1) + 1 := by ring
      rw [this, Nat.choose_succ_succ, Nat.choose_symm_half]
      ring
    have hw := centralBinom_sq_le (M + 1)
    rw [hcb] at hw
    have : 4 * (((2 * M + 1).choose M) ^ 2 * (2 * M + 1 + 1)) ≤ 4 * 4 ^ (2 * M + 1) := by
      calc 4 * (((2 * M + 1).choose M) ^ 2 * (2 * M + 1 + 1))
          ≤ (2 * (2 * M + 1).choose M) ^ 2 * (2 * (M + 1) + 1) := by nlinarith
        _ ≤ 16 ^ (M + 1) := hw
        _ = 4 * 4 ^ (2 * M + 1) := by
          rw [show (16 : ℕ) = 4 ^ 2 by norm_num, ← pow_mul]; ring
    omega

 

 
def cnt (t : ℕ) (m : ℤ) : ℕ := (univ.filter fun σ : Fin t → Bool => psum σ t = m).card

 
def cmax (t : ℕ) : ℕ := t.choose (t / 2)

theorem cnt_le_cmax (t : ℕ) (m : ℤ) : cnt t m ≤ cmax t := card_psum_eq_le_middle t m

theorem cmax_sq_le (t : ℕ) : ((cmax t : ℝ) / 2 ^ t) ^ 2 * (t + 1) ≤ 1 := by
  have h := choose_half_sq_le t
  have h' : ((cmax t : ℝ)) ^ 2 * (t + 1) ≤ (4 : ℝ) ^ t := by
    unfold cmax; exact_mod_cast h
  have h4 : (4 : ℝ) ^ t = ((2 : ℝ) ^ t) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [div_pow]
  have hpos : (0 : ℝ) < ((2 : ℝ) ^ t) ^ 2 := by positivity
  rw [div_mul_eq_mul_div, div_le_one hpos]
  linarith

theorem cmax_nonneg (t : ℕ) : (0 : ℝ) ≤ (cmax t : ℝ) / 2 ^ t := by positivity

 
theorem card_abs_psum_ge_le (t : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    ((univ.filter fun σ : Fin t → Bool => r ≤ |(psum σ t : ℝ)|).card : ℝ) * r ^ 2 ≤
      2 ^ t * t := by
  have h2 := sum_sq_psum t 0
  have h2z : ∑ σ : Fin t → Bool, psum σ t ^ 2 = 2 ^ t * (t : ℤ) := by simpa using h2
  have h2' : ∑ σ : Fin t → Bool, ((psum σ t : ℝ)) ^ 2 = 2 ^ t * t := by exact_mod_cast h2z
  rw [← h2', ← Finset.sum_boole, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro σ _
  split_ifs with h
  · rw [one_mul]
    nlinarith [sq_abs ((psum σ t : ℝ)), abs_nonneg ((psum σ t : ℝ))]
  · rw [zero_mul]
    positivity

theorem ite_nonneg_one (p : Prop) [Decidable p] : (0 : ℝ) ≤ if p then 1 else 0 := by
  split_ifs <;> norm_num

 

theorem cnt_add_le (t₁ t₂ : ℕ) (m : ℤ) (r : ℝ) (hr : 2 * r ≤ |(m : ℝ)|) :
    (cnt (t₁ + t₂) m : ℝ) ≤
      ((univ.filter fun σ : Fin t₁ → Bool => r ≤ |(psum σ t₁ : ℝ)|).card : ℝ) * cmax t₂ +
      ((univ.filter fun τ : Fin t₂ → Bool => r ≤ |(psum τ t₂ : ℝ)|).card : ℝ) * cmax t₁ := by
  classical
  unfold cnt
  rw [← Finset.sum_boole, P3.sum_append]
  simp only [psum_append_add]
  have hpt : ∀ (σ : Fin t₁ → Bool) (τ : Fin t₂ → Bool),
      (if psum σ t₁ + psum τ t₂ = m then (1 : ℝ) else 0) ≤
        (if r ≤ |(psum σ t₁ : ℝ)| then 1 else 0) *
            (if psum τ t₂ = m - psum σ t₁ then 1 else 0) +
          (if r ≤ |(psum τ t₂ : ℝ)| then 1 else 0) *
            (if psum σ t₁ = m - psum τ t₂ then 1 else 0) := by
    intro σ τ
    by_cases h : psum σ t₁ + psum τ t₂ = m
    · have hB : psum τ t₂ = m - psum σ t₁ := by omega
      have hA : psum σ t₁ = m - psum τ t₂ := by omega
      rw [if_pos h, if_pos hB, if_pos hA, mul_one, mul_one]
      have hor : r ≤ |(psum σ t₁ : ℝ)| ∨ r ≤ |(psum τ t₂ : ℝ)| := by
        by_contra hc
        push_neg at hc
        have : |(m : ℝ)| ≤ |(psum σ t₁ : ℝ)| + |(psum τ t₂ : ℝ)| := by
          rw [← h]; push_cast; exact abs_add_le _ _
        linarith
      rcases hor with h1 | h1
      · rw [if_pos h1]
        have := ite_nonneg_one (r ≤ |(psum τ t₂ : ℝ)|)
        linarith
      · rw [if_pos h1]
        have := ite_nonneg_one (r ≤ |(psum σ t₁ : ℝ)|)
        linarith
    · rw [if_neg h]
      apply add_nonneg <;> apply mul_nonneg <;> exact ite_nonneg_one _
  have hsum := Finset.sum_le_sum fun σ (_ : σ ∈ univ) =>
    Finset.sum_le_sum fun τ (_ : τ ∈ univ) => hpt σ τ
  refine hsum.trans ?_
  simp only [Finset.sum_add_distrib]
  apply add_le_add
  · rw [← Finset.sum_boole, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro σ _
    rw [← Finset.mul_sum]
    split_ifs with hσ
    · rw [one_mul, one_mul, Finset.sum_boole]
      exact_mod_cast cnt_le_cmax t₂ (m - psum σ t₁)
    · simp
  · rw [Finset.sum_comm]
    rw [← Finset.sum_boole, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro τ _
    simp_rw [mul_comm (if r ≤ |(psum τ t₂ : ℝ)| then (1 : ℝ) else 0)]
    rw [← Finset.sum_mul]
    split_ifs with hτ
    · rw [mul_one, mul_one, Finset.sum_boole]
      exact_mod_cast cnt_le_cmax t₁ (m - psum τ t₂)
    · simp

 

 
def freeP (t : ℕ) (a b : ℤ × ℤ) : ℝ := avg^[t] (fun c => if c = b then 1 else 0) a

 
theorem avgIter_eq_sum (t : ℕ) (f : ℤ × ℤ → ℝ) (a : ℤ × ℤ) :
    avg^[t] f a = (∑ ω : Fin t → Bool × Bool, f (wpos a ω t)) / 4 ^ t := by
  induction t generalizing a with
  | zero =>
    rw [Function.iterate_zero, id, pow_zero, div_one, Fintype.sum_unique, wpos_zero]
  | succ t ih =>
    rw [Function.iterate_succ_apply', avg]
    simp_rw [ih]
    rw [P3.sum_cons]
    simp_rw [wpos_cons_succ]
    rw [← Finset.sum_div, div_div, pow_succ]

theorem freeP_eq (t : ℕ) (a b : ℤ × ℤ) :
    freeP t a b = (cnt t ((b.1 + b.2) - (a.1 + a.2)) : ℝ) *
      (cnt t ((b.1 - b.2) - (a.1 - a.2)) : ℝ) / 4 ^ t := by
  classical
  have hiff : ∀ ω : Fin t → Bool × Bool, wpos a ω t = b ↔
      (psum (fun l => (ω l).1) t = (b.1 + b.2) - (a.1 + a.2) ∧
        psum (fun l => (ω l).2) t = (b.1 - b.2) - (a.1 - a.2)) := by
    intro ω
    have hadd := wpos_add a ω t
    have hsub := wpos_sub a ω t
    constructor
    · rintro h
      rw [h] at hadd hsub
      constructor <;> omega
    · rintro ⟨h1, h2⟩
      apply Prod.ext <;> omega
  have key : ((univ.filter fun ω : Fin t → Bool × Bool => wpos a ω t = b).card : ℝ) =
      (cnt t ((b.1 + b.2) - (a.1 + a.2)) : ℝ) * (cnt t ((b.1 - b.2) - (a.1 - a.2)) : ℝ) := by
    unfold cnt
    rw [← card_filter_fst_snd]
    congr 2
    ext ω
    simp only [mem_filter, mem_univ, true_and]
    exact hiff ω
  unfold freeP
  rw [avgIter_eq_sum]
  congr 1
  rw [Finset.sum_boole]
  exact key

theorem freeP_mul_le (t : ℕ) (a b : ℤ × ℤ) : freeP t a b * (t + 1) ≤ 1 := by
  rw [freeP_eq]
  set x : ℝ := (cnt t ((b.1 + b.2) - (a.1 + a.2)) : ℝ) / 2 ^ t
  set y : ℝ := (cnt t ((b.1 - b.2) - (a.1 - a.2)) : ℝ) / 2 ^ t
  have h4 : (4 : ℝ) ^ t = 2 ^ t * 2 ^ t := by rw [← mul_pow]; norm_num
  have hxy : (cnt t ((b.1 + b.2) - (a.1 + a.2)) : ℝ) *
      (cnt t ((b.1 - b.2) - (a.1 - a.2)) : ℝ) / 4 ^ t = x * y := by
    rw [h4]; simp only [x, y]; field_simp
  rw [hxy]
  have hcm := cmax_sq_le t
  have hx : x ≤ (cmax t : ℝ) / 2 ^ t := by
    simp only [x]; gcongr; exact_mod_cast cnt_le_cmax t _
  have hy : y ≤ (cmax t : ℝ) / 2 ^ t := by
    simp only [y]; gcongr; exact_mod_cast cnt_le_cmax t _
  have hx0 : 0 ≤ x := by positivity
  have hy0 : 0 ≤ y := by positivity
  have hxy' : x * y ≤ ((cmax t : ℝ) / 2 ^ t) ^ 2 := by
    rw [sq]; exact mul_le_mul hx hy hy0 (cmax_nonneg t)
  have ht : (0 : ℝ) ≤ t + 1 := by positivity
  nlinarith

 

theorem cnt_off_le (t : ℕ) (m : ℤ) (r : ℝ) (hr0 : 0 < r) (hr : r ≤ |(m : ℝ)|) :
    (cnt t m : ℝ) / 2 ^ t * ((cmax t : ℝ) / 2 ^ t) * r ^ 2 ≤ 8 := by
  set t₁ := t / 2
  set t₂ := t - t / 2
  have ht : t₁ + t₂ = t := by omega
  have hsplit := cnt_add_le t₁ t₂ m (r / 2) (by linarith)
  rw [ht] at hsplit
  have hc1 := card_abs_psum_ge_le t₁ (r / 2) (by linarith)
  have hc2 := card_abs_psum_ge_le t₂ (r / 2) (by linarith)
  set A₁ : ℝ := ((univ.filter fun σ : Fin t₁ → Bool => r / 2 ≤ |(psum σ t₁ : ℝ)|).card : ℝ)
  set A₂ : ℝ := ((univ.filter fun τ : Fin t₂ → Bool => r / 2 ≤ |(psum τ t₂ : ℝ)|).card : ℝ)
  set β : ℕ → ℝ := fun s => (cmax s : ℝ) / 2 ^ s
  have hβ : ∀ s, β s ^ 2 * (s + 1) ≤ 1 := cmax_sq_le
  have hβ0 : ∀ s, 0 ≤ β s := cmax_nonneg
  have h2t : (2 : ℝ) ^ t = 2 ^ t₁ * 2 ^ t₂ := by rw [← pow_add, ht]
  
  have hcnt : (cnt t m : ℝ) / 2 ^ t ≤ A₁ / 2 ^ t₁ * β t₂ + A₂ / 2 ^ t₂ * β t₁ := by
    rw [h2t]
    have hp1 : (0 : ℝ) < 2 ^ t₁ := by positivity
    have hp2 : (0 : ℝ) < 2 ^ t₂ := by positivity
    simp only [β]
    rw [div_le_iff₀ (by positivity)]
    calc (cnt t m : ℝ) ≤ A₁ * cmax t₂ + A₂ * cmax t₁ := hsplit
      _ = (A₁ / 2 ^ t₁ * (cmax t₂ / 2 ^ t₂) + A₂ / 2 ^ t₂ * (cmax t₁ / 2 ^ t₁)) *
          (2 ^ t₁ * 2 ^ t₂) := by field_simp
  have hA₁ : A₁ / 2 ^ t₁ * r ^ 2 ≤ 4 * t₁ := by
    have hp1 : (0 : ℝ) < 2 ^ t₁ := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hp1]
    nlinarith [hc1]
  have hA₂ : A₂ / 2 ^ t₂ * r ^ 2 ≤ 4 * t₂ := by
    have hp2 : (0 : ℝ) < 2 ^ t₂ := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hp2]
    nlinarith [hc2]
  
  have hk1 : (t₁ : ℝ) * (β t₂ * β t) ≤ 1 := by
    have hsq : ((t₁ : ℝ) * (β t₂ * β t)) ^ 2 ≤ 1 := by
      have e1 := hβ t₂
      have e2 := hβ t
      have h12 : (t₁ : ℝ) ^ 2 ≤ (t₂ + 1) * (t + 1) := by
        have : (t₁ : ℝ) ≤ t₂ + 1 := by
          have : t₁ ≤ t₂ + 1 := by omega
          exact_mod_cast this
        have : (t₁ : ℝ) ≤ t + 1 := by
          have : t₁ ≤ t + 1 := by omega
          exact_mod_cast this
        have h0 : (0 : ℝ) ≤ t₁ := by positivity
        nlinarith
      have hprod : (β t₂ * β t) ^ 2 * ((t₂ + 1) * (t + 1)) ≤ 1 := by
        have : (β t₂ * β t) ^ 2 * ((t₂ + 1) * (t + 1)) =
            (β t₂ ^ 2 * (t₂ + 1)) * (β t ^ 2 * (t + 1)) := by ring
        rw [this]
        have := mul_le_mul e1 e2 (by positivity) zero_le_one
        linarith
      have hb : 0 ≤ (β t₂ * β t) ^ 2 := sq_nonneg _
      calc ((t₁ : ℝ) * (β t₂ * β t)) ^ 2 = (t₁ : ℝ) ^ 2 * (β t₂ * β t) ^ 2 := by ring
        _ ≤ ((t₂ + 1) * (t + 1)) * (β t₂ * β t) ^ 2 := by
          exact mul_le_mul_of_nonneg_right h12 hb
        _ ≤ 1 := by linarith
    have h0 : 0 ≤ (t₁ : ℝ) * (β t₂ * β t) := by
      have := hβ0 t₂; have := hβ0 t; positivity
    nlinarith
  have hk2 : (t₂ : ℝ) * (β t₁ * β t) ≤ 1 := by
    have hsq : ((t₂ : ℝ) * (β t₁ * β t)) ^ 2 ≤ 1 := by
      have e1 := hβ t₁
      have e2 := hβ t
      have h12 : (t₂ : ℝ) ^ 2 ≤ (t₁ + 1) * (t + 1) := by
        have : (t₂ : ℝ) ≤ t₁ + 1 := by
          have : t₂ ≤ t₁ + 1 := by omega
          exact_mod_cast this
        have : (t₂ : ℝ) ≤ t + 1 := by
          have : t₂ ≤ t + 1 := by omega
          exact_mod_cast this
        have h0 : (0 : ℝ) ≤ t₂ := by positivity
        nlinarith
      have hprod : (β t₁ * β t) ^ 2 * ((t₁ + 1) * (t + 1)) ≤ 1 := by
        have : (β t₁ * β t) ^ 2 * ((t₁ + 1) * (t + 1)) =
            (β t₁ ^ 2 * (t₁ + 1)) * (β t ^ 2 * (t + 1)) := by ring
        rw [this]
        have := mul_le_mul e1 e2 (by positivity) zero_le_one
        linarith
      have hb : 0 ≤ (β t₁ * β t) ^ 2 := sq_nonneg _
      calc ((t₂ : ℝ) * (β t₁ * β t)) ^ 2 = (t₂ : ℝ) ^ 2 * (β t₁ * β t) ^ 2 := by ring
        _ ≤ ((t₁ + 1) * (t + 1)) * (β t₁ * β t) ^ 2 := by
          exact mul_le_mul_of_nonneg_right h12 hb
        _ ≤ 1 := by linarith
    have h0 : 0 ≤ (t₂ : ℝ) * (β t₁ * β t) := by
      have := hβ0 t₁; have := hβ0 t; positivity
    nlinarith
  have hbt0 := hβ0 t
  have hb1 := hβ0 t₁
  have hb2 := hβ0 t₂
  have hA₁0 : 0 ≤ A₁ / 2 ^ t₁ := by positivity
  have hA₂0 : 0 ≤ A₂ / 2 ^ t₂ := by positivity
  calc (cnt t m : ℝ) / 2 ^ t * ((cmax t : ℝ) / 2 ^ t) * r ^ 2
      = (cnt t m : ℝ) / 2 ^ t * β t * r ^ 2 := rfl
    _ ≤ (A₁ / 2 ^ t₁ * β t₂ + A₂ / 2 ^ t₂ * β t₁) * β t * r ^ 2 := by
        gcongr
    _ = (A₁ / 2 ^ t₁ * r ^ 2) * (β t₂ * β t) + (A₂ / 2 ^ t₂ * r ^ 2) * (β t₁ * β t) := by
        ring
    _ ≤ (4 * t₁) * (β t₂ * β t) + (4 * t₂) * (β t₁ * β t) := by
        gcongr
    _ = 4 * ((t₁ : ℝ) * (β t₂ * β t)) + 4 * ((t₂ : ℝ) * (β t₁ * β t)) := by ring
    _ ≤ 4 * 1 + 4 * 1 := by gcongr
    _ = 8 := by norm_num

 

theorem freeP_mul_sq_le (t : ℕ) (a b : ℤ × ℤ) (r : ℝ) (hr0 : 0 < r)
    (hr : r ≤ |((b.1 - a.1 : ℤ) : ℝ)| ∨ r ≤ |((b.2 - a.2 : ℤ) : ℝ)|) :
    freeP t a b * r ^ 2 ≤ 8 := by
  rw [freeP_eq]
  set u : ℤ := (b.1 + b.2) - (a.1 + a.2)
  set v : ℤ := (b.1 - b.2) - (a.1 - a.2)
  have h4 : (4 : ℝ) ^ t = 2 ^ t * 2 ^ t := by rw [← mul_pow]; norm_num
  have hxy : (cnt t u : ℝ) * (cnt t v : ℝ) / 4 ^ t =
      ((cnt t u : ℝ) / 2 ^ t) * ((cnt t v : ℝ) / 2 ^ t) := by
    rw [h4]; field_simp
  rw [hxy]
  
  have huv : r ≤ |(u : ℝ)| ∨ r ≤ |(v : ℝ)| := by
    have e1 : ((b.1 - a.1 : ℤ) : ℝ) = ((u : ℝ) + v) / 2 := by
      simp only [u, v]; push_cast; ring
    have e2 : ((b.2 - a.2 : ℤ) : ℝ) = ((u : ℝ) - v) / 2 := by
      simp only [u, v]; push_cast; ring
    by_contra hc
    push_neg at hc
    rcases hr with hr | hr
    · rw [e1] at hr
      have := abs_add_le (u : ℝ) v
      rw [abs_div, abs_two] at hr
      linarith
    · rw [e2] at hr
      have := abs_sub (u : ℝ) v
      rw [abs_div, abs_two] at hr
      linarith
  have hcu : (cnt t u : ℝ) / 2 ^ t ≤ (cmax t : ℝ) / 2 ^ t := by
    gcongr; exact_mod_cast cnt_le_cmax t u
  have hcv : (cnt t v : ℝ) / 2 ^ t ≤ (cmax t : ℝ) / 2 ^ t := by
    gcongr; exact_mod_cast cnt_le_cmax t v
  have h0u : 0 ≤ (cnt t u : ℝ) / 2 ^ t := by positivity
  have h0v : 0 ≤ (cnt t v : ℝ) / 2 ^ t := by positivity
  rcases huv with hu | hv
  · have := cnt_off_le t u r hr0 hu
    calc (cnt t u : ℝ) / 2 ^ t * ((cnt t v : ℝ) / 2 ^ t) * r ^ 2
        ≤ (cnt t u : ℝ) / 2 ^ t * ((cmax t : ℝ) / 2 ^ t) * r ^ 2 := by gcongr
      _ ≤ 8 := this
  · have := cnt_off_le t v r hr0 hv
    calc (cnt t u : ℝ) / 2 ^ t * ((cnt t v : ℝ) / 2 ^ t) * r ^ 2
        ≤ ((cmax t : ℝ) / 2 ^ t) * ((cnt t v : ℝ) / 2 ^ t) * r ^ 2 := by gcongr
      _ = (cnt t v : ℝ) / 2 ^ t * ((cmax t : ℝ) / 2 ^ t) * r ^ 2 := by ring
      _ ≤ 8 := this

 

theorem avgIter_mono (t : ℕ) {f g : ℤ × ℤ → ℝ} (h : ∀ c, f c ≤ g c) (a : ℤ × ℤ) :
    avg^[t] f a ≤ avg^[t] g a := by
  induction t generalizing a with
  | zero => exact h a
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact avg_mono ih a

theorem killIter_le_avgIter (U : Finset (ℤ × ℤ)) (t : ℕ) {f : ℤ × ℤ → ℝ}
    (hf : ∀ c, 0 ≤ f c) (a : ℤ × ℤ) : (killOp U)^[t] f a ≤ avg^[t] f a := by
  induction t generalizing a with
  | zero => exact le_rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    by_cases ha : a ∈ U
    · rw [killOp_of_mem ha]
      apply avg_mono
      intro c
      split_ifs
      · exact ih c
      · exact killIter_nonneg U t hf c |>.trans (ih c)
    · rw [killOp_of_not_mem ha]
      exact avg_nonneg (fun c => killIter_nonneg U t hf c |>.trans (ih c)) a

end SupercriticalLQGUniqueness.B2.QPos.P4
