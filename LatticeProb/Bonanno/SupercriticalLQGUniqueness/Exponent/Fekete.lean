/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.Fekete at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5Sub




 

set_option autoImplicit false

open Filter Topology

namespace SupercriticalLQGUniqueness.Exponent.Fekete

variable {a : ℕ → ℝ} {C θ B : ℝ} {k₀ : ℕ}


private lemma greedy_bound_local (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hC : 0 ≤ C) (hnn : ∀ n, 0 ≤ a n)
    (hB0 : 0 ≤ B)
    (hsub : ∀ k l : ℕ, k₀ ≤ k → 1 ≤ l → l ≤ k →
      a (k + l) ≤ a k + a l + C * ((k : ℝ) + l) * (k : ℝ) ^ (-θ))
    {m : ℕ} (hm : 1 ≤ m) (hm₀ : k₀ ≤ m)
    (hB : ∀ n : ℕ, n < m → a n ≤ B) (n : ℕ) :
    a n ≤ n * (a m / m + C * (m : ℝ) ^ (-θ) * (1 / (1 - (2 : ℝ) ^ (-θ)))) + B +
      2 ^ θ * C * (Nat.log 2 n) * (n : ℝ) ^ (1 - θ) := by
  set ρ : ℝ := (2 : ℝ) ^ (-θ)
  have hρ1 : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hρ0 : 0 < ρ := by positivity
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  set S := a m / m + C * (m : ℝ) ^ (-θ) * (1 / (1 - ρ))
  have hS : 0 ≤ S := by
    have : 0 < 1 - ρ := sub_pos.mpr hρ1
    have := hnn m; positivity
  have hdbl : ∀ j, a (2 ^ j * m) ≤ ((2 ^ j * m : ℕ) : ℝ) * S := fun j => by
    have h := LQGMetric.DZZ.doubling_bound hθ hC hsub hm hm₀ j
    have hpos : (0 : ℝ) < ((2 ^ j * m : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_pos (by positivity) hm
    rw [div_le_iff₀ hpos] at h
    refine h.trans ?_
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ hpos.le
    have : 0 ≤ C * (m : ℝ) ^ (-θ) * (1 / (1 - ρ)) := by
      have : 0 < 1 - ρ := sub_pos.mpr hρ1; positivity
    have : 0 ≤ ρ ^ j := by positivity
    nlinarith
  have herr : ∀ n : ℕ, 0 ≤ 2 ^ θ * C * (Nat.log 2 n) * (n : ℝ) ^ (1 - θ) := fun n => by positivity
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hnm : n < m
    · have h1 : a n ≤ B := hB n hnm
      have : 0 ≤ (n : ℝ) * S := by positivity
      linarith [herr n]
    push Not at hnm
    have hq : n / m ≠ 0 := (Nat.div_pos hnm hm).ne'
    set j := Nat.log 2 (n / m)
    have hjle : 2 ^ j * m ≤ n :=
      (Nat.mul_le_mul_right m (Nat.pow_log_le_self 2 hq)).trans (Nat.div_mul_le_self n m)
    have hjlt : n < 2 ^ (j + 1) * m :=
      (Nat.div_lt_iff_lt_mul hm).mp (Nat.lt_pow_succ_log_self (by norm_num) _)
    set k := 2 ^ j * m
    set r := n - k
    have hnkr : n = k + r := (Nat.add_sub_cancel' hjle).symm
    have hrk : r < k := by
      have : 2 ^ (j + 1) * m = k + k := by simp only [k]; rw [pow_succ]; ring
      omega
    rcases Nat.eq_zero_or_pos r with hr0 | hr1
    · have : n = k := by omega
      rw [this]
      have h := hdbl j
      change a k ≤ (k : ℝ) * S at h
      linarith [herr k, hB0]
    
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hk0 : k₀ ≤ k := hm₀.trans (Nat.le_mul_of_pos_left m (by positivity))
    have hs := hsub k r hk0 hr1 hrk.le
    have ihr := ih r (by omega)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hk : (0 : ℝ) < k := by exact_mod_cast hk1
    have hkn : (n : ℝ) / 2 ≤ k := by
      have : (n : ℝ) < 2 * k := by
        have : n < 2 * k := by omega
        exact_mod_cast this
      linarith
    
    have hsplit : C * ((k : ℝ) + r) * (k : ℝ) ^ (-θ) ≤ 2 ^ θ * C * (n : ℝ) ^ (1 - θ) := by
      have e1 : ((k : ℝ) + r) = n := by rw [hnkr]; push_cast; ring
      rw [e1]
      have h1 : (k : ℝ) ^ (-θ) ≤ ((n : ℝ) / 2) ^ (-θ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hkn (by linarith)
      have h2 : (n : ℝ) * ((n : ℝ) / 2) ^ (-θ) = 2 ^ θ * (n : ℝ) ^ (1 - θ) := by
        rw [Real.div_rpow hn0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
          div_inv_eq_mul, sub_eq_add_neg, Real.rpow_add hn0, Real.rpow_one]
        ring
      calc C * (n : ℝ) * (k : ℝ) ^ (-θ) ≤ C * (n : ℝ) * ((n : ℝ) / 2) ^ (-θ) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 2 ^ θ * C * (n : ℝ) ^ (1 - θ) := by rw [mul_assoc, h2]; ring
    
    have hlog : Nat.log 2 r + 1 ≤ Nat.log 2 n := by
      rw [← Nat.log_mul_base (by norm_num) (by omega)]
      exact Nat.log_mono_right (by omega)
    have hpow : (r : ℝ) ^ (1 - θ) ≤ (n : ℝ) ^ (1 - θ) :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast (show r ≤ n by omega)) (by linarith)
    have hlogR : ((Nat.log 2 r : ℕ) : ℝ) + 1 ≤ (Nat.log 2 n : ℕ) := by exact_mod_cast hlog
    have hr_err : 2 ^ θ * C * (Nat.log 2 r) * (r : ℝ) ^ (1 - θ) + 2 ^ θ * C * (n : ℝ) ^ (1 - θ)
        ≤ 2 ^ θ * C * (Nat.log 2 n) * (n : ℝ) ^ (1 - θ) := by
      have h0 : 0 ≤ 2 ^ θ * C := by positivity
      have h3 : 2 ^ θ * C * (Nat.log 2 r) * (r : ℝ) ^ (1 - θ) ≤
          2 ^ θ * C * (Nat.log 2 r) * (n : ℝ) ^ (1 - θ) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      have h4 : 0 ≤ (n : ℝ) ^ (1 - θ) := by positivity
      have h5 : 2 ^ θ * C * (((Nat.log 2 r : ℕ) : ℝ) + 1) * (n : ℝ) ^ (1 - θ) ≤
          2 ^ θ * C * (Nat.log 2 n : ℕ) * (n : ℝ) ^ (1 - θ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogR h0) h4
      have e : 2 ^ θ * C * (((Nat.log 2 r : ℕ) : ℝ) + 1) * (n : ℝ) ^ (1 - θ) =
          2 ^ θ * C * (Nat.log 2 r : ℕ) * (n : ℝ) ^ (1 - θ) + 2 ^ θ * C * (n : ℝ) ^ (1 - θ) := by
        ring
      linarith
    have hnr : (n : ℝ) = k + r := by rw [hnkr]; push_cast; ring
    calc a n = a (k + r) := by rw [← hnkr]
      _ ≤ a k + a r + C * ((k : ℝ) + r) * (k : ℝ) ^ (-θ) := hs
      _ ≤ k * S + (r * S + B + 2 ^ θ * C * (Nat.log 2 r) * (r : ℝ) ^ (1 - θ)) +
          2 ^ θ * C * (n : ℝ) ^ (1 - θ) := by
        have h := hdbl j
        change a k ≤ (k : ℝ) * S at h
        linarith
      _ ≤ n * S + B + 2 ^ θ * C * (Nat.log 2 n) * (n : ℝ) ^ (1 - θ) := by
        have : (n : ℝ) * S = k * S + r * S := by rw [hnr]; ring
        linarith



private lemma log_mul_rpow_neg_tendsto_zero (hθ : 0 < θ) :
    Tendsto (fun n : ℕ => (Nat.log 2 n : ℝ) * (n : ℝ) ^ (-θ)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun y : ℝ => Real.log y / y ^ θ) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop hθ).tendsto_div_nhds_zero
  have h2 := (h1.comp tendsto_natCast_atTop_atTop).const_mul (1 / Real.log 2)
  rw [mul_zero] at h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2
    (Eventually.of_forall fun n => by positivity) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hl := Real.natLog_le_logb n 2
  simp only [Nat.cast_ofNat] at hl
  rw [Real.logb] at hl
  calc (Nat.log 2 n : ℝ) * (n : ℝ) ^ (-θ) ≤ (Real.log n / Real.log 2) * (n : ℝ) ^ (-θ) :=
        mul_le_mul_of_nonneg_right hl (by positivity)
    _ = 1 / Real.log 2 * (Real.log n / (n : ℝ) ^ θ) := by
        rw [Real.rpow_neg hn0.le]; ring


private lemma upper_linear_of_near_subadd (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hC : 0 ≤ C)
    (hzero : a 0 = 0) (hnn : ∀ n, 0 ≤ a n)
    (hsub : ∀ k l : ℕ, k₀ ≤ k → 1 ≤ l → l ≤ k →
      a (k + l) ≤ a k + a l + C * ((k : ℝ) + l) * (k : ℝ) ^ (-θ)) :
    ∃ M : ℝ, ∀ n : ℕ, a n ≤ M * n := by
  let m : ℕ := max k₀ 1
  have hm : 1 ≤ m := le_max_right k₀ 1
  have hm₀ : k₀ ≤ m := le_max_left k₀ 1
  let B : ℝ := ∑ i ∈ Finset.range m, max (a i) 0
  have hB0 : 0 ≤ B := Finset.sum_nonneg (fun i _ => le_max_right (a i) 0)
  have hB : ∀ i : ℕ, i < m → a i ≤ B := by
    intro i hi
    exact (le_max_left (a i) 0).trans
      (Finset.single_le_sum (fun j _ => le_max_right (a j) 0) (Finset.mem_range.mpr hi))
  let S : ℝ := a m / m + C * (m : ℝ) ^ (-θ) * (1 / (1 - (2 : ℝ) ^ (-θ)))
  have hbound (n : ℕ) : a n ≤ n * S + B +
      2 ^ θ * C * (Nat.log 2 n) * (n : ℝ) ^ (1 - θ) :=
    greedy_bound_local hθ hθ1 hC hnn hB0 hsub hm hm₀ hB n
  have hA : Tendsto (fun n : ℕ => B / (n : ℝ) +
      2 ^ θ * C * ((Nat.log 2 n : ℝ) * (n : ℝ) ^ (-θ))) atTop (𝓝 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat B).add
      ((log_mul_rpow_neg_tendsto_zero hθ).const_mul (2 ^ θ * C))
    simpa using h
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hA (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  let F : ℝ := ∑ i ∈ Finset.range N, max (a i / (i : ℝ)) 0
  have hF0 : 0 ≤ F := Finset.sum_nonneg (fun i _ => le_max_right (a i / (i : ℝ)) 0)
  let M : ℝ := max (S + 1) F
  refine ⟨M, fun n => ?_⟩
  by_cases hn : n = 0
  · subst n
    simp [hzero]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  by_cases hnN : n < N
  · have hsmall : a n / (n : ℝ) ≤ F :=
      (le_max_left (a n / (n : ℝ)) 0).trans
        (Finset.single_le_sum (fun i _ => le_max_right (a i / (i : ℝ)) 0)
          (Finset.mem_range.mpr hnN))
    have hle : a n / (n : ℝ) ≤ M := hsmall.trans (le_max_right (S + 1) F)
    exact (div_le_iff₀ hn0).mp hle
  · have hnN' : N ≤ n := Nat.le_of_not_gt hnN
    have hpow : (n : ℝ) ^ (1 - θ) = n * (n : ℝ) ^ (-θ) := by
      rw [sub_eq_add_neg, Real.rpow_add hn0, Real.rpow_one]
    have hb : a n / (n : ℝ) ≤ S +
        (B / n + 2 ^ θ * C * ((Nat.log 2 n : ℝ) * (n : ℝ) ^ (-θ))) := by
      rw [div_le_iff₀ hn0]
      have hg := hbound n
      rw [hpow] at hg
      calc a n ≤ _ := hg
        _ = _ := by field_simp; ring
    have hle : a n / (n : ℝ) ≤ M := by
      have ht := hN n hnN'
      change B / (n : ℝ) + 2 ^ θ * C * ((Nat.log 2 n : ℝ) * (n : ℝ) ^ (-θ)) < 1 at ht
      have hS := le_max_left (S + 1) F
      linarith
    exact (div_le_iff₀ hn0).mp hle


private lemma fekete_of_dzz_error (a : ℕ → ℝ) (C θ K : ℝ) (k₀ : ℕ)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hC : 0 ≤ C) (hk₀ : 1 ≤ k₀)
    (hlower : ∀ n : ℕ, 1 ≤ n → -K * (n : ℝ) ≤ a n)
    (hsub : ∀ k l : ℕ, k₀ ≤ k → 1 ≤ l → l ≤ k →
      a (k + l) ≤ a k + a l + C * ((k : ℝ) + l) * (k : ℝ) ^ (-θ)) :
    ∃ L : ℝ, Tendsto (fun n : ℕ => a n / (n : ℝ)) atTop (𝓝 L) := by
  let b : ℕ → ℝ := fun n => if n = 0 then 0 else a n + K * n
  have hbzero : b 0 = 0 := by simp [b]
  have hbnn : ∀ n, 0 ≤ b n := by
    intro n
    by_cases hn : n = 0
    · simp [b, hn]
    · simp only [b, hn, ↓reduceIte]
      linarith only [hlower n (Nat.one_le_iff_ne_zero.mpr hn)]
  have hbsub : ∀ k l : ℕ, k₀ ≤ k → 1 ≤ l → l ≤ k →
      b (k + l) ≤ b k + b l + C * ((k : ℝ) + l) * (k : ℝ) ^ (-θ) := by
    intro k l hk hl hlk
    have hkpos : k ≠ 0 := Nat.ne_of_gt (hk₀.trans hk)
    have hlpos : l ≠ 0 := by omega
    have hklpos : k + l ≠ 0 := by omega
    simp only [b, hkpos, hlpos, hklpos, ↓reduceIte]
    have hs := hsub k l hk hl hlk
    push_cast
    linarith only [hs]
  obtain ⟨M, hM⟩ := upper_linear_of_near_subadd hθ hθ1 hC hbzero hbnn hbsub
  obtain ⟨χ, hχ⟩ := LQGMetric.DZZ.tendsto_div_of_near_subadd
    (a := b) (C := C) (θ := θ) (M := M) (k₀ := k₀)
    hθ hθ1 hC hbnn hM hbsub
  refine ⟨χ - K, ?_⟩
  have h := hχ.sub (tendsto_const_nhds (x := K) (f := atTop))
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hne : n ≠ 0 := by omega
  simp only [b, hne, ↓reduceIte]
  field_simp
  ring


 

theorem fekete_rpow_error (a : ℕ → ℝ) (C θ K : ℝ) (m₀ n₀ : ℕ)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hC : 0 ≤ C)
    (hlower : ∀ n : ℕ, 1 ≤ n → -K * (n : ℝ) ≤ a n)
    (hsub : ∀ m k : ℕ, m₀ ≤ m → 1 ≤ k → n₀ ≤ m + k →
      a (m + k) ≤ a m + a k + C * ((m + k : ℕ) : ℝ) ^ (1 - θ)) :
    ∃ L : ℝ, Tendsto (fun n : ℕ => a n / (n : ℝ)) atTop (𝓝 L) := by
  let k₀ : ℕ := max 1 (max m₀ n₀)
  have hk₀ : 1 ≤ k₀ := le_max_left 1 (max m₀ n₀)
  apply fekete_of_dzz_error a C θ K k₀ hθ hθ1 hC hk₀ hlower
  intro k l hk hl hlk
  have hk' : max m₀ n₀ ≤ k := (le_max_right 1 (max m₀ n₀)).trans hk
  have hm₀ : m₀ ≤ k := (le_max_left m₀ n₀).trans hk'
  have hn₀ : n₀ ≤ k + l := (le_max_right m₀ n₀).trans (hk'.trans (Nat.le_add_right k l))
  have hs := hsub k l hm₀ hl hn₀
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (hk₀.trans hk)
  have hklpos : (0 : ℝ) < (k + l : ℕ) := by exact_mod_cast (show 0 < k + l by omega)
  have hneg : ((k + l : ℕ) : ℝ) ^ (-θ) ≤ (k : ℝ) ^ (-θ) :=
    Real.rpow_le_rpow_of_nonpos hkpos (by exact_mod_cast (Nat.le_add_right k l)) (by linarith)
  have hpow : ((k + l : ℕ) : ℝ) ^ (1 - θ) =
      ((k + l : ℕ) : ℝ) * ((k + l : ℕ) : ℝ) ^ (-θ) := by
    rw [sub_eq_add_neg, Real.rpow_add hklpos, Real.rpow_one]
  have he : C * ((k + l : ℕ) : ℝ) ^ (1 - θ) ≤
      C * ((k : ℝ) + l) * (k : ℝ) ^ (-θ) := by
    calc C * ((k + l : ℕ) : ℝ) ^ (1 - θ) =
          (C * ((k + l : ℕ) : ℝ)) * ((k + l : ℕ) : ℝ) ^ (-θ) := by rw [hpow]; ring
      _ ≤ (C * ((k + l : ℕ) : ℝ)) * (k : ℝ) ^ (-θ) :=
        mul_le_mul_of_nonneg_left hneg (by positivity)
      _ = C * ((k : ℝ) + l) * (k : ℝ) ^ (-θ) := by push_cast; ring
  exact hs.trans (by linarith only [he])

 
theorem fekete_two_thirds_error (a : ℕ → ℝ) (C K : ℝ) (m₀ n₀ : ℕ)
    (hC : 0 ≤ C)
    (hlower : ∀ n : ℕ, 1 ≤ n → -K * (n : ℝ) ≤ a n)
    (hsub : ∀ m k : ℕ, m₀ ≤ m → 1 ≤ k → n₀ ≤ m + k →
      a (m + k) ≤ a m + a k + C * ((m + k : ℕ) : ℝ) ^ (2 / 3 : ℝ)) :
    ∃ L : ℝ, Tendsto (fun n : ℕ => a n / (n : ℝ)) atTop (𝓝 L) := by
  have hθ : (0 : ℝ) < 1 / 3 := by norm_num
  have hθ1 : (1 / 3 : ℝ) ≤ 1 := by norm_num
  convert fekete_rpow_error a C (1 / 3) K m₀ n₀ hθ hθ1 hC hlower ?_ using 1
  intro m k hm hk hn
  convert hsub m k hm hk hn using 1; norm_num


 

theorem fekete_two_thirds_error_of_eventual_lower (a : ℕ → ℝ) (C K : ℝ) (m₀ n₀ : ℕ)
    (hC : 0 ≤ C)
    (hlower : ∀ᶠ n : ℕ in atTop, -K * (n : ℝ) ≤ a n)
    (hsub : ∀ m k : ℕ, m₀ ≤ m → 1 ≤ k → n₀ ≤ m + k →
      a (m + k) ≤ a m + a k + C * ((m + k : ℕ) : ℝ) ^ (2 / 3 : ℝ)) :
    ∃ L : ℝ, Tendsto (fun n : ℕ => a n / (n : ℝ)) atTop (𝓝 L) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hlower
  let F : ℝ := ∑ i ∈ Finset.range N, max (-a i / (i : ℝ)) 0
  let K' : ℝ := max K F
  have hK' : K ≤ K' := le_max_left K F
  have hglobal : ∀ n : ℕ, 1 ≤ n → -K' * (n : ℝ) ≤ a n := by
    intro n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    by_cases hnN : n < N
    · have hsmall : -a n / (n : ℝ) ≤ F :=
        (le_max_left (-a n / (n : ℝ)) 0).trans
          (Finset.single_le_sum (fun i _ => le_max_right (-a i / (i : ℝ)) 0)
            (Finset.mem_range.mpr hnN))
      have hle : -a n / (n : ℝ) ≤ K' := hsmall.trans (le_max_right K F)
      have := (div_le_iff₀ hnpos).mp hle
      linarith
    · have hln := hN n (Nat.le_of_not_gt hnN)
      nlinarith [mul_le_mul_of_nonneg_right hK' hnpos.le]
  exact fekete_two_thirds_error a C K' m₀ n₀ hC hglobal hsub


end SupercriticalLQGUniqueness.Exponent.Fekete
