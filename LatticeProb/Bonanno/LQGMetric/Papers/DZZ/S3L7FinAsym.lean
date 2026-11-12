/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L7FinAsym at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L7FinCore
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# DZZ Lemma 3.7, (eq-B-percolation-Phi) (P2-DZZ3F)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 958–1015). With
`ε = 2^{-kL37} = min {2^{-n} : 2^n ≤ 4 C_mc log δ⁻¹}` and
`λ = lamL37 δ δ' = (δ/δ')³ e^{(log δ⁻¹)^{0.7}}`, for every dyadic box `B` with
`1 ≤ m_B ≤ C_mc log₂ δ⁻¹`:
`P({M_s(B) ≤ δ²} ∩ 𝓔_{δ,α} ∩ 𝓔ᶜ_{δ', B, ε, λ}) ≤ δ^{10 C_mc + 10}`.

Parameters (DZZ l. 990): `t = 2^{-(k + k'')}` with `2^{k''} ≈ λ / 2^5` (DZZ:
`t = ε 2^{-⌈0.9 log₂ λ⌉}`; we take `2^{k''} ∈ (λ/64, λ/32]`, which gives `Ψ ≤ 8(2^{k''}+2) ≤ λ`
and `t^{0.8} ≤ (δ'/δ)^2 e^{-0.8 (log δ⁻¹)^{0.7}}`), threshold `a = 1.2 log t⁻¹` (DZZ's
`η ≤ 1.5 log t⁻¹` normalized), `p = 8 (2^{k''}+2) e^{-a} ≤ 24 t^{0.2}`, `θ = e^{-(log δ⁻¹)^{0.7}/100}`.
The asymptotics are done with `u = (log δ⁻¹)^{1/10}`: every requirement is a polynomial
inequality in `u` (`ev_pow_le`), using `log L ≤ 10 u` and `e^y ≥ 1 + y`, `e^y ≥ y²/2`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

/-- `ε = 2^{-kL37 γ δ} = min {2^{-n} : 2^n ≤ 4 C_mc log δ⁻¹}` (DZZ Lemma 3.7). -/
def kL37 (γ δ : ℝ) : ℕ := Nat.log 2 ⌊4 * dzzCmc γ * Real.log δ⁻¹⌋₊

/-- `λ = (δ/δ')³ e^{(log δ⁻¹)^{0.7}}` (DZZ Lemma 3.7). -/
def lamL37 (δ δ' : ℝ) : ℝ := (δ / δ') ^ 3 * Real.exp (Real.log δ⁻¹ ^ (0.7 : ℝ))

lemma ev_pow_le {a : ℝ} (ha : 0 < a) (c : ℝ) {q p : ℕ} (hqp : q < p) :
    ∀ᶠ u : ℝ in atTop, c * u ^ q ≤ a * u ^ p := by
  filter_upwards [eventually_ge_atTop (max 1 (|c| / a))] with u hu
  have h1 : 1 ≤ u := (le_max_left _ _).trans hu
  have h2 : |c| / a ≤ u := (le_max_right _ _).trans hu
  have h3 : |c| ≤ a * u := by rwa [div_le_iff₀ ha, mul_comm] at h2
  have hq : (0 : ℝ) ≤ u ^ q := by positivity
  calc c * u ^ q ≤ |c| * u ^ q := mul_le_mul_of_nonneg_right (le_abs_self c) hq
    _ ≤ a * u * u ^ q := mul_le_mul_of_nonneg_right h3 hq
    _ = a * u ^ (q + 1) := by ring
    _ ≤ a * u ^ p := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 hqp) ha.le

/-- The polynomial requirements in `u = (log δ⁻¹)^{1/10}`. -/
lemma l37_ev (C γ α : ℝ) (hC : 0 < C) : ∃ U : ℝ, 1 ≤ U ∧ ∀ u ≥ U,
    8 ≤ C * u ^ 10 ∧ 256 * C * u ^ 10 ≤ 1 / 2 * u ^ 14 ∧
    24 / 5 + γ * α * 10 * u ^ 6 + γ ^ 2 * 93 * (C + 4) * u ^ 5 ≤ 7 / 10 * u ^ 7 ∧
    1600 ≤ u ^ 7 ∧ 32 * C * u ^ 10 ≤ 1 / 2 * u ^ 20 ∧
    (10 * C + 11) * u ^ 10 + 3 / 200 * u ^ 7 ≤ C / 200 * u ^ 17 := by
  have e1 := ev_pow_le hC 8 (show 0 < 10 by norm_num)
  have e2 := ev_pow_le (show (0 : ℝ) < 1 / 2 by norm_num) (256 * C) (show 10 < 14 by norm_num)
  have e3 := ev_pow_le (show (0 : ℝ) < 1 / 10 by norm_num) (24 / 5) (show 0 < 7 by norm_num)
  have e4 := ev_pow_le (show (0 : ℝ) < 3 / 10 by norm_num) (γ * α * 10) (show 6 < 7 by norm_num)
  have e5 := ev_pow_le (show (0 : ℝ) < 3 / 10 by norm_num) (γ ^ 2 * 93 * (C + 4))
    (show 5 < 7 by norm_num)
  have e6 := ev_pow_le (show (0 : ℝ) < 1 by norm_num) 1600 (show 0 < 7 by norm_num)
  have e7 := ev_pow_le (show (0 : ℝ) < 1 / 2 by norm_num) (32 * C) (show 10 < 20 by norm_num)
  have e8 := ev_pow_le (show 0 < C / 400 by positivity) (10 * C + 11) (show 10 < 17 by norm_num)
  have e9 := ev_pow_le (show 0 < C / 400 by positivity) (3 / 200) (show 7 < 17 by norm_num)
  obtain ⟨U, hU⟩ := eventually_atTop.1
    (e1.and (e2.and (e3.and (e4.and (e5.and (e6.and (e7.and (e8.and e9))))))))
  refine ⟨max U 1, le_max_right _ _, fun u hu => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hU u ((le_max_left _ _).trans hu)
  simp only [pow_zero, mul_one, one_mul] at h1 h3 h6
  exact ⟨h1, h2, by linarith, h6, h7, by linarith⟩

lemma two_mul_add_le_pow : ∀ m : ℕ, 2 * (m + 5) + 1 ≤ 2 ^ (m + 4)
  | 0 => by norm_num
  | m + 1 => by
    rw [show m + 1 + 4 = (m + 4) + 1 by ring, pow_succ]
    have := two_mul_add_le_pow m
    omega

lemma inv_two_pow_eq_exp (n : ℕ) : (2 : ℝ)⁻¹ ^ n = Real.exp (-(n * Real.log 2)) := by
  rw [Real.exp_neg, ← Real.log_pow, Real.exp_log (by positivity), inv_pow]

lemma two_pow_eq_exp (n : ℕ) : (2 : ℝ) ^ n = Real.exp (n * Real.log 2) := by
  rw [← Real.log_pow, Real.exp_log (by positivity)]

lemma exp_sq_eq (y : ℝ) : Real.exp y ^ 2 = Real.exp (2 * y) := by
  rw [← Real.exp_nat_mul]; norm_num

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

lemma encEventPsi_mono {γ δ' : ℝ} {b : DyBox} {k : ℕ} {l₁ l₂ : ℝ} (h : l₁ ≤ l₂) :
    encEventPsi γ W δ' b k l₁ ⊆ encEventPsi γ W δ' b k l₂ := by
  intro ω hω
  obtain ⟨l, hl, hch, hmem, henc⟩ := hω
  refine ⟨l, hl, hch, fun b' hb' => ⟨(hmem b' hb').1, (hmem b' hb').2.1, ?_⟩, henc⟩
  obtain ⟨N, hN, hle⟩ := (hmem b' hb').2.2
  exact ⟨N, hN, hle.trans h⟩

set_option maxHeartbeats 1000000 in
/-- **DZZ Lemma 3.7, (eq-B-percolation-Phi)** (l. 958–962, proof l. 966–1015).
Stated for `α > 4 C_mc` (DZZ assume `α > max {α₀, 4 C_mc}`; `α₀` is not used in this part). -/
theorem dzz_lemma37_perc (hW : IsWhiteNoise P W) {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : 4 * dzzCmc γ < α) :
    ∃ δ₀ > 0, ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ δ' ∈ Ioc (0 : ℝ) δ, ∀ b : DyBox, 1 ≤ b.n →
      (b.n : ℝ) ≤ dzzCmc γ * Real.logb 2 δ⁻¹ →
      P ({ω | approxLQG γ W ω b ≤ δ ^ 2} ∩ eventEFine γ W α δ ∩
        (encEventPsi γ W δ' b (kL37 γ δ) (lamL37 δ δ'))ᶜ) ≤
        ENNReal.ofReal (δ ^ (10 * dzzCmc γ + 10)) := by
  have hC : 0 < dzzCmc γ := by have := l31theta_pos hγ hγ2; unfold dzzCmc; linarith
  obtain ⟨U, hU1, hU⟩ := l37_ev (dzzCmc γ) γ α hC
  refine ⟨Real.exp (-(U ^ 10)), Real.exp_pos _, ?_⟩
  rintro δ ⟨hδ0, hδ1⟩ δ' ⟨hδ'0, hδ'δ⟩ b hb1 hbn
  obtain ⟨k, hkdef⟩ : ∃ k, k = kL37 γ δ := ⟨_, rfl⟩
  obtain ⟨lam, hlamdef⟩ : ∃ lam, lam = lamL37 δ δ' := ⟨_, rfl⟩
  rw [← hkdef, ← hlamdef]
  set C := dzzCmc γ with hCdef
  have hα0 : 0 < α := by linarith
  set L := Real.log δ⁻¹ with hLdef
  have hlogδ : Real.log δ = -L := by rw [hLdef, Real.log_inv, neg_neg]
  have hL : U ^ 10 < L := by
    have := Real.log_lt_log hδ0 hδ1
    rw [Real.log_exp] at this; linarith
  have hU0 : (0 : ℝ) ≤ U := by linarith
  have hL0 : 0 < L := lt_of_le_of_lt (by positivity) hL
  set u := L ^ ((1 : ℝ) / 10) with hudef
  have hu10 : u ^ 10 = L := by
    rw [hudef, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
  have hu7 : L ^ (0.7 : ℝ) = u ^ 7 := by
    rw [hudef, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
  have huU : U ≤ u := by
    have h1 : (U ^ 10) ^ ((1 : ℝ) / 10) = U := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hU0]; norm_num
    rw [← h1]; exact Real.rpow_le_rpow (by positivity) hL.le (by norm_num)
  obtain ⟨E2, E3, E4, E5, E6, E7⟩ := hU u huU
  have hu1 : 1 ≤ u := hU1.trans huU
  have hu0 : 0 < u := by linarith
  have hL1 : 1 ≤ L := by rw [← hu10]; exact one_le_pow₀ hu1
  have hsqrt : Real.sqrt L = u ^ 5 := by
    rw [← hu10, show u ^ 10 = (u ^ 5) ^ 2 by ring]; exact Real.sqrt_sq (by positivity)
  have hlogL : Real.log L ≤ 10 * u := by
    have := Real.log_le_rpow_div hL0.le (show (0 : ℝ) < 1 / 10 by norm_num)
    rw [← hudef] at this
    calc Real.log L ≤ u / (1 / 10) := this
      _ = 10 * u := by ring
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2' : Real.log 2 < 1 := by have := Real.log_two_lt_d9; norm_num at this; linarith
  -- `k`: `2^k ≤ 4 C L < 2^{k+1}`
  set x := 4 * C * L with hx
  have hCL : 8 ≤ C * L := by rw [← hu10]; exact E2
  have hx32 : 32 ≤ x := by rw [hx]; linarith
  have hk' : k = Nat.log 2 ⌊x⌋₊ := by rw [hkdef]; rfl
  have hfl : ⌊x⌋₊ ≠ 0 := by
    have := Nat.floor_pos.2 (show (1 : ℝ) ≤ x by linarith); omega
  have hkx : (2 : ℝ) ^ k ≤ x := by
    have h1 := Nat.pow_log_le_self 2 hfl
    rw [← hk'] at h1
    have h2 : ((2 ^ k : ℕ) : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h1
    push_cast at h2; exact h2.trans (Nat.floor_le (by linarith))
  have hxk : x < (2 : ℝ) ^ (k + 1) := by
    have h1 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ⌊x⌋₊
    rw [← hk'] at h1
    have h2 : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ ((2 ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h2; linarith [Nat.lt_floor_add_one x]
  have hk5 : 5 ≤ k := by
    by_contra hk; push_neg at hk
    have : (2 : ℝ) ^ (k + 1) ≤ 2 ^ 5 := pow_le_pow_right₀ (by norm_num) (by omega)
    norm_num at this; linarith
  set h := 2 ^ (k - 1) with hhdef
  have hK : 2 ^ k = 2 * h := by
    rw [hhdef, ← pow_succ']; congr 1; omega
  have hhR : (2 : ℝ) ^ k = 2 * (h : ℝ) := by exact_mod_cast hK
  have h4 : 4 ≤ h := by
    calc 4 ≤ 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hhCL : C * L < h := by
    have : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    rw [hx] at hxk; linarith
  -- `λ` and `k''`: `2^{k''} · 32 ≤ λ < 2^{k''} · 64`
  have hr : 1 ≤ δ / δ' := by rw [le_div_iff₀ hδ'0]; linarith
  have hlam : lam = (δ / δ') ^ 3 * Real.exp (u ^ 7) := by rw [hlamdef, lamL37, ← hLdef, hu7]
  have hexp7 : u ^ 14 / 2 ≤ Real.exp (u ^ 7) := by
    have := Real.pow_div_factorial_le_exp (u ^ 7) (by positivity) 2
    calc u ^ 14 / 2 = (u ^ 7) ^ 2 / (Nat.factorial 2) := by
          rw [Nat.factorial_two]; push_cast; ring
      _ ≤ _ := this
  have hlam_ge : Real.exp (u ^ 7) ≤ lam := by
    rw [hlam]; exact le_mul_of_one_le_left (Real.exp_pos _).le (one_le_pow₀ hr)
  have hlam64 : 64 * x ≤ lam := by
    have : 64 * x = 256 * C * u ^ 10 := by rw [hx, ← hu10]; ring
    linarith
  have hlam0 : 0 < lam := by linarith
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ, ℓ = Nat.log 2 ⌊lam⌋₊ := ⟨_, rfl⟩
  have hfl2 : ⌊lam⌋₊ ≠ 0 := by
    have := Nat.floor_pos.2 (show (1 : ℝ) ≤ lam by linarith); omega
  have hℓ1 : (2 : ℝ) ^ ℓ ≤ lam := by
    have h1 := Nat.pow_log_le_self 2 hfl2
    rw [← hℓdef] at h1
    have h2 : ((2 ^ ℓ : ℕ) : ℝ) ≤ (⌊lam⌋₊ : ℝ) := by exact_mod_cast h1
    push_cast at h2; exact h2.trans (Nat.floor_le hlam0.le)
  have hℓ2 : lam < (2 : ℝ) ^ (ℓ + 1) := by
    have h1 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ⌊lam⌋₊
    rw [← hℓdef] at h1
    have h2 : ((⌊lam⌋₊ + 1 : ℕ) : ℝ) ≤ ((2 ^ (ℓ + 1) : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h2; linarith [Nat.lt_floor_add_one lam]
  have hkℓ : k + 6 ≤ ℓ := by
    by_contra hc; push_neg at hc
    have h1 : (2 : ℝ) ^ (ℓ + 1) ≤ 2 ^ (k + 6) := pow_le_pow_right₀ (by norm_num) (by omega)
    have e : (2 : ℝ) ^ (k + 6) = 64 * 2 ^ k := by rw [pow_add]; norm_num; ring
    linarith
  set k'' := ℓ - 5 with hk''def
  have hkk : k ≤ k'' := by omega
  have hk''ℓ : (2 : ℝ) ^ k'' * 32 = 2 ^ ℓ := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num, ← pow_add]; congr 1; omega
  have hlam8 : (8 * (2 ^ k'' + 2) : ℝ) ≤ lam := by linarith
  -- `τ = log t⁻¹ = (k + k'') log 2`
  set τ := ((k + k'' : ℕ) : ℝ) * Real.log 2 with hτdef
  have hloglam : Real.log lam = 3 * (Real.log δ - Real.log δ') + u ^ 7 := by
    rw [hlam, Real.log_mul (by positivity) (by positivity), Real.log_pow,
      Real.log_div hδ0.ne' hδ'0.ne', Real.log_exp]
    push_cast; ring
  have hτ : Real.log lam - 6 ≤ τ := by
    have h1 : Real.log lam < ((ℓ + 1 : ℕ) : ℝ) * Real.log 2 := by
      rw [← Real.log_pow]; exact Real.log_lt_log hlam0 hℓ2
    have e : τ = ((ℓ : ℝ) + 1) * Real.log 2 + (k : ℝ) * Real.log 2 - 6 * Real.log 2 := by
      rw [hτdef, hk''def]; push_cast [Nat.cast_sub (show 5 ≤ ℓ by omega)]; ring
    push_cast at h1
    have hk0 : (0 : ℝ) ≤ k := by positivity
    linarith [mul_nonneg hk0 hlog2.le]
  have hlogδδ' : Real.log δ' ≤ Real.log δ := Real.log_le_log hδ'0 hδ'δ
  have hτu : u ^ 7 - 6 ≤ τ := by linarith
  set a := 6 / 5 * τ with hadef
  have hinvτ : (2 : ℝ)⁻¹ ^ (k + k'') = Real.exp (-τ) := inv_two_pow_eq_exp _
  -- `hsmall`
  have hbn' : (b.n : ℝ) * Real.log 2 ≤ C * L := by
    rw [Real.logb, ← hLdef] at hbn
    rw [← le_div_iff₀ hlog2]
    calc (b.n : ℝ) ≤ C * (L / Real.log 2) := hbn
      _ = C * L / Real.log 2 := by ring
  have hside : Real.log b.side⁻¹ = b.n * Real.log 2 := by
    rw [show b.side⁻¹ = (2 : ℝ) ^ b.n by unfold DyBox.side; rw [inv_pow, inv_inv]]
    exact Real.log_pow _ _
  have hsq1 : Real.sqrt 8608 ≤ 93 := by
    calc Real.sqrt 8608 ≤ Real.sqrt (93 ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = 93 := Real.sqrt_sq (by norm_num)
  have hsq2 : Real.sqrt (Real.log b.side⁻¹ + 4) ≤ (C + 4) * u ^ 5 := by
    calc Real.sqrt (Real.log b.side⁻¹ + 4) ≤ Real.sqrt (((C + 4) * u ^ 5) ^ 2) := by
          apply Real.sqrt_le_sqrt
          rw [hside, show ((C + 4) * u ^ 5) ^ 2 = (C + 4) ^ 2 * L by rw [← hu10]; ring]
          have : (C + 4) * L ≤ (C + 4) ^ 2 * L :=
            mul_le_mul_of_nonneg_right (le_self_pow₀ (by linarith) (by norm_num)) hL0.le
          linarith
      _ = (C + 4) * u ^ 5 := Real.sqrt_sq (by positivity)
  have hE : γ * (α * Real.sqrt L * Real.log L) +
      γ ^ 2 / 2 * (2 * Real.sqrt 8608 * Real.sqrt (Real.log b.side⁻¹ + 4)) ≤
      γ * α * 10 * u ^ 6 + γ ^ 2 * 93 * (C + 4) * u ^ 5 := by
    have t1 : α * Real.sqrt L * Real.log L ≤ α * u ^ 5 * (10 * u) := by
      rw [hsqrt]; exact mul_le_mul_of_nonneg_left hlogL (mul_nonneg hα0.le (by positivity))
    have t2 : 2 * Real.sqrt 8608 * Real.sqrt (Real.log b.side⁻¹ + 4) ≤
        2 * 93 * ((C + 4) * u ^ 5) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hsq1 (by norm_num)) hsq2 (Real.sqrt_nonneg _)
        (by norm_num)
    have t1' := mul_le_mul_of_nonneg_left t1 hγ.le
    have t2' := mul_le_mul_of_nonneg_left t2 (show 0 ≤ γ ^ 2 / 2 by positivity)
    linarith
  have hsmall : δ ^ 2 * ((2 : ℝ)⁻¹ ^ (k + k'')) ^ 2 *
      Real.exp (γ * (α * Real.sqrt (Real.log δ⁻¹) * Real.log (Real.log δ⁻¹)) +
        γ ^ 2 / 2 * (2 * Real.sqrt 8608 * Real.sqrt (Real.log b.side⁻¹ + 4))) * Real.exp a <
      δ' ^ 2 := by
    have e1 : δ ^ 2 = Real.exp (2 * Real.log δ) := by rw [← exp_sq_eq, Real.exp_log hδ0]
    have e2 : δ' ^ 2 = Real.exp (2 * Real.log δ') := by rw [← exp_sq_eq, Real.exp_log hδ'0]
    rw [hinvτ, exp_sq_eq, e1, e2, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
      Real.exp_lt_exp, ← hLdef]
    have : 0 < u ^ 7 := by positivity
    linarith
  -- `hRs`
  have hRs : 2 * (((2 : ℝ)⁻¹ ^ (b.n + 2 * k) * Real.log (((2 : ℝ)⁻¹ ^ (b.n + 2 * k)) ^ 2)⁻¹ +
        2 * (2 : ℝ)⁻¹ ^ (b.n + 2 * k)) / 4) + 2 * (2 : ℝ)⁻¹ ^ (b.n + k + k'') ≤
      3 * (2 : ℝ)⁻¹ ^ (b.n + k) := by
    have hlg : Real.log (((2 : ℝ)⁻¹ ^ (b.n + 2 * k)) ^ 2)⁻¹ =
        2 * (((b.n : ℝ) + 2 * k) * Real.log 2) := by
      rw [inv_two_pow_eq_exp, exp_sq_eq, ← Real.exp_neg, Real.log_exp]; push_cast; ring
    have he : (2 : ℝ)⁻¹ ^ (b.n + 2 * k) = (2 : ℝ)⁻¹ ^ (b.n + k) * (2 : ℝ)⁻¹ ^ k := by
      rw [← pow_add]; congr 1; ring
    have h3 : (2 : ℝ)⁻¹ ^ (b.n + k + k'') ≤ (2 : ℝ)⁻¹ ^ (b.n + k) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have hnat : 2 * k + 1 ≤ h := by
      have := two_mul_add_le_pow (k - 5)
      rw [show k - 5 + 5 = k by omega, show k - 5 + 4 = k - 1 by omega] at this
      exact this
    have hnatR : 2 * (k : ℝ) + 1 ≤ h := by exact_mod_cast hnat
    have hk0 : (0 : ℝ) ≤ k := by positivity
    have hkey : ((b.n : ℝ) + 2 * k) * Real.log 2 + 1 ≤ 2 ^ k := by
      rw [hhR]; nlinarith [mul_le_mul_of_nonneg_left hlog2'.le hk0]
    set s := (2 : ℝ)⁻¹ ^ (b.n + k)
    set q := (2 : ℝ)⁻¹ ^ k
    have hq : q * 2 ^ k = 1 := pow_inv_mul_pow k
    have m1 : s * q * (((b.n : ℝ) + 2 * k) * Real.log 2 + 1) ≤ s * q * 2 ^ k :=
      mul_le_mul_of_nonneg_left hkey (by positivity)
    have m2 : s * q * 2 ^ k = s := by rw [mul_assoc, hq, mul_one]
    rw [hlg, he]
    linarith
  -- `θ`
  set ρ := Real.exp (-(u ^ 7 / 100)) with hρdef
  have h8 : 8 ≤ Real.exp (u ^ 7 / 200) := by
    have := Real.add_one_le_exp (u ^ 7 / 200); linarith
  have hρ8 : 8 * ρ ≤ Real.exp (-(u ^ 7 / 200)) := by
    rw [show -(u ^ 7 / 200) = u ^ 7 / 200 + -(u ^ 7 / 100) by ring, Real.exp_add]
    exact mul_le_mul_of_nonneg_right h8 (Real.exp_pos _).le
  have hρ2 : 8 * ρ ≤ 2⁻¹ := by
    have hm : Real.exp (-(u ^ 7 / 200)) ≤ 1 / 8 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]; norm_num; exact h8
    linarith
  have hθ : 8 * ENNReal.ofReal ρ ≤ 2⁻¹ := by
    rw [show (8 : ℝ≥0∞) = ENNReal.ofReal 8 by simp, ← ENNReal.ofReal_mul (by norm_num),
      show (2⁻¹ : ℝ≥0∞) = ENNReal.ofReal 2⁻¹ by rw [ENNReal.ofReal_inv_of_pos two_pos]; simp]
    exact ENNReal.ofReal_le_ofReal hρ2
  have hεθ : ENNReal.ofReal (8 * (2 ^ k'' + 2) * Real.exp (-a)) ≤
      ENNReal.ofReal ρ ^ ((3 + 1) ^ 2) := by
    rw [← ENNReal.ofReal_pow (Real.exp_pos _).le]
    apply ENNReal.ofReal_le_ofReal
    have hk''τ : (2 : ℝ) ^ k'' ≤ Real.exp τ := by
      rw [hτdef, ← two_pow_eq_exp]; exact pow_le_pow_right₀ (by norm_num) (by omega)
    have h1k : (1 : ℝ) ≤ 2 ^ k'' := one_le_pow₀ (by norm_num)
    have hy : 24 ≤ Real.exp (u ^ 7 / 25 - 6 / 5) := by
      have := Real.add_one_le_exp (u ^ 7 / 25 - 6 / 5); linarith
    calc 8 * (2 ^ k'' + 2) * Real.exp (-a) ≤ 24 * Real.exp τ * Real.exp (-a) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
      _ = 24 * Real.exp (-(τ / 5)) := by
          rw [mul_assoc, ← Real.exp_add, hadef]; congr 2; ring
      _ ≤ Real.exp (u ^ 7 / 25 - 6 / 5) * Real.exp (6 / 5 - u ^ 7 / 5) :=
          mul_le_mul hy (Real.exp_le_exp.2 (by linarith)) (Real.exp_pos _).le (Real.exp_pos _).le
      _ = ρ ^ ((3 + 1) ^ 2) := by
          rw [← Real.exp_add, hρdef, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  -- the final bound
  have hfinal : 4 * (((2 * (2 * h - 2) + 1 : ℕ) : ℝ≥0∞) *
      (8 * ENNReal.ofReal ρ) ^ ((2 * h - 2) - (h + 2) + 1)) ≤
      ENNReal.ofReal (δ ^ (10 * C + 10)) := by
    set m := (2 * h - 2) - (h + 2) + 1 with hmdef
    have hm : (m : ℝ) = h - 3 := by
      have : m = h - 3 := by omega
      rw [this, Nat.cast_sub (by omega)]; norm_num
    have hN : (((2 * (2 * h - 2) + 1 : ℕ)) : ℝ) ≤ 4 * h := by
      have : 2 * (2 * h - 2) + 1 ≤ 4 * h := by omega
      exact_mod_cast this
    have e8 : (8 : ℝ≥0∞) * ENNReal.ofReal ρ = ENNReal.ofReal (8 * ρ) := by
      rw [ENNReal.ofReal_mul (by norm_num)]; simp
    rw [e8, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity), show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp,
      ← ENNReal.ofReal_mul (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    have hpow : (8 * ρ) ^ m ≤ Real.exp (m * (-(u ^ 7 / 200))) := by
      rw [Real.exp_nat_mul]; exact pow_le_pow_left₀ (by positivity) hρ8 m
    have hexp10 : u ^ 20 / 2 ≤ Real.exp (u ^ 10) := by
      have := Real.pow_div_factorial_le_exp (u ^ 10) (by positivity) 2
      calc u ^ 20 / 2 = (u ^ 10) ^ 2 / (Nat.factorial 2) := by
            rw [Nat.factorial_two]; push_cast; ring
        _ ≤ _ := this
    have h4N : 4 * (((2 * (2 * h - 2) + 1 : ℕ)) : ℝ) ≤ Real.exp (u ^ 10) := by
      have : (h : ℝ) ≤ 2 * C * u ^ 10 := by rw [hu10]; linarith
      linarith
    have hhu : C * u ^ 10 < h := by rw [hu10]; exact hhCL
    have hp : (C * u ^ 10 - 3) * u ^ 7 ≤ ((h : ℝ) - 3) * u ^ 7 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    calc 4 * ((((2 * (2 * h - 2) + 1 : ℕ)) : ℝ) * (8 * ρ) ^ m) =
          (4 * (((2 * (2 * h - 2) + 1 : ℕ)) : ℝ)) * (8 * ρ) ^ m := by ring
      _ ≤ Real.exp (u ^ 10) * Real.exp (m * (-(u ^ 7 / 200))) :=
          mul_le_mul h4N hpow (by positivity) (Real.exp_pos _).le
      _ = Real.exp (u ^ 10 + m * (-(u ^ 7 / 200))) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (Real.log δ * (10 * C + 10)) := by
          rw [Real.exp_le_exp, hlogδ, hm, ← hu10]
          have e17 : u ^ 17 = u ^ 10 * u ^ 7 := by ring
          linarith
      _ = δ ^ (10 * C + 10) := (Real.rpow_def_of_pos hδ0 _).symm
  -- assembly
  have hm' : (2 : ℝ) ^ b.n ≤ δ ^ (-C) := by
    rw [two_pow_eq_exp, Real.rpow_def_of_pos hδ0, hlogδ, Real.exp_le_exp]; linarith
  have hjY : (2 : ℝ) ^ (2 * k) ≤ (α * Real.log δ⁻¹) ^ 2 := by
    rw [pow_mul', ← hLdef]
    refine pow_le_pow_left₀ (by positivity) (hkx.trans ?_) 2
    rw [hx]; exact mul_le_mul_of_nonneg_right hα.le hL0.le
  have core := l37_enc_core hW hγ (α := α) (δ := δ) (δ' := δ') (a := a) (B := b) (k := k)
    (k'' := k'') (h := h) hK h4 hb1 hm' hjY hkk hsmall hRs hθ hεθ
  refine le_trans (measure_mono ?_) (core.trans hfinal)
  exact inter_subset_inter_right _ (compl_subset_compl.2 (encEventPsi_mono hlam8))

end DZZ
end LQGMetric
