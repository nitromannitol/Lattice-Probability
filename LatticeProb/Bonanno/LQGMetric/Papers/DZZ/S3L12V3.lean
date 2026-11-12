/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L12V3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12V2

/-!
# DZZ Lemma 3.16, (eq-B-percolation), crossing form (D93, packet P-4, coarse form)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1365–1371 (statement), l. 1381–1397
(proof). The proof of `dzz_lemma316_perc` (S3L316P4: same parameters `ε = 2^{-k}`,
`t = ε* = 2^{-(k + k'')}`, `a = 1.2 log t⁻¹`, `θ = t^{1/100}`, same asymptotics, copied
verbatim), ending with the crossing form of the Peierls step `l316_cross_open` instead of
`l316_enc_open`, and keeping the coarse crossings (`HasCrossRing`) instead of passing to the
enclosure by `hasEnclosure_ring`.

* `dzz_lemma316_cross : DZZLemma316Cross P γ W`;
  `dzzLemma316Perc_of_cross` (S3L12V2) recovers `dzz_lemma316_perc`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

set_option maxHeartbeats 1000000 in
/-- **DZZ Lemma 3.16, (eq-B-percolation), crossing form** (l. 1369–1371, proof l. 1381–1397). -/
theorem dzz_lemma316_cross (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    DZZLemma316Cross P γ W := by
  have hC : 0 < dzzCmc γ := by have := l31theta_pos hγ hγ2; unfold dzzCmc; linarith
  refine ⟨4 * dzzCmc γ + 1, fun α hα => ⟨2 * γ * α + 1, fun αs hαs => ?_⟩⟩
  set C := dzzCmc γ with hCdef
  have hα4 : 4 * C < α := by linarith
  have hα0 : 0 < α := by linarith
  have hαs1 : 1 ≤ αs := by nlinarith
  set T0 := max 1400 (400 * (42 * C + 10) / C) with hT0
  set L₀ := max (max (8 / C) (Real.exp (125 * γ ^ 2 * (C + 4) + 1)))
    (max (T0 ^ 2) (5760 * C ^ 2 + 1)) with hL₀
  refine ⟨Real.exp (-L₀), Real.exp_pos _, ?_⟩
  rintro δ ⟨hδ0, hδ1⟩ b hb1 hbn
  set L := Real.log δ⁻¹ with hLdef
  have hlogδ : Real.log δ = -L := by rw [hLdef, Real.log_inv, neg_neg]
  have hL : L₀ < L := by
    have := Real.log_lt_log hδ0 hδ1
    rw [Real.log_exp] at this; linarith
  have hLe : Real.exp (125 * γ ^ 2 * (C + 4) + 1) < L :=
    lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hL
  have hL1 : 1 ≤ L := le_trans (Real.one_le_exp (by positivity)) hLe.le
  have hL0 : 0 < L := by linarith
  have hlogL : 125 * γ ^ 2 * (C + 4) + 1 < Real.log L := (Real.lt_log_iff_exp_lt hL0).2 hLe
  have hCL : 8 < C * L := by
    have h1 : 8 / C < L := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hL
    rwa [div_lt_iff₀ hC, mul_comm] at h1
  have hT0L : T0 ^ 2 < L := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hL
  have hCL2 : 5760 * C ^ 2 + 1 < L :=
    lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hL
  have hT00 : 0 ≤ T0 := le_trans (by norm_num) (le_max_left _ _)
  have hsqL : T0 ≤ Real.sqrt L := by
    calc T0 = Real.sqrt (T0 ^ 2) := (Real.sqrt_sq hT00).symm
      _ ≤ Real.sqrt L := Real.sqrt_le_sqrt hT0L.le
  have hsq0 : 0 < Real.sqrt L := Real.sqrt_pos.2 hL0
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2' : Real.log 2 < 1 := by have := Real.log_two_lt_d9; norm_num at this; linarith
  -- `k`: `2^k ≤ 4 C L < 2^{k+1}` (as in `dzz_lemma37_perc`)
  obtain ⟨k, hkdef⟩ : ∃ k, k = kL37 γ δ := ⟨_, rfl⟩
  set x := 4 * C * L with hx
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
  have hh2CL : (h : ℝ) ≤ 2 * C * L := by rw [hx] at hkx; linarith
  -- `t = ε* = 2^{-N}`, `τ = log t⁻¹`
  obtain ⟨N, hNdef⟩ : ∃ N, N = epsStarN αs δ := ⟨_, rfl⟩
  set τ := (N : ℝ) * Real.log 2 with hτdef
  have hτX : αs * Real.sqrt L * Real.log L ≤ τ := by
    have h1 := epsStar_le_thr αs δ
    rw [epsStar, epsStarThr, ← hNdef, inv_two_pow_eq_exp, Real.exp_le_exp, ← hLdef] at h1
    linarith
  have hγC : 0 ≤ γ ^ 2 * (C + 4) := by positivity
  have hlogL1 : 1 ≤ Real.log L := by linarith
  have hXs : Real.sqrt L ≤ αs * Real.sqrt L * Real.log L := by
    have := mul_le_mul hαs1 hlogL1 zero_le_one (by linarith)
    calc Real.sqrt L = Real.sqrt L * (1 * 1) := by ring
      _ ≤ Real.sqrt L * (αs * Real.log L) := mul_le_mul_of_nonneg_left this hsq0.le
      _ = αs * Real.sqrt L * Real.log L := by ring
  have hτT : T0 ≤ τ := hsqL.trans (hXs.trans hτX)
  have hτ1400 : 1400 ≤ τ := (le_max_left _ _).trans hτT
  have hCτ : 400 * (42 * C + 10) ≤ C * τ := by
    have := (le_max_right _ _).trans hτT
    rw [div_le_iff₀ hC] at this; linarith
  have h2N : (2 : ℝ) ^ N = Real.exp τ := two_pow_eq_exp N
  -- `2k ≤ N`
  have hkN : 2 * k ≤ N := by
    by_contra hc; push_neg at hc
    have h1 : (2 : ℝ) ^ (N + 1) ≤ 2 ^ (2 * k) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h2 : (2 : ℝ) ^ (2 * k) ≤ x ^ 2 := by
      rw [pow_mul']; exact pow_le_pow_left₀ (by positivity) hkx 2
    have h3 : Real.sqrt L ^ 6 / 720 ≤ Real.exp τ := by
      have := Real.pow_div_factorial_le_exp (Real.sqrt L) hsq0.le 6
      have e : (Nat.factorial 6 : ℝ) = 720 := by norm_num [Nat.factorial]
      rw [e] at this
      exact this.trans (Real.exp_le_exp.2 (hXs.trans hτX))
    have e6 : Real.sqrt L ^ 6 = L ^ 3 := by
      rw [show Real.sqrt L ^ 6 = (Real.sqrt L ^ 2) ^ 3 by ring, Real.sq_sqrt hL0.le]
    rw [e6] at h3
    have e2 : (2 : ℝ) ^ (N + 1) = 2 * Real.exp τ := by rw [pow_succ, h2N]; ring
    have h4' : L ^ 3 ≤ 5760 * C ^ 2 * L ^ 2 := by
      have : 2 * (L ^ 3 / 720) ≤ x ^ 2 := by linarith
      rw [hx] at this; linarith
    have : L ≤ 5760 * C ^ 2 := by
      have hL2 : 0 < L ^ 2 := by positivity
      refine le_of_mul_le_mul_right ?_ hL2
      have e3 : L * L ^ 2 = L ^ 3 := by ring
      rw [e3]; linarith
    linarith
  set k'' := N - k with hk''def
  have hkk : k ≤ k'' := by omega
  have hNk : k + k'' = N := by omega
  set a := 6 / 5 * τ with hadef
  have hinvτ : (2 : ℝ)⁻¹ ^ (k + k'') = Real.exp (-τ) := by rw [hNk]; exact inv_two_pow_eq_exp _
  -- `hsmall` (with `δ' = δ`)
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
  have hsq2 : Real.sqrt (Real.log b.side⁻¹ + 4) ≤ (C + 4) * Real.sqrt L := by
    calc Real.sqrt (Real.log b.side⁻¹ + 4) ≤ Real.sqrt (((C + 4) * Real.sqrt L) ^ 2) := by
          apply Real.sqrt_le_sqrt
          rw [hside, mul_pow, Real.sq_sqrt hL0.le]
          have : (C + 4) * L ≤ (C + 4) ^ 2 * L :=
            mul_le_mul_of_nonneg_right (le_self_pow₀ (by linarith) (by norm_num)) hL0.le
          linarith
      _ = (C + 4) * Real.sqrt L := Real.sqrt_sq (by positivity)
  have hE : γ * (α * Real.sqrt L * Real.log L) +
      γ ^ 2 / 2 * (2 * Real.sqrt 8608 * Real.sqrt (Real.log b.side⁻¹ + 4)) ≤
      γ * α * Real.sqrt L * Real.log L + γ ^ 2 * 93 * (C + 4) * Real.sqrt L := by
    have t2 : 2 * Real.sqrt 8608 * Real.sqrt (Real.log b.side⁻¹ + 4) ≤
        2 * 93 * ((C + 4) * Real.sqrt L) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hsq1 (by norm_num)) hsq2 (Real.sqrt_nonneg _)
        (by norm_num)
    have t2' := mul_le_mul_of_nonneg_left t2 (show 0 ≤ γ ^ 2 / 2 by positivity)
    linarith
  have hτbig : γ * α * Real.sqrt L * Real.log L + γ ^ 2 * 93 * (C + 4) * Real.sqrt L <
      4 / 5 * τ := by
    have p1 : γ ^ 2 * 93 * (C + 4) * Real.sqrt L < 4 / 5 * (Real.sqrt L * Real.log L) := by
      have : γ ^ 2 * 93 * (C + 4) < 4 / 5 * Real.log L := by linarith
      have := mul_lt_mul_of_pos_right this hsq0
      linarith
    have p2 : (2 * γ * α + 1) * (Real.sqrt L * Real.log L) ≤ αs * (Real.sqrt L * Real.log L) :=
      mul_le_mul_of_nonneg_right hαs (by positivity)
    have e : αs * Real.sqrt L * Real.log L = αs * (Real.sqrt L * Real.log L) := by ring
    have p3 : 0 ≤ γ * α * (Real.sqrt L * Real.log L) := by positivity
    linarith
  have hsmall : δ ^ 2 * ((2 : ℝ)⁻¹ ^ (k + k'')) ^ 2 *
      Real.exp (γ * (α * Real.sqrt (Real.log δ⁻¹) * Real.log (Real.log δ⁻¹)) +
        γ ^ 2 / 2 * (2 * Real.sqrt 8608 * Real.sqrt (Real.log b.side⁻¹ + 4))) * Real.exp a <
      δ ^ 2 := by
    rw [hinvτ, exp_sq_eq, ← hLdef]
    have key : Real.exp (2 * -τ) * Real.exp (γ * (α * Real.sqrt L * Real.log L) +
        γ ^ 2 / 2 * (2 * Real.sqrt 8608 * Real.sqrt (Real.log b.side⁻¹ + 4))) *
        Real.exp a < 1 := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_zero, Real.exp_lt_exp]; linarith
    calc _ = δ ^ 2 * (Real.exp (2 * -τ) * Real.exp (γ * (α * Real.sqrt L * Real.log L) +
          γ ^ 2 / 2 * (2 * Real.sqrt 8608 * Real.sqrt (Real.log b.side⁻¹ + 4))) *
          Real.exp a) := by ring
      _ < δ ^ 2 * 1 := mul_lt_mul_of_pos_left key (by positivity)
      _ = δ ^ 2 := mul_one _
  -- `hRs` (as in `dzz_lemma37_perc`)
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
      rw [hhR]; linarith [mul_le_mul_of_nonneg_left hlog2'.le hk0]
    set s := (2 : ℝ)⁻¹ ^ (b.n + k)
    set q := (2 : ℝ)⁻¹ ^ k
    have hq : q * 2 ^ k = 1 := pow_inv_mul_pow k
    have m1 : s * q * (((b.n : ℝ) + 2 * k) * Real.log 2 + 1) ≤ s * q * 2 ^ k :=
      mul_le_mul_of_nonneg_left hkey (by positivity)
    have m2 : s * q * 2 ^ k = s := by rw [mul_assoc, hq, mul_one]
    rw [hlg, he]
    linarith
  -- `θ = e^{-τ/100}`
  set ρ := Real.exp (-(τ / 100)) with hρdef
  have h8 : 8 ≤ Real.exp (τ / 200) := by
    have := Real.add_one_le_exp (τ / 200); linarith
  have hρ8 : 8 * ρ ≤ Real.exp (-(τ / 200)) := by
    rw [show -(τ / 200) = τ / 200 + -(τ / 100) by ring, Real.exp_add]
    exact mul_le_mul_of_nonneg_right h8 (Real.exp_pos _).le
  have hρ2 : 8 * ρ ≤ 2⁻¹ := by
    have hm : Real.exp (-(τ / 200)) ≤ 1 / 8 := by
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
      rw [← h2N]; exact pow_le_pow_right₀ (by norm_num) (by omega)
    have h1k : (1 : ℝ) ≤ 2 ^ k'' := one_le_pow₀ (by norm_num)
    have hy : 24 ≤ Real.exp (τ / 25) := by
      have := Real.add_one_le_exp (τ / 25); linarith
    calc 8 * (2 ^ k'' + 2) * Real.exp (-a) ≤ 24 * Real.exp τ * Real.exp (-a) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
      _ = 24 * Real.exp (-(τ / 5)) := by
          rw [mul_assoc, ← Real.exp_add, hadef]; congr 2; ring
      _ ≤ Real.exp (τ / 25) * Real.exp (-(τ / 5)) :=
          mul_le_mul_of_nonneg_right hy (Real.exp_pos _).le
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
    have e8 : (8 : ℝ≥0∞) * ENNReal.ofReal ρ = ENNReal.ofReal (8 * ρ) := by
      rw [ENNReal.ofReal_mul (by norm_num)]; simp
    rw [e8, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity), show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp,
      ← ENNReal.ofReal_mul (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    have hpow : (8 * ρ) ^ m ≤ Real.exp (m * (-(τ / 200))) := by
      rw [Real.exp_nat_mul]; exact pow_le_pow_left₀ (by positivity) hρ8 m
    have hN : (((2 * (2 * h - 2) + 1 : ℕ)) : ℝ) ≤ 4 * h := by
      have : 2 * (2 * h - 2) + 1 ≤ 4 * h := by omega
      exact_mod_cast this
    have h4N : 4 * (((2 * (2 * h - 2) + 1 : ℕ)) : ℝ) ≤ Real.exp (32 * C * L) := by
      have := Real.add_one_le_exp (32 * C * L)
      linarith
    have hmτ : C * L / 2 * τ ≤ (m : ℝ) * τ := by
      refine mul_le_mul_of_nonneg_right ?_ (by linarith)
      rw [hm]; linarith
    have hLτ : L * (400 * (42 * C + 10)) / 2 ≤ C * L / 2 * τ := by
      have := mul_le_mul_of_nonneg_left hCτ hL0.le
      linarith
    calc 4 * ((((2 * (2 * h - 2) + 1 : ℕ)) : ℝ) * (8 * ρ) ^ m) =
          (4 * (((2 * (2 * h - 2) + 1 : ℕ)) : ℝ)) * (8 * ρ) ^ m := by ring
      _ ≤ Real.exp (32 * C * L) * Real.exp (m * (-(τ / 200))) :=
          mul_le_mul h4N hpow (by positivity) (Real.exp_pos _).le
      _ = Real.exp (32 * C * L + m * (-(τ / 200))) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (Real.log δ * (10 * C + 10)) := by
          rw [Real.exp_le_exp, hlogδ]
          linarith
      _ = δ ^ (10 * C + 10) := (Real.rpow_def_of_pos hδ0 _).symm
  -- assembly
  have hm' : (2 : ℝ) ^ b.n ≤ δ ^ (-C) := by
    rw [two_pow_eq_exp, Real.rpow_def_of_pos hδ0, hlogδ, Real.exp_le_exp]; linarith
  have hjY : (2 : ℝ) ^ (2 * k) ≤ (α * Real.log δ⁻¹) ^ 2 := by
    rw [pow_mul', ← hLdef]
    refine pow_le_pow_left₀ (by positivity) (hkx.trans ?_) 2
    rw [hx]; exact mul_le_mul_of_nonneg_right hα4.le hL0.le
  have core := l316_cross_open (P := P) hW γ a (B := b) (k'' := k'') hK h4 hb1 hRs hθ hεθ
  have hdec0 : P (decompEvent W)ᶜ = 0 := by
    have := ae_iff.1 (ae_decompEvent (P := P) hW)
    simpa [compl_def] using this
  refine (measure_mono (t := (decompEvent W)ᶜ ∪
    {ω | ¬ HasCross b k fun b' => ω ∈ boxOpen γ W b' k'' (b.n + 2 * k) a}) ?_).trans ?_
  · rintro ω ⟨⟨hM, hEv⟩, hnot⟩
    by_cases hdec : ω ∈ decompEvent W
    · right
      intro hcr
      apply hnot
      refine ⟨k, k'', ?_, hasCross_mono' (fun b' hb' hop =>
        approxLQG_lt_of_boxOpen hW hγ hEv.2 hdec hm' hjY (by omega) hM hb' hop hsmall) hcr⟩
      rw [← hNdef, ← hNk]
    · left; exact hdec
  · refine (measure_union_le _ _).trans ?_
    rw [hdec0, zero_add]
    exact core.trans hfinal

end DZZ
end LQGMetric
