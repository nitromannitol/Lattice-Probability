/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3Eta8 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3Eta7
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L7FinAsym

/-!
# `L32CellCompareBox` from the comparison with `M̃_{γ,ε²s',η}` (P2-DZZETA)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1183–1206), with DZZ's parameters:
`ε = 2^{-kL37} = max{2^{-n} : 2^n ≤ 4 C_mc log δ⁻¹}` (l. 1185, `K = 1/ε = 2 kP32`),
`β = e^{-(log δ⁻¹)^{0.7}}` (l. 1202), `δ' = δ e^{(log δ⁻¹)^{0.8}}`.

* `L32TildeMLower P γ W ν`: DZZ l. 1193–1195 on a high-probability event (`Ẽ_{δ,α} ∩ Ẽ_{δ',α}`),
  for some `α`, for the squares `S̃_{i_j}` of every `S ∈ 𝒮_B` inside `𝕍`, `s ≥ δ'^{C_mc}`.
* `p32Eta_asymp`: DZZ's parameter inequalities for small `δ` (`u = (log δ⁻¹)^{1/10}`, as
  `l37_ev`): `β ≤ 1/2`, `β C ≤ 1`, l. 1200 (`16·1024² δ² ≤ β² e^{-2αγ√L log L} δ'²`), l. 1197
  (`ε² s' log(1/(ε² s')) < ε s'`, with `+1`), and the tail `2^{k²}(β C)^{⌊k²/2⌋} ≤ e^{-(2 C_Mc L)²}`
  (own elementary estimates).
* **`l32CellCompareBox_of_lower`**: `L32TildeMLower P γ W ν → L32CellCompareBox P γ W ν`;
  `l32BallCover_dzzMuIn_of_lower`: with P2-DZZ97A, `L32TildeMLower P γ W (wickQArea γ W)` gives
  `L32BallCover P γ W (dzzMuIn γ W)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal NNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- `K/2 = 1/(2ε)`: the number of squares `S̃_{i_j}` per side -/
def kP32 (γ δ : ℝ) : ℕ := 2 ^ (kL37 γ δ - 1)

/-- **DZZ l. 1193–1195** (comparison of `M` with `M̃_{γ,ε²s',η}` on `S̃_{i_j}`) on a
high-probability event, for all boxes of side `≥ δ'^{C_mc}` and squares of `𝒮_B` in `𝕍` -/
def L32TildeMLower (P : Measure Ω) (γ : ℝ) (W : WNSpace → Ω → ℝ) (ν : Ω → Measure ℂ) : Prop :=
  ∃ α : ℝ, ∃ G : ℝ → Set Ω, HighProb P G ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
    ∀ (B : DyBox) (a b : ℕ), a < 4096 → b < 4096 → p32Up δ ^ dzzCmc γ ≤ B.side →
      sqSB B a b ⊆ dzzV →
        L32TildeMLowerBox γ W ν (G δ) B a b (kP32 γ δ) (p32Up δ ^ 2)
          (Real.exp (-(2 * α * γ * Real.sqrt (Real.log δ⁻¹) * Real.log (Real.log δ⁻¹))))

lemma log_le_div_eight {x : ℝ} (hx : 64 ≤ x) : Real.log x ≤ x / 8 := by
  have hx0 : 0 < x := by linarith
  have h1 := Real.log_le_sub_one_of_pos (show 0 < x / 64 by positivity)
  rw [Real.log_div hx0.ne' (by norm_num)] at h1
  have h2 : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]; norm_num
  have h3 := Real.log_two_lt_d9
  linarith

lemma kP32_facts {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {δ : ℝ} (hL : 33 ≤ Real.log δ⁻¹) :
    (2 * (kP32 γ δ : ℝ)) = (2 : ℝ) ^ kL37 γ δ ∧
      2 * dzzCmc γ * Real.log δ⁻¹ < (2 : ℝ) ^ kL37 γ δ ∧ 64 ≤ (2 : ℝ) ^ kL37 γ δ := by
  have hCm1 : 1 ≤ dzzCmc γ := by have := l31theta_pos hγ hγ2; unfold dzzCmc; linarith
  set L := Real.log δ⁻¹
  set N := ⌊4 * dzzCmc γ * L⌋₊ with hN_def
  have hnN : kL37 γ δ = Nat.log 2 N := rfl
  set n := kL37 γ δ
  have hN2 : 2 ≤ N := Nat.le_floor (by push_cast; nlinarith)
  have hn1 : 1 ≤ n := by rw [hnN]; exact Nat.log_pos (by norm_num) hN2
  have hKgt : 2 * dzzCmc γ * L < (2 : ℝ) ^ n := by
    have h := Nat.lt_pow_succ_log_self (show 1 < 2 by norm_num) N
    rw [← hnN] at h
    have h' : ((N + 1 : ℕ) : ℝ) ≤ ((2 ^ (n + 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt h
    push_cast at h'
    have hf := Nat.lt_floor_add_one (4 * dzzCmc γ * L)
    rw [pow_succ] at h'
    linarith
  refine ⟨?_, hKgt, by nlinarith⟩
  simp only [kP32]; push_cast
  rw [← pow_succ', Nat.sub_add_cancel hn1]

/-- DZZ l. 1197 (finite range), with `+1` (own elementary estimate) -/
lemma range_asymp {K L Cm s δ' δ : ℝ} (hK64 : 64 ≤ K) (hKgt : 2 * Cm * L < K) (hCm : 0 < Cm)
    (hδ0 : 0 < δ) (hL : L = Real.log δ⁻¹) (hδ'δ : δ ≤ δ') (hs : δ' ^ Cm ≤ s) (hs1 : s ≤ 1) :
    s / 1024 / K ^ 2 ≤ 1 ∧
      s / 1024 / K ^ 2 * (Real.log (s / 1024 / K ^ 2)⁻¹ + 1) < s / 1024 / K := by
  have hδ'0 : 0 < δ' := hδ0.trans_le hδ'δ
  have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs
  have hK0 : 0 < K := by linarith
  refine ⟨by rw [div_le_one (by positivity)]; nlinarith, ?_⟩
  set δh := s / 1024 / K ^ 2
  have hδh0 : 0 < δh := by positivity
  have hlogs : Real.log s⁻¹ ≤ Cm * L := by
    have h1 := Real.log_le_log (by positivity) hs
    rw [Real.log_rpow hδ'0] at h1
    have h2 := mul_le_mul_of_nonneg_left (Real.log_le_log hδ0 hδ'δ) hCm.le
    rw [Real.log_inv, hL, Real.log_inv]
    linarith
  have hlogK := log_le_div_eight hK64
  have hlog1024 : Real.log 1024 ≤ 7 := by
    rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]
    have := Real.log_two_lt_d9
    norm_num at this ⊢
    linarith
  have hδhinv : Real.log δh⁻¹ = Real.log 1024 + 2 * Real.log K + Real.log s⁻¹ := by
    simp only [δh]
    rw [show (s / 1024 / K ^ 2)⁻¹ = 1024 * K ^ 2 * s⁻¹ by field_simp,
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
      Real.log_pow]
    push_cast; ring
  have hlt : Real.log δh⁻¹ + 1 < K := by rw [hδhinv]; linarith
  have : s / 1024 / K = δh * K := by simp only [δh]; field_simp
  rw [this]
  exact mul_lt_mul_of_pos_left hlt hδh0

/-- DZZ l. 1200 (own elementary estimate, `u = (log δ⁻¹)^{1/10}`) -/
lemma ratio_asymp {u L α γ δ : ℝ} (hγ : 0 < γ) (hu1 : 1 ≤ u) (hLu : L = u ^ 10)
    (h4 : Real.log (16 * 1024 ^ 2) ≤ u ^ 8) (h5 : 2 * u ^ 7 ≤ 1 / 2 * u ^ 8)
    (h6 : 20 * |α| * γ * u ^ 6 ≤ 1 / 2 * u ^ 8) :
    16 * 1024 ^ 2 * δ ^ 2 ≤ Real.exp (-u ^ 7) ^ 2 *
      Real.exp (-(2 * α * γ * u ^ 5 * Real.log L)) * (δ * Real.exp (u ^ 8)) ^ 2 := by
  have hu0 : 0 ≤ u := by linarith
  have hlogL : Real.log L ≤ 10 * u := by
    rw [hLu, Real.log_pow]
    have := Real.log_le_sub_one_of_pos (show 0 < u by linarith)
    push_cast; linarith
  have hlogL0 : 0 ≤ Real.log L := Real.log_nonneg (by rw [hLu]; exact one_le_pow₀ hu1)
  have hαb : 2 * α * γ * u ^ 5 * Real.log L ≤ 20 * |α| * γ * u ^ 6 := by
    have h1 : α * Real.log L ≤ |α| * (10 * u) :=
      (mul_le_mul_of_nonneg_right (le_abs_self α) hlogL0).trans
        (mul_le_mul_of_nonneg_left hlogL (abs_nonneg α))
    have hγu : 0 ≤ 2 * γ * u ^ 5 := by positivity
    calc 2 * α * γ * u ^ 5 * Real.log L = (2 * γ * u ^ 5) * (α * Real.log L) := by ring
      _ ≤ (2 * γ * u ^ 5) * (|α| * (10 * u)) := mul_le_mul_of_nonneg_left h1 hγu
      _ = 20 * |α| * γ * u ^ 6 := by ring
  have key : Real.exp (-u ^ 7) ^ 2 * Real.exp (-(2 * α * γ * u ^ 5 * Real.log L)) *
      (δ * Real.exp (u ^ 8)) ^ 2 =
      δ ^ 2 * Real.exp (2 * u ^ 8 + (2 * (-u ^ 7) + -(2 * α * γ * u ^ 5 * Real.log L))) := by
    rw [mul_pow, exp_sq_eq, exp_sq_eq, Real.exp_add, Real.exp_add]; ring
  rw [key, mul_comm (16 * 1024 ^ 2 : ℝ) (δ ^ 2)]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg δ)
  calc (16 : ℝ) * 1024 ^ 2 = Real.exp (Real.log (16 * 1024 ^ 2)) :=
        (Real.exp_log (by norm_num)).symm
    _ ≤ _ := Real.exp_le_exp.2 (by linarith)

/-- the binomial tail `2^{k²} (β C)^{⌊k²/2⌋} ≤ e^{-(2 C_Mc L)²}` (own elementary estimate) -/
lemma tail_asymp {u L CM bC : ℝ} {k : ℕ} (hu7 : 8 ≤ u ^ 7) (hL2 : 2 ≤ L) (hkL : L ≤ k)
    (hCM0 : 0 < CM) (hCM5 : CM ≤ 1 / 5) (hbC0 : 0 ≤ bC) (hbC : bC ≤ Real.exp (-(u ^ 7 / 2))) :
    (2 : ℝ) ^ (k * k) * bC ^ (k * k / 2) ≤ Real.exp (-(2 * CM * L) ^ 2) := by
  set m := k * k / 2
  have hm : ((k : ℝ) ^ 2) - 1 ≤ 2 * m := by
    have : k * k ≤ 2 * m + 1 := by omega
    have : ((k * k : ℕ) : ℝ) ≤ 2 * (m : ℝ) + 1 := by exact_mod_cast this
    push_cast at this; nlinarith
  have hpow : bC ^ m ≤ Real.exp (-(u ^ 7 / 2)) ^ m := pow_le_pow_left₀ hbC0 hbC m
  have h2 : (2 : ℝ) ^ (k * k) ≤ Real.exp ((k : ℝ) ^ 2) := by
    rw [← Real.exp_one_rpow, ← Real.rpow_natCast]
    have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    refine (Real.rpow_le_rpow (x := 2) (y := Real.exp 1) (z := ((k * k : ℕ) : ℝ)) (by norm_num)
      he (by positivity)).trans (le_of_eq ?_)
    push_cast; ring_nf
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have h3 : 4 * (m : ℝ) ≤ u ^ 7 / 2 * m := by nlinarith
  calc (2 : ℝ) ^ (k * k) * bC ^ m ≤ Real.exp ((k : ℝ) ^ 2) * Real.exp (-(u ^ 7 / 2)) ^ m :=
        mul_le_mul h2 hpow (by positivity) (by positivity)
    _ = Real.exp ((k : ℝ) ^ 2 - u ^ 7 / 2 * m) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; ring_nf
    _ ≤ _ := Real.exp_le_exp.2 (by
        have hk2 : L ^ 2 ≤ (k : ℝ) ^ 2 := pow_le_pow_left₀ (by linarith) hkL 2
        have hCMs : CM * CM ≤ 1 / 25 := by nlinarith
        have hCM2 : (2 * CM * L) ^ 2 ≤ 4 / 25 * L ^ 2 := by
          have : 0 ≤ (1 / 25 - CM * CM) * L ^ 2 := mul_nonneg (by linarith) (sq_nonneg L)
          nlinarith
        have hL4 : 4 ≤ L ^ 2 := by nlinarith
        linarith)

/-- DZZ's parameter inequalities (own elementary estimates) -/
theorem p32Eta_asymp {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (α C' : ℝ) (hC' : 0 ≤ C') :
    ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₁,
      Real.exp (-(Real.log δ⁻¹ ^ (0.7 : ℝ))) ≤ 2⁻¹ ∧
      Real.exp (-(Real.log δ⁻¹ ^ (0.7 : ℝ))) * C' ≤ 1 ∧
      16 * 1024 ^ 2 * δ ^ 2 ≤ Real.exp (-(Real.log δ⁻¹ ^ (0.7 : ℝ))) ^ 2 *
        Real.exp (-(2 * α * γ * Real.sqrt (Real.log δ⁻¹) * Real.log (Real.log δ⁻¹))) *
          p32Up δ ^ 2 ∧
      (∀ s : ℝ, p32Up δ ^ dzzCmc γ ≤ s → s ≤ 1 →
        s / 1024 / (2 * (kP32 γ δ : ℝ)) ^ 2 ≤ 1 ∧
        s / 1024 / (2 * (kP32 γ δ : ℝ)) ^ 2 *
            (Real.log (s / 1024 / (2 * (kP32 γ δ : ℝ)) ^ 2)⁻¹ + 1) <
          s / 1024 / (2 * (kP32 γ δ : ℝ))) ∧
      2 ^ (kP32 γ δ * kP32 γ δ) *
          (Real.exp (-(Real.log δ⁻¹ ^ (0.7 : ℝ))) * C') ^ (kP32 γ δ * kP32 γ δ / 2) ≤
        Real.exp (-(2 * dzzCMc γ * Real.log δ⁻¹) ^ 2) := by
  have hCm1 : 1 ≤ dzzCmc γ := by have := l31theta_pos hγ hγ2; unfold dzzCmc; linarith
  have hCM5 : dzzCMc γ ≤ 1 / 5 := by
    unfold dzzCMc; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have e1 := ev_pow_le (show (0 : ℝ) < 1 by norm_num) 33 (show 0 < 10 by norm_num)
  have e2 := ev_pow_le (show (0 : ℝ) < 1 by norm_num) 8 (show 0 < 7 by norm_num)
  have e3 := ev_pow_le (show (0 : ℝ) < 1 / 2 by norm_num) (Real.log (C' + 1))
    (show 0 < 7 by norm_num)
  have e4 := ev_pow_le (show (0 : ℝ) < 1 by norm_num)
    (Real.log (16 * 1024 ^ 2)) (show 0 < 8 by norm_num)
  have e5 := ev_pow_le (show (0 : ℝ) < 1 / 2 by norm_num) 2 (show 7 < 8 by norm_num)
  have e6 := ev_pow_le (show (0 : ℝ) < 1 / 2 by norm_num) (20 * |α| * γ)
    (show 6 < 8 by norm_num)
  obtain ⟨U₀, hU₀⟩ := eventually_atTop.1 (e1.and (e2.and (e3.and (e4.and (e5.and e6)))))
  set U := max U₀ 1
  refine ⟨Real.exp (-(U ^ 10)), Real.exp_pos _, fun δ hδ => ?_⟩
  obtain ⟨hδ0, hδ1⟩ := hδ
  set L := Real.log δ⁻¹ with hL_def
  have hU1 : 1 ≤ U := le_max_right _ _
  have hLU : U ^ 10 < L := by
    rw [hL_def, Real.log_inv, lt_neg]
    exact (Real.log_lt_log_iff hδ0 (Real.exp_pos _)).2 hδ1 |>.trans_eq (Real.log_exp _)
  have hL0 : 0 < L := lt_of_le_of_lt (by positivity) hLU
  set u := L ^ ((1 : ℝ) / 10) with hu_def
  have hu0 : 0 ≤ u := by positivity
  have hLu : L = u ^ 10 := by
    rw [hu_def, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
  have hUu : U ≤ u := by
    by_contra hc
    have : u ^ 10 < U ^ 10 := pow_lt_pow_left₀ (lt_of_not_ge hc) hu0 (by norm_num)
    linarith
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hU₀ u ((le_max_left _ _).trans hUu)
  simp only [pow_zero, mul_one, one_mul] at h1 h2 h3 h4
  have hu1 : 1 ≤ u := hU1.trans hUu
  have h07 : L ^ (0.7 : ℝ) = u ^ 7 := by
    rw [hLu, ← Real.rpow_natCast, ← Real.rpow_mul hu0, ← Real.rpow_natCast]; norm_num
  have h08 : L ^ (0.8 : ℝ) = u ^ 8 := by
    rw [hLu, ← Real.rpow_natCast, ← Real.rpow_mul hu0, ← Real.rpow_natCast]; norm_num
  have hsq : Real.sqrt L = u ^ 5 := by
    rw [hLu, show u ^ 10 = (u ^ 5) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hL33 : 33 ≤ L := by rw [hLu]; linarith
  obtain ⟨hk2, hKgt, hK64⟩ := kP32_facts hγ hγ2 hL33
  have hβC : Real.exp (-(L ^ (0.7 : ℝ))) * C' ≤ Real.exp (-(u ^ 7 / 2)) := by
    have hC'' : C' ≤ Real.exp (u ^ 7 / 2) := by
      have hC1 : C' + 1 ≤ Real.exp (u ^ 7 / 2) := by
        rw [← Real.log_le_iff_le_exp (by linarith)]; linarith
      linarith
    calc Real.exp (-(L ^ (0.7 : ℝ))) * C' ≤ Real.exp (-(L ^ (0.7 : ℝ))) * Real.exp (u ^ 7 / 2) :=
          mul_le_mul_of_nonneg_left hC'' (Real.exp_pos _).le
      _ = Real.exp (-(u ^ 7 / 2)) := by rw [h07, ← Real.exp_add]; ring_nf
  have hu7 : 1 ≤ u ^ 7 := one_le_pow₀ hu1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h07]
    calc Real.exp (-(u ^ 7)) ≤ Real.exp (-1) := Real.exp_le_exp.2 (by linarith)
      _ ≤ 2⁻¹ := by have := Real.exp_neg_one_lt_half; norm_num at this ⊢; linarith
  · exact hβC.trans (by rw [Real.exp_le_one_iff]; linarith)
  · have hp : p32Up δ = δ * Real.exp (u ^ 8) := by rw [p32Up, ← hL_def, h08]
    rw [hp, hsq, h07]
    exact ratio_asymp hγ hu1 hLu h4 h5 h6
  · intro s hs hs1
    rw [hk2]
    refine range_asymp hK64 hKgt (by linarith) hδ0 hL_def ?_ hs hs1
    unfold p32Up; exact le_mul_of_one_le_right hδ0.le (Real.one_le_exp (by positivity))
  · have hkL : L ≤ (kP32 γ δ : ℝ) := by nlinarith
    exact tail_asymp (by linarith) (by linarith) hkL (dzzCMc_pos γ) hCM5
      (mul_nonneg (Real.exp_pos _).le hC') hβC

/-- **DZZ (Eq.LD-lowerbound-approx-LGD) from the comparison** -/
theorem l32CellCompareBox_of_lower (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {ν : Ω → Measure ℂ} (h : L32TildeMLower P γ W ν) : L32CellCompareBox P γ W ν := by
  obtain ⟨α, G, hG, δ₀, hδ₀, hcomp⟩ := h
  obtain ⟨C, hC, hbox⟩ := measure_cellCompare_le_of_lower (P := P) hW hγ hγ2
  obtain ⟨δ₁, hδ₁, hev⟩ := p32Eta_asymp hγ hγ2 α C.toReal ENNReal.toReal_nonneg
  refine ⟨G, hG, min δ₀ δ₁, lt_min hδ₀ hδ₁, fun δ hδ B a b ha hb hs hSV => ?_⟩
  have hδ0 : δ ∈ Ioo (0 : ℝ) δ₀ := ⟨hδ.1, hδ.2.trans_le (min_le_left _ _)⟩
  obtain ⟨c1, c2, c3, c4, c5⟩ := hev δ ⟨hδ.1, hδ.2.trans_le (min_le_right _ _)⟩
  have hside1 : B.side ≤ 1 := by
    unfold DyBox.side; exact pow_le_one₀ (by norm_num) (by norm_num)
  obtain ⟨c41, c42⟩ := c4 B.side hs hside1
  have hβC : ENNReal.ofReal (Real.exp (-(Real.log δ⁻¹ ^ (0.7 : ℝ)))) * C =
      ENNReal.ofReal (Real.exp (-(Real.log δ⁻¹ ^ (0.7 : ℝ))) * C.toReal) := by
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_toReal hC]
  have hδ'0 : 0 < p32Up δ := by unfold p32Up; exact mul_pos hδ.1 (Real.exp_pos _)
  refine (hbox ν (G δ) B a b (kP32 γ δ) δ (p32Up δ ^ 2) _ _ (Nat.one_le_two_pow) (by positivity)
    (Real.exp_pos _) (Real.exp_pos _) c1 (by rw [hβC]; exact ENNReal.ofReal_le_one.2 c2) c3 c41 c42
    (hcomp δ hδ0 B a b ha hb hs hSV)).trans ?_
  rw [hβC, ← ENNReal.ofReal_pow (by positivity),
    show (2 : ℝ≥0∞) ^ (kP32 γ δ * kP32 γ δ) = ENNReal.ofReal (2 ^ (kP32 γ δ * kP32 γ δ)) by
      rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat],
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal c5

/-- **P-3 of D97 from the comparison**: `L32TildeMLower` at `M^W` gives (eq-Euclidean-Ball-covering)
for `μIn` (`l32BallCover_dzzMuIn_of_box`, P2-DZZ97A) -/
theorem l32BallCover_dzzMuIn_of_lower (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) (h : L32TildeMLower P γ W (wickQArea γ W)) :
    L32BallCover P γ W (dzzMuIn γ W) :=
  l32BallCover_dzzMuIn_of_box hW hγ hγ2 (l32CellCompareBox_of_lower hW hγ hγ2 h)

end DZZ
end LQGMetric
