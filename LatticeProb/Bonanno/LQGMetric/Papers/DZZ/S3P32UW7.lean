/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32UW7 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32UW6

/-!
# Walled (Eq.boundDprime), UW7: `L32EncPhiHPWOn` at `dzzWall B̄w μIn`, the union over the cells
(P2-DZZUPW, packet P-317K-UP)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1088–1094, 1104–1147) with Remark 5.2: copy of
`l32EncPhiHPW_dzzMuIn` (S3P32F4, P2-DZZ32F) for the cells `wEmb Bw b` inside the wall, from the
walled one-box bound `p32_enc_percW` (S3P32UW6); the union is over the pulled-back levels
`1 ≤ n ≤ ⌊C_mc log₂ δ⁻¹⌋ − n_{Bw}` (`n ≥ 1` since `δ^{C_Mc} < s_{Bw}`). Result:
**`l32EncPhiHPWOn_dzzMuIn : L32EncPhiHPWOn P γ W (dzzWall B̄w μIn) Bw (rP32 γ)`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

universe u

/-- **Walled DZZ (eq-B-percolation-Psi) + union over the cells inside the wall** (copy of
`l32EncPhiHPW_dzzMuIn`). -/
theorem l32EncPhiHPWOn_dzzMuIn {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (Bw : DyBox) :
    L32EncPhiHPWOn P γ W (fun ω => dzzWall Bw.closedBox (dzzMuIn γ W ω)) Bw (rP32 γ) := by
  have := hW.isProbabilityMeasure
  obtain ⟨α, G, hG, δ₀, hδ₀, hup⟩ := l32TildeMUpper_wickQArea (P := P) hW hγ hγ2
  obtain ⟨δ₁, hδ₁, hperc⟩ := p32_enc_percW hW hγ hγ2 α G hδ₀ Bw hup
  set C := dzzCmc γ with hCdef
  have hC : 0 < C := by have := l31theta_pos hγ hγ2; rw [hCdef]; unfold dzzCmc; linarith
  set Bad : ℝ → DyBox → Set Ω := fun δ b => {ω | approxLQG γ W ω (wEmb Bw b) ≤ δ ^ 2} ∩ G δ ∩
    {ω | ¬ HasEnclosure b (kL37 γ δ) fun b' =>
      PhiLeW (wPullMeas Bw (dzzWall Bw.closedBox (dzzMuIn γ W ω))) δ (rP32 γ δ / Bw.side) b'
        (lamP32 δ)} with hBad
  set Kf : ℝ → ℕ := fun δ => ⌊C * Real.logb 2 δ⁻¹⌋₊ with hKf
  set Good : ℝ → Set Ω := fun δ =>
    (⋃ n ∈ Finset.Icc 1 (Kf δ - Bw.n), {ω | ∃ b : DyBox, b.n = n ∧ ω ∈ Bad δ b})ᶜ with hGood
  -- the union bound
  have hGoodHP : HighProb P Good := by
    refine ⟨1, one_pos, min δ₁ (1 / 2), by positivity, fun δ hδ => ?_⟩
    obtain ⟨hδ0, hδ⟩ := hδ
    have hδa : δ < δ₁ := hδ.trans_le (min_le_left _ _)
    have hδ1 : δ < 1 := by linarith [hδ.trans_le (min_le_right _ _)]
    set L := Real.log δ⁻¹ with hLdef
    have hlogδ : Real.log δ = -L := by rw [hLdef, Real.log_inv, neg_neg]
    have hL0 : 0 < L := by
      rw [hLdef, Real.log_inv]; have := Real.log_neg hδ0 hδ1; linarith
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2' : 1 / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
    have hKr : 0 ≤ C * Real.logb 2 δ⁻¹ := by
      rw [Real.logb, ← hLdef]; positivity
    set K := Kf δ with hKdef
    have hK : (K : ℝ) ≤ C * L / Real.log 2 := by
      calc (K : ℝ) ≤ C * Real.logb 2 δ⁻¹ := Nat.floor_le hKr
        _ = C * L / Real.log 2 := by rw [Real.logb, ← hLdef, mul_div_assoc]
    have hlevel : ∀ n ∈ Finset.Icc 1 (K - Bw.n), P.real {ω | ∃ b : DyBox, b.n = n ∧ ω ∈ Bad δ b} ≤
        ((2 : ℝ) ^ n) ^ 2 * δ ^ (10 * C + 10) := by
      intro n hn
      obtain ⟨hn1, hnK⟩ := Finset.mem_Icc.1 hn
      refine measureReal_level_le n (Bad δ) fun b hb => ?_
      have hbK : ((wEmb Bw b).n : ℝ) ≤ C * Real.logb 2 δ⁻¹ := by
        have : (wEmb Bw b).n ≤ K := by simp only [wEmb]; omega
        exact (Nat.cast_le.2 this).trans (Nat.floor_le hKr)
      exact ENNReal.toReal_le_of_le_ofReal (by positivity)
        (hperc δ ⟨hδ0, hδa⟩ b (hb ▸ hn1) hbK)
    have hterm : ∀ n ∈ Finset.Icc 1 (K - Bw.n), ((2 : ℝ) ^ n) ^ 2 * δ ^ (10 * C + 10) ≤
        Real.exp (-((8 * C + 10) * L)) := by
      intro n hn
      have hnK : n ≤ K := by have := (Finset.mem_Icc.1 hn).2; omega
      have hnL : (n : ℝ) * Real.log 2 ≤ C * L := by
        have : (n : ℝ) ≤ K := by exact_mod_cast hnK
        have := mul_le_mul_of_nonneg_right (this.trans hK) hlog2.le
        rwa [div_mul_cancel₀ _ hlog2.ne'] at this
      rw [two_pow_sq_eq, Real.rpow_def_of_pos hδ0, hlogδ, ← Real.exp_add, Real.exp_le_exp]
      nlinarith
    have hsum : ∑ n ∈ Finset.Icc 1 (K - Bw.n), ((2 : ℝ) ^ n) ^ 2 * δ ^ (10 * C + 10) ≤ δ := by
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
      have hcard : ((K - Bw.n + 1 - 1 : ℕ) : ℝ) ≤ K := by
        exact_mod_cast (show K - Bw.n + 1 - 1 ≤ K by omega)
      refine (mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le).trans ?_
      have hKL : (K : ℝ) ≤ 2 * C * L := by
        refine hK.trans ?_
        rw [div_le_iff₀ hlog2]
        have := mul_le_mul_of_nonneg_left hlog2'.le (mul_pos hC hL0).le
        linarith
      have hex : 2 * C * L ≤ Real.exp ((8 * C + 9) * L) := by
        have := Real.add_one_le_exp ((8 * C + 9) * L); nlinarith
      have hδe : δ = Real.exp (-L) := by rw [← hlogδ, Real.exp_log hδ0]
      calc (K : ℝ) * Real.exp (-((8 * C + 10) * L)) ≤
            Real.exp ((8 * C + 9) * L) * Real.exp (-((8 * C + 10) * L)) :=
            mul_le_mul_of_nonneg_right (hKL.trans hex) (Real.exp_pos _).le
        _ = δ := by rw [← Real.exp_add, hδe]; congr 1; ring
    have hreal : P.real (Good δ)ᶜ ≤ δ := by
      rw [hGood, compl_compl]
      exact (measureReal_biUnion_finset_le _ _).trans ((Finset.sum_le_sum hlevel).trans hsum)
    rw [← ofReal_measureReal (measure_ne_top P _), Real.rpow_one]
    exact ENNReal.ofReal_le_ofReal hreal
  -- the inclusion
  obtain ⟨c, hc, δ₂, hδ₂, hH⟩ := ((dzz_lemma31 hW hγ hγ2).inter hG).inter hGoodHP
  have hcM := dzzCMc_pos γ
  have hsw := wside_pos Bw
  refine ⟨c, hc, min δ₂ (min (1 / 2) ((Bw.side / 2) ^ (1 / dzzCMc γ))), by positivity,
    fun δ hδ => ?_⟩
  obtain ⟨hδ0, hδ⟩ := hδ
  have hδ1 : δ < 1 := by
    linarith [hδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))]
  have hδs : δ ^ dzzCMc γ < Bw.side := by
    have := Real.rpow_lt_rpow hδ0.le (hδ.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
      hcM
    rw [← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ hcM.ne', Real.rpow_one] at this
    linarith
  refine le_trans (measure_mono (compl_subset_compl.2 ?_)) (hH δ ⟨hδ0, hδ.trans_le
    (min_le_left _ _)⟩)
  rintro ω ⟨⟨hS, hGω⟩, hgood⟩ b hb
  by_contra hnot
  apply hgood
  set L := Real.log δ⁻¹ with hLdef
  have hlogδ : Real.log δ = -L := by rw [hLdef, Real.log_inv, neg_neg]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hKr : 0 ≤ C * Real.logb 2 δ⁻¹ := by
    rw [Real.logb, ← hLdef]
    have : 0 < L := by rw [hLdef, Real.log_inv]; have := Real.log_neg hδ0 hδ1; linarith
    positivity
  obtain ⟨hs1, hs2⟩ := hS.2 _ hb
  rw [← hCdef] at hs1
  have hn1 : 1 ≤ b.n := by
    by_contra h0
    have h0' : b.n = 0 := by omega
    have : (wEmb Bw b).side = Bw.side := by
      rw [side_wEmb]; unfold DyBox.side; rw [h0', pow_zero, mul_one]
    linarith
  have hnK' : (wEmb Bw b).n ≤ Kf δ := by
    simp only [hKf]
    apply Nat.le_floor
    have h1 := Real.log_le_log (by positivity) hs1
    rw [Real.log_rpow hδ0, hlogδ] at h1
    have h2 : Real.log (wEmb Bw b).side = -((wEmb Bw b).n * Real.log 2) := by
      unfold DyBox.side; rw [Real.log_pow, Real.log_inv]; ring
    rw [h2] at h1
    rw [Real.logb, ← hLdef, mul_div_assoc', le_div_iff₀ hlog2]
    linarith
  have hnK : b.n ≤ Kf δ - Bw.n := by
    have : (wEmb Bw b).n = Bw.n + b.n := rfl
    omega
  exact mem_iUnion₂.2 ⟨b.n, Finset.mem_Icc.2 ⟨hn1, hnK⟩, b, rfl, ⟨⟨hb.1.le, hGω⟩, hnot⟩⟩

end DZZ
end LQGMetric
