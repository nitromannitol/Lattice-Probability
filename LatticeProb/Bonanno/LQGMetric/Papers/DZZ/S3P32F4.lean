/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32F4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32F3

/-!
# `L32EncPhiHPW` at `μIn`: the union over the cells (P2-DZZ32F)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1088–1094, 1104–1147): (eq-B-percolation-Psi) holds
for every box `B` of level `≤ C_mc log₂ δ⁻¹` (`p32_enc_perc`), and on the event of Lemma 3.1 every
cell is such a box; a union bound over the `≤ 4^n` boxes of each level `n ≤ C_mc log₂ δ⁻¹` (as in
`l37_cells_enc`, DZZ l. 1047–1049) gives
**`l32EncPhiHPW_dzzMuIn : L32EncPhiHPW P γ W (dzzMuIn γ W) (rP32 γ)`**.
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

/-- **DZZ (eq-B-percolation-Psi) + union over cells at `μIn`** (D102 P-4bW, first input). -/
theorem l32EncPhiHPW_dzzMuIn {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    L32EncPhiHPW P γ W (dzzMuIn γ W) (rP32 γ) := by
  have := hW.isProbabilityMeasure
  obtain ⟨α, G, hG, δ₀, hδ₀, hup⟩ := l32TildeMUpper_wickQArea (P := P) hW hγ hγ2
  obtain ⟨δ₁, hδ₁, hperc⟩ := p32_enc_perc hW hγ hγ2 α G hδ₀ hup
  set C := dzzCmc γ with hCdef
  have hC : 0 < C := by have := l31theta_pos hγ hγ2; rw [hCdef]; unfold dzzCmc; linarith
  set Bad : ℝ → DyBox → Set Ω := fun δ b => {ω | approxLQG γ W ω b ≤ δ ^ 2} ∩ G δ ∩
    {ω | ¬ HasEnclosure b (kL37 γ δ) fun b' =>
      PhiLeW (dzzMuIn γ W ω) δ (rP32 γ δ) b' (lamP32 δ)} with hBad
  set Kf : ℝ → ℕ := fun δ => ⌊C * Real.logb 2 δ⁻¹⌋₊ with hKf
  set Good : ℝ → Set Ω := fun δ =>
    (⋃ n ∈ Finset.Icc 1 (Kf δ), {ω | ∃ b : DyBox, b.n = n ∧ ω ∈ Bad δ b})ᶜ with hGood
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
    have hlevel : ∀ n ∈ Finset.Icc 1 K, P.real {ω | ∃ b : DyBox, b.n = n ∧ ω ∈ Bad δ b} ≤
        ((2 : ℝ) ^ n) ^ 2 * δ ^ (10 * C + 10) := by
      intro n hn
      obtain ⟨hn1, hnK⟩ := Finset.mem_Icc.1 hn
      refine measureReal_level_le n (Bad δ) fun b hb => ?_
      have hbK : (b.n : ℝ) ≤ C * Real.logb 2 δ⁻¹ := by
        rw [hb]; exact (Nat.cast_le.2 hnK).trans (Nat.floor_le hKr)
      exact ENNReal.toReal_le_of_le_ofReal (by positivity)
        (hperc δ ⟨hδ0, hδa⟩ b (hb ▸ hn1) hbK)
    have hterm : ∀ n ∈ Finset.Icc 1 K, ((2 : ℝ) ^ n) ^ 2 * δ ^ (10 * C + 10) ≤
        Real.exp (-((8 * C + 10) * L)) := by
      intro n hn
      have hnK := (Finset.mem_Icc.1 hn).2
      have hnL : (n : ℝ) * Real.log 2 ≤ C * L := by
        have : (n : ℝ) ≤ K := by exact_mod_cast hnK
        have := mul_le_mul_of_nonneg_right (this.trans hK) hlog2.le
        rwa [div_mul_cancel₀ _ hlog2.ne'] at this
      rw [two_pow_sq_eq, Real.rpow_def_of_pos hδ0, hlogδ, ← Real.exp_add, Real.exp_le_exp]
      nlinarith
    have hsum : ∑ n ∈ Finset.Icc 1 K, ((2 : ℝ) ^ n) ^ 2 * δ ^ (10 * C + 10) ≤ δ := by
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, show K + 1 - 1 = K by omega]
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
  refine ⟨c, hc, min δ₂ (1 / 2), by positivity, fun δ hδ => ?_⟩
  obtain ⟨hδ0, hδ⟩ := hδ
  have hδ1 : δ < 1 := by linarith [hδ.trans_le (min_le_right _ _)]
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
  obtain ⟨hs1, hs2⟩ := hS.2 b hb
  rw [← hCdef] at hs1
  have hn1 : 1 ≤ b.n := by
    by_contra h0
    have h0' : b.n = 0 := by omega
    have : b.side = 1 := by unfold DyBox.side; rw [h0', pow_zero]
    have hlt : δ ^ dzzCMc γ < 1 := Real.rpow_lt_one hδ0.le hδ1 (dzzCMc_pos γ)
    linarith
  have hnK : b.n ≤ Kf δ := by
    simp only [hKf]
    apply Nat.le_floor
    have h1 := Real.log_le_log (by positivity) hs1
    rw [Real.log_rpow hδ0, hlogδ] at h1
    have h2 : Real.log b.side = -(b.n * Real.log 2) := by
      unfold DyBox.side; rw [Real.log_pow, Real.log_inv]; ring
    rw [h2] at h1
    rw [Real.logb, ← hLdef, mul_div_assoc', le_div_iff₀ hlog2]
    linarith
  exact mem_iUnion₂.2 ⟨b.n, Finset.mem_Icc.2 ⟨hn1, hnK⟩, b, rfl, ⟨⟨hb.1.le, hGω⟩, hnot⟩⟩

end DZZ
end LQGMetric
