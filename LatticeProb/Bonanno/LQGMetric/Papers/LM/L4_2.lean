/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.L4_2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_6Main
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.GoodAnnulus

/-!
# LM Lemma 4.2 from LM Lemma 4.1 (task P2-LM42)

Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), Lemma 4.1 (`lem-good-radius-tail`, l. 803–816) and Lemma 4.2
(`lem-good-radius-all`, l. 820–829).

* `LMLem4_1Tail p`: LM Lemma 4.1 in the form proved in `L4_1.lean`: if `P[E_t(w)] ≥ p` for the
  scales `t = 8^{-k} r`, `k ∈ ℕ`, then `P[E_{8^{-m}r}(w)` fails for all `m ∈ [1, M]] ≤ c 8^{-5M}`
  (LM: `P[ρ_r(w) < εr] = O(ε^q)` with `q = 5`, as used in the proof of Lemma 4.2, l. 827).
  We only use the scales `8^{-m} r` (a subsequence of LM's `2^{-k} r`), see `L4_1.lean`.
* `lmLem4_2_of_tail`: LM Lemma 4.2 (`LMLem4_2 p`) from `LMLem4_1Tail p`, following LM l. 827–829:
  `q = 5`, union bound over the `O(ε^{-4})` grid points of `(¼ε²ℤ²) ∩ B_ε(K)`; the balls
  `B_{ε²/2}(w)` cover `K`. As in LM S4.2a (blueprint), the hypothesis (1.3) is used on the compact
  set `K' = cl B_1(K) ⊇ B_ε(K)`. The grid rounding and the box count follow `GM.gm_L3_9`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.LM

open Blueprint

/-- **LM Lemma 4.1** (`lem-good-radius-tail`, l. 803–816), `q = 5`, along the scales `8^{-m} r`:
the constant `c` does not depend on the field, the metrics, `C`, `w` or `r`. -/
def LMLem4_1Tail (p : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (ξ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (D D' : Ω → ContMetric),
    IsNormalizedWPGFF h P → IsXiAdditive2 ξ P h D D' → ∀ C : ℝ, 0 < C →
    ∀ (w : ℂ) (r : ℝ), 0 < r →
    (∀ k : ℕ, ENNReal.ofReal p ≤ P {ω | lmGoodE (D ω) (D' ω) C w ((8 : ℝ)⁻¹ ^ k * r)}) →
    ∀ M : ℕ, P {ω | ∀ m ∈ Finset.Icc 1 M, ¬ lmGoodE (D ω) (D' ω) C w ((8 : ℝ)⁻¹ ^ m * r)} ≤
      ENNReal.ofReal (c * (8 : ℝ)⁻¹ ^ (5 * M))

lemma two_zpow_three_mul (m : ℕ) : (2 : ℝ) ^ (-((3 * m : ℕ) : ℤ)) = (8 : ℝ)⁻¹ ^ m := by
  rw [zpow_neg, zpow_natCast, pow_mul, inv_pow]; norm_num

/-- the scale `M` with `8^{-(M+1)} < ε ≤ 8^{-M}` -/
lemma exists_scale {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ M : ℕ, ε ≤ (8 : ℝ)⁻¹ ^ M ∧ (8 : ℝ)⁻¹ ^ M < 8 * ε := by
  classical
  have hex : ∃ n : ℕ, (8 : ℝ)⁻¹ ^ n < ε := exists_pow_lt_of_lt_one hε0 (by norm_num)
  set N := Nat.find hex with hN
  have hN0 : N ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [← hN, h0, pow_zero] at this
    linarith
  refine ⟨N - 1, not_lt.1 (Nat.find_min hex (by omega)), ?_⟩
  have h1 := Nat.find_spec hex
  rw [← hN, show N = (N - 1) + 1 by omega, pow_succ] at h1
  linarith

/-- the arithmetic of the union bound: `(2M + 1)² c 8^5 ε^5 ≤ c 8^5 (8R₀ + 5)² ε` -/
lemma unionBound_arith42 {ε R₀ c : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hc : 0 < c)
    {M : ℕ} (hM : (M : ℝ) * (ε ^ 2 / 4) ≤ R₀ + 2 * (ε ^ 2 / 4)) :
    (2 * M + 1 : ℝ) ^ 2 * (c * (8 ^ 5 * ε ^ 5)) ≤ c * 8 ^ 5 * (8 * R₀ + 5) ^ 2 * ε := by
  have hb : (2 * M + 1 : ℝ) * ε ^ 2 ≤ 8 * R₀ + 5 := by nlinarith
  have hb0 : 0 ≤ (2 * M + 1 : ℝ) * ε ^ 2 := by positivity
  have hsq : ((2 * M + 1 : ℝ) * ε ^ 2) ^ 2 ≤ (8 * R₀ + 5) ^ 2 := pow_le_pow_left₀ hb0 hb 2
  have : (2 * M + 1 : ℝ) ^ 2 * (c * (8 ^ 5 * ε ^ 5)) =
      c * 8 ^ 5 * ε * ((2 * M + 1 : ℝ) * ε ^ 2) ^ 2 := by ring
  rw [this]
  have hKε : 0 ≤ c * 8 ^ 5 * ε := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hsq hKε]

/-- **LM Lemma 4.2** (`lem-good-radius-all`, l. 820–829) from LM Lemma 4.1 with `q = 5`. -/
theorem lmLem4_2_of_tail {p : ℝ} (H : LMLem4_1Tail p) : LMLem4_2 p := by
  obtain ⟨c, hc, Ht⟩ := H
  intro ξ Ω _ P _ h D D' hh hxi C hC hyp K hK
  -- the compact set `K' = cl B_1(K)` (LM S4.2a)
  obtain ⟨rK, hrK, hK'⟩ := hyp _ (hK.cthickening (r := 1))
  obtain ⟨R₀, hR₀, hKR⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : ℂ)
  set B : ℝ := c * 8 ^ 5 * (8 * R₀ + 5) ^ 2 with hB
  have hB0 : 0 < B := by positivity
  -- the bound `P[(F^ε)^c] ≤ B ε` for `ε < min (1/2) rK`
  have key : ∀ ε ∈ Ioo (0 : ℝ) (min (1 / 2) rK),
      P {ω | ¬ lmCoverE (D ω) (D' ω) C ε K} ≤ ENNReal.ofReal (B * ε) := by
    intro ε ⟨hε0, hεm⟩
    have hε1 : ε < 1 := by linarith [hεm.trans_le (min_le_left _ _)]
    have hεr : ε ≤ rK := (hεm.trans_le (min_le_right _ _)).le
    obtain ⟨M, hM1, hM2⟩ := exists_scale hε0 hε1
    set δ : ℝ := ε ^ 2 / 4 with hδ
    have hδ0 : 0 < δ := by positivity
    have hδε : δ < ε := by rw [hδ]; nlinarith
    set Mb : ℕ := ⌈R₀ / δ⌉₊ + 1 with hMbdef
    have hMlt : (Mb : ℝ) < R₀ / δ + 2 := by
      rw [hMbdef]; push_cast
      linarith [Nat.ceil_lt_add_one (show 0 ≤ R₀ / δ by positivity)]
    have hMge : R₀ / δ + 1 ≤ (Mb : ℝ) := by
      rw [hMbdef]; push_cast
      linarith [Nat.le_ceil (R₀ / δ)]
    have hMx : (Mb : ℝ) * δ ≤ R₀ + 2 * δ := by
      have := mul_le_mul_of_nonneg_right hMlt.le hδ0.le
      rwa [add_mul, div_mul_cancel₀ _ hδ0.ne'] at this
    set Box : Finset (ℤ × ℤ) := Finset.Icc (-(Mb : ℤ)) Mb ×ˢ Finset.Icc (-(Mb : ℤ)) Mb with hBox
    classical
    set F : ℤ × ℤ → Set Ω := fun m => if GM.gridPt δ m ∈ cthickening 1 K then
      {ω | ∀ j ∈ Finset.Icc 1 M, ¬ lmGoodE (D ω) (D' ω) C (GM.gridPt δ m) ((8 : ℝ)⁻¹ ^ j * ε)}
      else ∅ with hF
    have hsub : {ω | ¬ lmCoverE (D ω) (D' ω) C ε K} ⊆ ⋃ m ∈ Box, F m := by
      intro ω hω
      simp only [mem_ofPred_eq, lmCoverE, not_forall, not_exists, not_and] at hω
      obtain ⟨z, hz, hy⟩ := hω
      have hzn : ‖z‖ ≤ R₀ := by simpa using hKR hz
      have hbd : ∀ t : ℝ, |t| ≤ ‖z‖ → |t| / δ + 1 ≤ Mb := by
        intro t ht
        have : |t| / δ ≤ R₀ / δ := div_le_div_of_nonneg_right (ht.trans hzn) hδ0.le
        linarith
      obtain ⟨hre1, hre2⟩ := GM.round_grid hδ0 (hbd _ (Complex.abs_re_le_norm _))
      obtain ⟨him1, him2⟩ := GM.round_grid hδ0 (hbd _ (Complex.abs_im_le_norm _))
      set m : ℤ × ℤ := (round (z.re / δ), round (z.im / δ)) with hm
      have hdist : ‖z - GM.gridPt δ m‖ ≤ δ := by
        refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
        rw [Complex.sub_re, Complex.sub_im, GM.gridPt_re, GM.gridPt_im]
        linarith
      have hinf : infDist (GM.gridPt δ m) K < ε := by
        refine (infDist_le_dist_of_mem hz).trans_lt ?_
        rw [dist_comm, dist_eq_norm]; linarith
      have hK'm : GM.gridPt δ m ∈ cthickening 1 K := by
        refine mem_cthickening_of_dist_le _ z 1 K hz ?_
        rw [dist_eq_norm, ← norm_neg, neg_sub]; linarith
      refine mem_biUnion (x := m) (Finset.mem_coe.2 (Finset.mem_product.2 ⟨hre2, him2⟩)) ?_
      simp only [hF, if_pos hK'm, mem_ofPred_eq]
      intro j hj hgood
      have hj1 := (Finset.mem_Icc.1 hj).1
      have hjM := (Finset.mem_Icc.1 hj).2
      have hpow : (8 : ℝ)⁻¹ ^ M ≤ (8 : ℝ)⁻¹ ^ j :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hjM
      have hpow1 : (8 : ℝ)⁻¹ ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have hr1 : ε ^ 2 ≤ (8 : ℝ)⁻¹ ^ j * ε := by nlinarith
      refine hy (3 * j) (GM.gridPt δ m) ?_ ?_ ?_ hinf ?_ ?_
      · rw [two_zpow_three_mul]; exact hr1
      · rw [two_zpow_three_mul]; nlinarith
      · exact ⟨m.1, m.2, by simp [GM.gridPt, hδ]⟩
      · rw [two_zpow_three_mul]
        have : δ < ε ^ 2 / 2 := by rw [hδ]; nlinarith
        linarith
      · rw [two_zpow_three_mul]; exact hgood
    have hFm : ∀ m ∈ Box, P (F m) ≤ ENNReal.ofReal (c * (8 ^ 5 * ε ^ 5)) := by
      intro m _
      simp only [hF]
      split_ifs with hm
      · refine (Ht ξ P h D D' hh hxi C hC (GM.gridPt δ m) ε hε0 (fun k => ?_) M).trans ?_
        · refine hK' _ hm _ ⟨by positivity, ?_⟩
          have : (8 : ℝ)⁻¹ ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
          nlinarith
        · refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hc.le)
          rw [pow_mul']
          have h0 : 0 ≤ ((8 : ℝ)⁻¹ ^ M) := by positivity
          calc ((8 : ℝ)⁻¹ ^ M) ^ 5 ≤ (8 * ε) ^ 5 := pow_le_pow_left₀ h0 hM2.le 5
            _ = 8 ^ 5 * ε ^ 5 := by ring
      · simp
    have hcard : (Box.card : ℝ) = (2 * Mb + 1 : ℝ) ^ 2 := by
      rw [hBox, Finset.card_product, Int.card_Icc]
      have : ((Mb : ℤ) + 1 - -(Mb : ℤ)).toNat = 2 * Mb + 1 := by omega
      rw [this]; push_cast; ring
    calc P _ ≤ P (⋃ m ∈ Box, F m) := measure_mono hsub
      _ ≤ ∑ m ∈ Box, P (F m) := measure_biUnion_finset_le _ _
      _ ≤ ∑ _m ∈ Box, ENNReal.ofReal (c * (8 ^ 5 * ε ^ 5)) := Finset.sum_le_sum hFm
      _ = ENNReal.ofReal ((Box.card : ℝ) * (c * (8 ^ 5 * ε ^ 5))) := by
          rw [Finset.sum_const, nsmul_eq_mul,
            ENNReal.ofReal_mul (p := (Box.card : ℝ)) (by positivity), ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (B * ε) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [hcard, hB]
          exact unionBound_arith42 hε0 hε1 hc hMx
  -- `ε → 0`
  have hlim : Tendsto (fun ε : ℝ => ENNReal.ofReal (B * ε)) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun ε : ℝ => ENNReal.ofReal (B * ε)) (𝓝 0) (𝓝 (ENNReal.ofReal (B * 0))) :=
      (ENNReal.continuous_ofReal.comp (continuous_const.mul continuous_id)).tendsto 0
    rw [mul_zero, ENNReal.ofReal_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [Ioo_mem_nhdsGT (lt_min (by norm_num : (0 : ℝ) < 1 / 2) hrK)] with ε hε
  exact key ε hε

end LQGMetric.LM
