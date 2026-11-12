/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.P18Step3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Blocks
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Comb
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.C17

/-!
# DDDF Proposition 18, Step 3: the a priori bound (task P2-DDDF16c)

DDDF (arXiv:1904.08021, `tightness.tex` l. 915–927): `ℓ_n(φ,p) ≥ 2^{-2ξk} ℓ_{n−k}(φ,p) e^{-C√k}`.
"Using the supremum tail estimate (Prop 2) and the left tail estimates (Cor 17) ... each term is
less than `p/2` if `C` is large enough, depending on `p`." Here: the bad events are
`B₁ = {M ≤ max_{[0,1]²} |φ_{0,k}|}` (Prop 2, `M = α(k + C√k)`, `α = log 4 + β/√k`, as in
`dddf_p18_ell_lower`) and `B₂ = ⋃_b {L^{(k,n)}(R_b) ≤ 2^{-k} e^{-D√k} ℓ_{n−k}}` over the
`3·2^k(2^k+1)` block rectangles (`p18Idx`), each of probability `≤ C e^{-c D² k}` by
`prob_lenObs_p18V/H` and Cor 17 (`dddf_cor17`); off `B₁ ∪ B₂`, `p18_step3_pathwise` gives
`L^{(n)}_{1,1} ≥ 2^{-2ξk} e^{-C√k} ℓ_{n−k}`. We take each bad probability `< p/3`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ξ : ℝ}

lemma prob_p18Blk {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {k n : ℕ} (hkn : k ≤ n)
    (b : ℕ × ℤ × Fin 3) (x : ℝ) :
    P {ω | lenObs ξ (phiMN W P k n) (p18Blk k b) ω ≤ x} =
      P {ω | (2 : ℝ)⁻¹ ^ k * lenObs ξ (phiMN W P 0 (n - k)) (rectAB 1 3) ω ≤ x} := by
  unfold p18Blk
  split_ifs
  · exact prob_lenObs_p18V hW hkn _ _ measurableSet_Iic
  · exact prob_lenObs_p18H hW hkn _ _ measurableSet_Iic
  · exact prob_lenObs_p18H hW hkn _ _ measurableSet_Iic

lemma card_p18Idx_le (k : ℕ) : ((p18Idx k).card : ℝ) ≤ 6 * 4 ^ k := by
  have hc1 : (Finset.Icc (0 : ℤ) (2 ^ k)).card = 2 ^ k + 1 := by
    rw [Int.card_Icc, sub_zero]
    have : ((2 : ℤ) ^ k + 1) = ((2 ^ k + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [this, Int.toNat_natCast]
  have hc1' : ((Finset.Icc (0 : ℤ) (2 ^ k)).card : ℝ) = 2 ^ k + 1 := by
    rw [hc1]; push_cast; ring
  simp only [p18Idx, Finset.card_product, Finset.card_range, Finset.card_univ, Fintype.card_fin]
  push_cast
  rw [hc1']
  have h1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have e : (4 : ℝ) ^ k = 2 ^ k * 2 ^ k := by rw [← mul_pow]; norm_num
  rw [e]; nlinarith

/-- **DDDF Prop 18, Step 3** (l. 915–927): for `p` small there is `C` with
`ℓ_n(φ,p) ≥ 2^{-2ξk} ℓ_{n−k}(φ,p) e^{-C√k}` for all `k ≤ n`. -/
theorem dddf_p18_step3 {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (hξ : 0 < ξ) :
    P18Step3 ξ W P := by
  have := hW.isProbabilityMeasure
  obtain ⟨p₁, hp₁, h17⟩ := dddf_cor17 hW hξ
  obtain ⟨C₂, hC₂, h2⟩ := prop2_tail
  refine ⟨min p₁ (1 / 2), by positivity, fun p hp0 hp => ?_⟩
  have hpp₁ : p ≤ p₁ := (le_min_iff.1 hp).1
  have hp2 : p ≤ 1 / 2 := (le_min_iff.1 hp).2
  obtain ⟨C₁, c₁, hC₁, hc₁, hcor⟩ := h17 p hp0 hpp₁
  obtain ⟨Cℓ, -, hell⟩ := dddf_p18_ell_lower hW hξ hp0 (by linarith : p < 1)
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl42 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  -- `β` for Prop 2
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ, β = max 0 (Real.log (3 * C₂ / p) / 2) + 1 := ⟨_, rfl⟩
  have hβ : 0 < β := by rw [hβdef]; positivity
  have hβp : C₂ * Real.exp (-(2 * β)) < p / 3 := by
    have h1 : Real.log (3 * C₂ / p) < 2 * β := by
      have := le_max_right 0 (Real.log (3 * C₂ / p) / 2); rw [hβdef]; linarith
    have h2' : Real.exp (-(2 * β)) < Real.exp (-Real.log (3 * C₂ / p)) :=
      Real.exp_lt_exp.2 (by linarith)
    have e : Real.exp (-Real.log (3 * C₂ / p)) = p / (3 * C₂) := by
      rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
    rw [e] at h2'
    calc C₂ * Real.exp (-(2 * β)) < C₂ * (p / (3 * C₂)) := mul_lt_mul_of_pos_left h2' hC₂
      _ = p / 3 := by field_simp
  -- `D` for the blocks
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = |Real.log (18 * C₁ / p)| + 1 := ⟨_, rfl⟩
  have hL1 : 1 ≤ L := by rw [hLdef]; linarith [abs_nonneg (Real.log (18 * C₁ / p))]
  have hL : 6 * C₁ * Real.exp (-L) < p / 3 := by
    have h1 : Real.log (18 * C₁ / p) < L := by
      rw [hLdef]; linarith [le_abs_self (Real.log (18 * C₁ / p))]
    have h2' : Real.exp (-L) < Real.exp (-Real.log (18 * C₁ / p)) :=
      Real.exp_lt_exp.2 (by linarith)
    have e : Real.exp (-Real.log (18 * C₁ / p)) = p / (18 * C₁) := by
      rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
    rw [e] at h2'
    calc 6 * C₁ * Real.exp (-L) < 6 * C₁ * (p / (18 * C₁)) :=
          mul_lt_mul_of_pos_left h2' (by positivity)
      _ = p / 3 := by field_simp; ring
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = √((Real.log 4 + L) / c₁) := ⟨_, rfl⟩
  have hD0 : 0 < D := by rw [hDdef]; exact Real.sqrt_pos.2 (by positivity)
  have hD2 : c₁ * D ^ 2 = Real.log 4 + L := by
    rw [hDdef, Real.sq_sqrt (by positivity)]; field_simp
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = ξ * (C₂ * Real.log 4 + β + β * C₂) + D + Real.log 2 + 1 :=
    ⟨_, rfl⟩
  have hC : 0 < C := by rw [hCdef]; positivity
  refine ⟨C, hC, fun n k hkn => ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hn : 1 ≤ n := by omega
  have hℓn0 : 0 < ellN ξ W P n (ENNReal.ofReal p) := lt_of_lt_of_le (Real.exp_pos _) (hell n hn)
  obtain ⟨ℓ', hℓ'⟩ : ∃ ℓ', ℓ' = ellN ξ W P (n - k) (ENNReal.ofReal p) := ⟨_, rfl⟩
  rw [← hℓ']
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨t, ht_def⟩ : ∃ t : ℝ, t = √(k : ℝ) := ⟨_, rfl⟩
  have ht1 : 1 ≤ t := by rw [ht_def]; exact Real.one_le_sqrt.2 hk'
  have ht2 : t ^ 2 = k := by rw [ht_def]; exact Real.sq_sqrt (by positivity)
  rw [← ht_def]
  -- the left side as an exponential
  have hLHS : (2 : ℝ) ^ (-(2 * ξ * k)) * ℓ' * Real.exp (-(C * t)) =
      Real.exp (-(ξ * k * Real.log 4) - C * t) * ℓ' := by
    rw [Real.rpow_def_of_pos (by norm_num), hl42, sub_eq_add_neg, Real.exp_add]; ring_nf
  rw [hLHS]
  by_cases hℓ'0 : ℓ' ≤ 0
  · have : Real.exp (-(ξ * k * Real.log 4) - C * t) * ℓ' ≤ 0 :=
      mul_nonpos_iff.2 (Or.inl ⟨(Real.exp_pos _).le, hℓ'0⟩)
    linarith
  push Not at hℓ'0
  obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = Real.log 4 + β / t := ⟨_, rfl⟩
  have hα : 0 < α := by rw [hαdef]; positivity
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = α * (k + C₂ * √k) := ⟨_, rfl⟩
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = (2 : ℝ)⁻¹ ^ k * (Real.exp (-(D * t)) * ℓ') := ⟨_, rfl⟩
  have hx0 : 0 ≤ x := by rw [hxdef]; positivity
  set B1 := {ω | M ≤ ⨆ z : SupTail.ferniqueBox 0 1, |phiMN W P 0 k z ω|} with hB1def
  set B2 := ⋃ b ∈ p18Idx k, {ω | lenObs ξ (phiMN W P k n) (p18Blk k b) ω ≤ x} with hB2def
  have hφk := isPhiVersion_phiMN hW (Nat.zero_le k)
  have hφn := isPhiVersion_phiMN hW (Nat.zero_le n)
  have hφkn := isPhiVersion_phiMN hW hkn
  -- Prop 2
  have hB1 : P.real B1 < p / 3 := by
    have hB := h2 hW k (phiMN W P 0 k) (fun x => by simpa [inv_pow] using hφk.ae_eq x) hφk.cont
      α hα
    rw [← hMdef] at hB
    refine lt_of_le_of_lt hB (lt_of_le_of_lt ?_ hβp)
    have e4 : (4 : ℝ) ^ k = Real.exp (k * Real.log 4) := by
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 4), ← Real.exp_nat_mul,
        Real.exp_log (by norm_num)]
    rw [e4, mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC₂.le
    have hαsq : α ^ 2 * k / Real.log 4 = k * Real.log 4 + 2 * β * t + β ^ 2 / Real.log 4 := by
      rw [hαdef, ← ht2]; field_simp; ring
    rw [neg_mul, neg_div, hαsq]
    have : 2 * β ≤ 2 * β * t := le_mul_of_one_le_right (by positivity) ht1
    have : 0 ≤ β ^ 2 / Real.log 4 := by positivity
    linarith
  -- the blocks (Cor 17)
  have hB2 : P B2 ≤ ENNReal.ofReal (6 * C₁ * Real.exp (-L)) := by
    refine (measure_biUnion_finset_le _ _).trans ?_
    have hb : ∀ b ∈ p18Idx k, P {ω | lenObs ξ (phiMN W P k n) (p18Blk k b) ω ≤ x} ≤
        ENNReal.ofReal (C₁ * Real.exp (-c₁ * (D * t) ^ 2)) := by
      intro b _
      rw [prob_p18Blk hW hkn b x]
      have e : {ω | (2 : ℝ)⁻¹ ^ k * lenObs ξ (phiMN W P 0 (n - k)) (rectAB 1 3) ω ≤ x} =
          {ω | lenObs ξ (phiMN W P 0 (n - k)) (rectAB 1 3) ω ≤ Real.exp (-(D * t)) *
            ellQ ξ P (phiMN W P 0 (n - k)) (rectAB 1 1) (ENNReal.ofReal p)} := by
        ext ω
        simp only [mem_ofPred_eq, hxdef, hℓ']
        exact mul_le_mul_iff_of_pos_left (by positivity)
      rw [e]
      exact hcor (n - k) (D * t) (by positivity)
    refine (Finset.sum_le_sum hb).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hs2 : -c₁ * (D * t) ^ 2 = -((Real.log 4 + L) * k) := by
      rw [mul_pow, ht2, neg_mul, ← mul_assoc, hD2]
    have e4 : (4 : ℝ) ^ k = Real.exp (k * Real.log 4) := by
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 4), ← Real.exp_nat_mul,
        Real.exp_log (by norm_num)]
    have hee : Real.exp (k * Real.log 4) * Real.exp (-((Real.log 4 + L) * k)) =
        Real.exp (-(L * k)) := by rw [← Real.exp_add]; congr 1; ring
    calc ((p18Idx k).card : ℝ) * (C₁ * Real.exp (-c₁ * (D * t) ^ 2))
        ≤ 6 * 4 ^ k * (C₁ * Real.exp (-c₁ * (D * t) ^ 2)) :=
          mul_le_mul_of_nonneg_right (card_p18Idx_le k) (by positivity)
      _ = 6 * C₁ * Real.exp (-(L * k)) := by
          rw [hs2, e4]; linear_combination (6 * C₁) * hee
      _ ≤ 6 * C₁ * Real.exp (-L) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) (by positivity)
  -- off the bad events
  have hM : ξ * M ≤ ξ * (k * Real.log 4 + (C₂ * Real.log 4 + β + β * C₂) * t) := by
    refine mul_le_mul_of_nonneg_left ?_ hξ.le
    rw [hMdef, hαdef, ← ht_def]
    have e : (Real.log 4 + β / t) * (k + C₂ * t) =
        k * Real.log 4 + C₂ * Real.log 4 * t + β * t + β * C₂ := by
      rw [← ht2]; field_simp; ring
    rw [e]
    have h := mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ β * C₂)
    rw [mul_one] at h
    linarith
  have hN : ((2 ^ k / 2 : ℕ) : ℝ) = 2 ^ k / 2 := by
    rw [Nat.cast_div (dvd_pow_self 2 (Nat.pos_iff_ne_zero.1 hk)) (by norm_num)]; push_cast; ring
  have hgood : ∀ᵐ ω ∂P, ω ∉ B1 → ω ∉ B2 →
      Real.exp (-(ξ * k * Real.log 4) - C * t) * ℓ' <
        lenObs ξ (phiMN W P 0 n) (rectAB 1 1) ω := by
    filter_upwards [p18_step3_pathwise (ξ := ξ) hW hkn] with ω hω h1 h2'
    have hb : ∀ z ∈ (rectAB 1 1).toSet, |phiMN W P 0 k z ω| ≤ M := by
      intro z hz
      have hz' : z ∈ SupTail.ferniqueBox 0 1 := by rwa [← rectAB_one_toSet]
      exact (le_ciSup (SupTail.bddAbove_abs_of_compact
        (by rw [← rectAB_one_toSet]; exact MarkedRect.isCompact_toSet _) (hφk.cont ω))
        (⟨z, hz'⟩ : SupTail.ferniqueBox 0 1)).trans (not_le.1 h1).le
    have hR : ∀ b ∈ p18Idx k, ENNReal.ofReal x ≤
        rectLen ξ (fun z => phiMN W P k n z ω) (p18Blk k b) := by
      intro b hbm
      have : ¬ lenObs ξ (phiMN W P k n) (p18Blk k b) ω ≤ x := fun h =>
        h2' (mem_biUnion hbm h)
      exact ENNReal.ofReal_le_of_le_toReal (not_le.1 this).le
    have hmain := hω M x hx0 hb hR
    rw [hN, abs_of_pos hξ] at hmain
    -- `2^k/2 · x = e^{-Dt} ℓ' / 2`
    have hx2 : 2 ^ k / 2 * x = Real.exp (-(D * t)) * ℓ' / 2 := by
      rw [hxdef, inv_pow]; field_simp
    rw [hx2] at hmain
    have hL' : lenObs ξ (phiMN W P 0 n) (rectAB 1 1) ω ≥
        Real.exp (-(ξ * M)) * (Real.exp (-(D * t)) * ℓ' / 2) := by
      rw [Real.exp_neg, ge_iff_le, inv_mul_le_iff₀ (Real.exp_pos _)]; exact hmain
    refine lt_of_lt_of_le ?_ hL'
    have hhalf : Real.exp (-(Real.log 2 * t)) ≤ 1 / 2 := by
      have h := mul_le_mul_of_nonneg_left ht1 hl2.le
      rw [mul_one] at h
      have : Real.exp (-(Real.log 2 * t)) ≤ Real.exp (-Real.log 2) :=
        Real.exp_le_exp.2 (by linarith)
      have e : Real.exp (-Real.log 2) = 1 / 2 := by
        rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
      exact this.trans (le_of_eq e)
    have hexp : Real.exp (-(ξ * k * Real.log 4) - C * t) <
        Real.exp (-(ξ * M)) * Real.exp (-(D * t)) * Real.exp (-(Real.log 2 * t)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      refine Real.exp_lt_exp.2 ?_
      rw [hCdef]
      linarith [hM, ht1]
    calc Real.exp (-(ξ * k * Real.log 4) - C * t) * ℓ'
        < Real.exp (-(ξ * M)) * Real.exp (-(D * t)) * Real.exp (-(Real.log 2 * t)) * ℓ' :=
          mul_lt_mul_of_pos_right hexp hℓ'0
      _ ≤ Real.exp (-(ξ * M)) * Real.exp (-(D * t)) * (1 / 2) * ℓ' := by
          gcongr
      _ = Real.exp (-(ξ * M)) * (Real.exp (-(D * t)) * ℓ' / 2) := by ring
  -- the quantile
  by_contra hcon
  push Not at hcon
  have hq := prob_le_ellQ (ξ := ξ) (P := P) hφn.cont hφn.meas (rectAB 1 1)
    (ENNReal.ofReal_pos.2 hp0) (by rw [ENNReal.ofReal_lt_one]; linarith)
  have hsub : {ω | lenObs ξ (phiMN W P 0 n) (rectAB 1 1) ω ≤
      ellQ ξ P (phiMN W P 0 n) (rectAB 1 1) (ENNReal.ofReal p)} ≤ᵐ[P] (B1 ∪ B2 : Set Ω) := by
    filter_upwards [hgood] with ω hω hmem
    by_contra hnot
    simp only [mem_union, not_or] at hnot
    have h1 := hω hnot.1 hnot.2
    have h2' : lenObs ξ (phiMN W P 0 n) (rectAB 1 1) ω ≤ ellN ξ W P n (ENNReal.ofReal p) := hmem
    linarith
  have h3 := hq.trans ((measure_mono_ae hsub).trans (measure_union_le _ _))
  rw [← ofReal_measureReal (measure_ne_top P B1)] at h3
  have h4 := h3.trans (add_le_add le_rfl hB2)
  rw [← ENNReal.ofReal_add measureReal_nonneg (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h4
  linarith

/-- **DDDF Proposition 18** ((4.49)) from Step 1 (percolation), with Steps 2–4 proved:
`P(L^{(n)}_{3,1}(φ) ≥ e^s Λ_n(φ,p) ℓ_n(φ,p)) ≤ C e^{-c s²/log s}` for all `n ≥ 0`, `s > 2`. -/
theorem dddf_prop18_of_step1 {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (hξ : 0 < ξ)
    (h1 : P18Step1 ξ W P) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (n : ℕ) (s : ℝ), 2 < s →
      P {ω | Real.exp s * LambdaN ξ W P n (ENNReal.ofReal p) * ellN ξ W P n (ENNReal.ofReal p) ≤
          lenObs ξ (phiMN W P 0 n) (rectAB 3 1) ω} ≤
        ENNReal.ofReal (C * Real.exp (-c * s ^ 2 / Real.log s)) :=
  dddf_prop18_of_steps hW hξ h1 (dddf_p18_step3 hW hξ)

end DDDF
end LQGMetric
