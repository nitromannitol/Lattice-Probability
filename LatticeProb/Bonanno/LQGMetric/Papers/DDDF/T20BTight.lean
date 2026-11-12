/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.T20BTight at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.C17
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18S2
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.RSWUnif

/-!
# DDDF Theorem 20, last sentence: tightness from bounded quantile ratios (task P2-DDDFT20b)

DDDF = Ding–Dubédat–Dunlap–Falconet, arXiv:1904.08021, `literature/src/1904.08021/tightness.tex`
l. 1212–1213: "Therefore `Λ_∞(ψ,p/2) < ∞` thus `Λ_∞(φ,p) < ∞` and by the tail estimates
(4.48) = `eq:LowerTailsPhi` and (4.49) = `eq:UpperTailsPhi`, the sequence
`(log L^{(n)}_{1,1}(φ) − log λ_n(φ))_{n ≥ 0}` is tight."

The implicit steps, written out here:
* the rectangle comparison `L_{1,3} ≤ L_{1,1} ≤ L_{3,1}` (`T20B.lenObs_13_le_11`,
  `T20B.lenObs_11_le_31`, from `rectLen_rectAB_mono`, D-DDDF-21);
* `ℓ_n(p) ≤ λ_n ≤ ℓ̄_n(p)` for `p ≤ 1/2` (`T20B.ellN_le_lambdaN`, `T20B.lambdaN_le_ellBarN`:
  `λ_n` is the lower `1/2`-quantile and quantiles are monotone), `ℓ_n(p) > 0`
  (`T20B.ellN_pos`), so `ℓ̄_n(p) ≤ Λ_n(p) ℓ_n(p)`;
* then Corollary 17 (`dddf_cor17`) bounds the lower tail and Proposition 18 (`dddf_prop18`) the
  upper tail.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} {ξ : ℝ}

namespace T20B

omit [MeasurableSpace Ω] in
/-- `L_{1,3} ≤ L_{1,1}` (a crossing of `[0,1]²` is one of `[0,1] × [0,3]`) -/
theorem lenObs_13_le_11 {Y : ℂ → Ω → ℝ} (hYc : ∀ ω, Continuous fun x => Y x ω) (ω : Ω) :
    lenObs ξ Y (rectAB 1 3) ω ≤ lenObs ξ Y (rectAB 1 1) ω :=
  ENNReal.toReal_mono (rectLen_ne_top _ (by simp [rectAB]) (by simp [rectAB]) (hYc ω))
    (rectLen_rectAB_mono zero_le_one le_rfl (by norm_num))

omit [MeasurableSpace Ω] in
/-- `L_{1,1} ≤ L_{3,1}` (a crossing of `[0,3] × [0,1]` contains one of `[0,1]²`) -/
theorem lenObs_11_le_31 {Y : ℂ → Ω → ℝ} (hYc : ∀ ω, Continuous fun x => Y x ω) (ω : Ω) :
    lenObs ξ Y (rectAB 1 1) ω ≤ lenObs ξ Y (rectAB 3 1) ω :=
  ENNReal.toReal_mono (rectLen_ne_top _ (by simp [rectAB]) (by simp [rectAB]) (hYc ω))
    (rectLen_rectAB_mono zero_le_one (by norm_num) le_rfl)

variable [IsProbabilityMeasure P]

theorem ellN_le_lambdaN {q : ℝ≥0∞} (hq0 : 0 < q) (hq : q ≤ 2⁻¹) (n : ℕ) :
    ellN ξ W P n q ≤ lambdaN ξ W P n :=
  ellQ_mono (rectAB 1 1) hq0 inv_two_lt_one' hq

theorem lambdaN_le_ellBarN {q : ℝ≥0∞} (hq0 : 0 < q) (hq : q ≤ 2⁻¹) (n : ℕ) :
    lambdaN ξ W P n ≤ ellBarN ξ W P n q := by
  refine ellQ_mono (rectAB 1 1) inv_two_pos'
    (ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hq0.ne') ?_
  calc (2⁻¹ : ℝ≥0∞) = 1 - 2⁻¹ := ENNReal.one_sub_inv_two.symm
    _ ≤ 1 - q := tsub_le_tsub_left hq 1

theorem ellN_pos (hW : IsWhiteNoise P W) {q : ℝ≥0∞} (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    0 < ellN ξ W P n q := by
  have hφ := isPhiVersion_phiMN hW (Nat.zero_le n)
  by_contra h
  push Not at h
  have h1 := prob_le_ellQ (ξ := ξ) (P := P) hφ.cont hφ.meas (rectAB 1 1) hq0 hq1
  have he : {ω | lenObs ξ (phiMN W P 0 n) (rectAB 1 1) ω ≤
      ellQ ξ P (phiMN W P 0 n) (rectAB 1 1) q} = ∅ := by
    ext ω
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
    exact h.trans_lt (lenObs_pos hφ.cont _ (by simp [rectAB]) (by simp [rectAB])
      (by simp [rectAB, MarkedRect.crossWidth]) ω)
  rw [he, measure_empty] at h1
  exact hq0.ne' (le_antisymm h1 bot_le)

/-- `C e^{-c s} ≤ ε/2` once `s ≥ log(2C/ε)/c` -/
theorem mul_exp_neg_le_half {C c ε s : ℝ} (hC : 0 < C) (hc : 0 < c) (hε : 0 < ε)
    (hs : Real.log (2 * C / ε) / c ≤ s) : C * Real.exp (-(c * s)) ≤ ε / 2 := by
  have h1 : Real.log (2 * C / ε) ≤ c * s := by
    rw [div_le_iff₀ hc] at hs; linarith
  calc C * Real.exp (-(c * s)) ≤ C * Real.exp (-Real.log (2 * C / ε)) := by
        gcongr
    _ = ε / 2 := by
        rw [Real.exp_neg, Real.exp_log (by positivity)]
        field_simp

end T20B

open T20B in
/-- **DDDF Theorem 20, tightness** (`tightness.tex` l. 1212–1213): for `p` small, if the quantile
ratios `Λ_n(φ, p)` are bounded then `(log L^{(n)}_{1,1}(φ) − log λ_n)_n` is tight. -/
theorem dddf_thm20_tight (hW : IsWhiteNoise P W) (hξ : 0 < ξ) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ →
      (∃ B : ℝ, ∀ n, LambdaN ξ W P n (ENNReal.ofReal p) ≤ B) →
      ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ n : ℕ,
        P {ω | M < |Real.log (lenN ξ W P 1 1 n ω) - Real.log (lambdaN ξ W P n)|} ≤
          ENNReal.ofReal ε := by
  have := hW.isProbabilityMeasure
  obtain ⟨p₁, hp₁, h17⟩ := dddf_cor17 (P := P) hW hξ
  obtain ⟨p₂, hp₂, h18⟩ := dddf_prop18 (P := P) hW hξ
  refine ⟨min (min p₁ p₂) (1 / 4), lt_min (lt_min hp₁ hp₂) (by norm_num),
    fun p hp hpp hBd ε hε => ?_⟩
  obtain ⟨B, hB⟩ := hBd
  have hpa : p ≤ p₁ := hpp.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hpb : p ≤ p₂ := hpp.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hp4 : p ≤ 1 / 4 := hpp.trans (min_le_right _ _)
  obtain ⟨C₁, c₁, hC₁, hc₁, t17⟩ := h17 p hp hpa
  obtain ⟨C₂, c₂, hC₂, hc₂, t18⟩ := h18 p hp hpb
  set B' : ℝ := max B 1 with hB'
  have hB'pos : 0 < B' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set s : ℝ := max 3 (max (Real.log (2 * C₁ / ε) / c₁) (Real.log (2 * C₂ / ε) / c₂)) with hsdef
  have hs3 : 3 ≤ s := le_max_left _ _
  have hs1 : Real.log (2 * C₁ / ε) / c₁ ≤ s :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hs2 : Real.log (2 * C₂ / ε) / c₂ ≤ s :=
    (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨s + Real.log B', fun n => ?_⟩
  set q : ℝ≥0∞ := ENNReal.ofReal p with hqdef
  have hq0 : 0 < q := ENNReal.ofReal_pos.2 hp
  have hq2 : q ≤ 2⁻¹ := by
    rw [hqdef, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_inv_of_pos (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hq1 : q < 1 := hq2.trans_lt inv_two_lt_one'
  have hφ := isPhiVersion_phiMN hW (Nat.zero_le n)
  have hℓpos : 0 < ellN ξ W P n q := ellN_pos hW hq0 hq1 n
  have hℓlam := ellN_le_lambdaN (ξ := ξ) (W := W) (P := P) hq0 hq2 n
  have hlamℓb := lambdaN_le_ellBarN (ξ := ξ) (W := W) (P := P) hq0 hq2 n
  have hΛ : LambdaN ξ W P n q ≤ B' := (hB n).trans (le_max_left _ _)
  have hratio : ellBarN ξ W P n q / ellN ξ W P n q ≤ B' :=
    le_trans (Finset.le_sup' (fun k => ellBarN ξ W P k q / ellN ξ W P k q)
      (Finset.self_mem_range_succ n)) hΛ
  have hℓb : ellBarN ξ W P n q ≤ B' * ellN ξ W P n q := (div_le_iff₀ hℓpos).1 hratio
  have hlampos : 0 < lambdaN ξ W P n := hℓpos.trans_le hℓlam
  have hsub : {ω | s + Real.log B' <
      |Real.log (lenN ξ W P 1 1 n ω) - Real.log (lambdaN ξ W P n)|} ⊆
      {ω | lenObs ξ (phiMN W P 0 n) (rectAB 1 3) ω ≤
          Real.exp (-s) * ellQ ξ P (phiMN W P 0 n) (rectAB 1 1) q} ∪
      {ω | Real.exp s * LambdaN ξ W P n q * ellN ξ W P n q ≤
          lenObs ξ (phiMN W P 0 n) (rectAB 3 1) ω} := by
    intro ω hω
    have hL : 0 < lenN ξ W P 1 1 n ω := lenObs_pos hφ.cont _ (by simp [rectAB])
      (by simp [rectAB]) (by simp [rectAB, MarkedRect.crossWidth]) ω
    simp only [mem_ofPred_eq] at hω
    rcases lt_abs.1 hω with h | h
    · right
      have hlt : Real.exp s * B' * lambdaN ξ W P n < lenN ξ W P 1 1 n ω := by
        refine (Real.log_lt_log_iff (by positivity) hL).1 ?_
        rw [Real.log_mul (by positivity) hlampos.ne', Real.log_mul (Real.exp_pos _).ne'
          hB'pos.ne', Real.log_exp]
        linarith
      simp only [mem_ofPred_eq]
      calc Real.exp s * LambdaN ξ W P n q * ellN ξ W P n q
          ≤ Real.exp s * B' * lambdaN ξ W P n := by
            have h0 : 0 ≤ Real.exp s * B' := by positivity
            calc Real.exp s * LambdaN ξ W P n q * ellN ξ W P n q
                ≤ Real.exp s * B' * ellN ξ W P n q := by gcongr
              _ ≤ Real.exp s * B' * lambdaN ξ W P n := by gcongr
        _ ≤ lenN ξ W P 1 1 n ω := hlt.le
        _ ≤ lenObs ξ (phiMN W P 0 n) (rectAB 3 1) ω := lenObs_11_le_31 hφ.cont ω
    · left
      have hlt : lenN ξ W P 1 1 n ω < Real.exp (-s) * B'⁻¹ * lambdaN ξ W P n := by
        refine (Real.log_lt_log_iff hL (by positivity)).1 ?_
        rw [Real.log_mul (by positivity) hlampos.ne', Real.log_mul (Real.exp_pos _).ne'
          (inv_pos.2 hB'pos).ne', Real.log_exp, Real.log_inv]
        linarith
      simp only [mem_ofPred_eq]
      calc lenObs ξ (phiMN W P 0 n) (rectAB 1 3) ω ≤ lenN ξ W P 1 1 n ω :=
            lenObs_13_le_11 hφ.cont ω
        _ ≤ Real.exp (-s) * B'⁻¹ * lambdaN ξ W P n := hlt.le
        _ ≤ Real.exp (-s) * B'⁻¹ * (B' * ellN ξ W P n q) := by
            gcongr; exact hlamℓb.trans hℓb
        _ = Real.exp (-s) * ellQ ξ P (phiMN W P 0 n) (rectAB 1 1) q := by
            simp only [ellN]; field_simp
  have hs0 : 0 < s := by linarith
  have hlog : 0 < Real.log s := Real.log_pos (by linarith)
  have hlogs : Real.log s ≤ s := (Real.log_le_sub_one_of_pos hs0).trans (by linarith)
  have hb1 : C₁ * Real.exp (-c₁ * s ^ 2) ≤ ε / 2 := by
    refine le_trans ?_ (mul_exp_neg_le_half hC₁ hc₁ hε hs1)
    gcongr
    have hss : s ≤ s ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hss hc₁.le]
  have hb2 : C₂ * Real.exp (-c₂ * s ^ 2 / Real.log s) ≤ ε / 2 := by
    refine le_trans ?_ (mul_exp_neg_le_half hC₂ hc₂ hε hs2)
    gcongr
    rw [div_le_iff₀ hlog]
    nlinarith [mul_le_mul_of_nonneg_left hlogs (by positivity : (0 : ℝ) ≤ c₂ * s)]
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (C₁ * Real.exp (-c₁ * s ^ 2)) +
        ENNReal.ofReal (C₂ * Real.exp (-c₂ * s ^ 2 / Real.log s)) :=
          add_le_add (t17 n s hs0) (t18 n s (by linarith))
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
          add_le_add (ENNReal.ofReal_le_ofReal hb1) (ENNReal.ofReal_le_ofReal hb2)
    _ = ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

end DDDF
end LQGMetric
