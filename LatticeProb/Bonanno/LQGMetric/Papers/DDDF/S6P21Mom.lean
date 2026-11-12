/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P21Mom at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20BRatio

/-!
# DDDF Proposition 21, Step 3: negative moments of `L^{(K)}_{1,1}(φ)` (task P2-DDDF6c)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1001 ("using … (`eq:LowerTailsPhi`) for the
left-right crossing"): from Corollary 17, `P(L^{(n)}_{1,3} ≤ e^{-t} ℓ_n(p)) ≤ C e^{-ct²}` and
`L_{1,3} ≤ L_{1,1}`, the moments `E (ℓ_n(p) / L^{(n)}_{1,1})^s` are bounded uniformly in `n`
(`S6.invMoment_L11`). The integration of the tail is `T20B.lintegral_exp_le_of_tail_logsq`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} {ξ : ℝ}

namespace S6

lemma gauss_le_logsq {c t : ℝ} (hc : 0 < c) (ht : 2 < t) :
    Real.exp (-c * t ^ 2) ≤ Real.exp (-(c / 2) * t ^ 2 / Real.log t) := by
  have hl : 0 < Real.log t := Real.log_pos (by linarith)
  have hl2 : 1 / 2 ≤ Real.log t := by
    have h3 : Real.exp (1 / 2) ≤ t := by
      have : Real.exp (1 / 2) ≤ 2 := by
        have := Real.exp_one_lt_d9
        have h4 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
          rw [← Real.exp_add]; norm_num
        nlinarith [Real.exp_pos (1 / 2)]
      linarith
    rw [← Real.exp_le_exp, Real.exp_log (by linarith)]; exact h3
  refine Real.exp_le_exp.2 ?_
  rw [le_div_iff₀ hl]
  nlinarith [sq_nonneg t, mul_le_mul_of_nonneg_left hl2 (sq_nonneg t)]

/-- **Negative moments of `L_{1,1}`** (DDDF l. 1001, from Cor 17 = `eq:LowerTailsPhi`). -/
theorem invMoment_L11 (hW : IsWhiteNoise P W) (hξ : 0 < ξ) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ → ∀ s : ℝ, 0 < s → ∃ M : ℝ, ∀ n : ℕ,
      0 < ellN ξ W P n (ENNReal.ofReal p) ∧
      ∫⁻ ω, ENNReal.ofReal ((ellN ξ W P n (ENNReal.ofReal p) /
        lenObs ξ (phiMN W P 0 n) (rectAB 1 1) ω) ^ s) ∂P ≤ ENNReal.ofReal M := by
  have := hW.isProbabilityMeasure
  obtain ⟨p₁, hp₁, h17⟩ := dddf_cor17 (P := P) hW hξ
  refine ⟨min p₁ (1 / 2), lt_min hp₁ (by norm_num), fun p hp hpp s hs => ?_⟩
  obtain ⟨C, c, hC, hc, ht⟩ := h17 p hp (hpp.trans (min_le_left _ _))
  have hp2 : p ≤ 1 / 2 := hpp.trans (min_le_right _ _)
  set x₀ := T20B.tailX0 s 1 C (c / 2)
  refine ⟨Real.exp (s * x₀) + 1, fun n => ?_⟩
  have hφ := isPhiVersion_phiMN hW (Nat.zero_le n)
  have hq0 : 0 < ENNReal.ofReal p := ENNReal.ofReal_pos.2 hp
  have hq1 : ENNReal.ofReal p < 1 := by
    rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 (by linarith)
  set ℓ := ellN ξ W P n (ENNReal.ofReal p)
  have hℓ : 0 < ℓ := T20B.ellN_pos hW hq0 hq1 n
  refine ⟨hℓ, ?_⟩
  set L13 := lenObs ξ (phiMN W P 0 n) (rectAB 1 3)
  have hL13 : ∀ ω, 0 < L13 ω := fun ω => lenObs_pos hφ.cont _ (by norm_num [rectAB])
    (by norm_num [rectAB]) (by simp [rectAB, MarkedRect.crossWidth]) ω
  have hle : ∀ ω, L13 ω ≤ lenObs ξ (phiMN W P 0 n) (rectAB 1 1) ω :=
    T20B.lenObs_13_le_11 hφ.cont
  set X : Ω → ℝ := fun ω => max 0 (Real.log ℓ - Real.log (L13 ω))
  have hX0 : ∀ ω, 0 ≤ X ω := fun ω => le_max_left _ _
  have hXm : Measurable X := measurable_const.max
    (measurable_const.sub (Real.measurable_log.comp (measurable_lenObs hφ.cont hφ.meas _)))
  have hpt : ∀ ω, ENNReal.ofReal ((ℓ / lenObs ξ (phiMN W P 0 n) (rectAB 1 1) ω) ^ s) ≤
      ENNReal.ofReal (Real.exp (s * X ω)) := by
    intro ω
    refine ENNReal.ofReal_le_ofReal ?_
    have h0 := hL13 ω
    have h1 : ℓ / lenObs ξ (phiMN W P 0 n) (rectAB 1 1) ω ≤ ℓ / L13 ω :=
      div_le_div_of_nonneg_left hℓ.le h0 (hle ω)
    calc (ℓ / lenObs ξ (phiMN W P 0 n) (rectAB 1 1) ω) ^ s ≤ (ℓ / L13 ω) ^ s :=
          Real.rpow_le_rpow (div_nonneg hℓ.le (h0.trans_le (hle ω)).le) h1 hs.le
      _ = Real.exp (s * (Real.log ℓ - Real.log (L13 ω))) := by
          rw [Real.rpow_def_of_pos (div_pos hℓ h0), Real.log_div hℓ.ne' h0.ne']; ring_nf
      _ ≤ Real.exp (s * X ω) := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (le_max_right _ _) hs.le)
  have htail : ∀ t, 2 < t → P {ω | t ≤ X ω} ≤
      ENNReal.ofReal (1 * C * Real.exp (-(c / 2) * t ^ 2 / Real.log t)) := by
    intro t ht2
    have hsub : {ω | t ≤ X ω} ⊆ {ω | L13 ω ≤ Real.exp (-t) * ℓ} := by
      intro ω hω
      simp only [mem_setOf_eq] at hω ⊢
      have h2 : t ≤ Real.log ℓ - Real.log (L13 ω) := by
        rcases le_total 0 (Real.log ℓ - Real.log (L13 ω)) with h | h
        · simp only [X, max_eq_right h] at hω; exact hω
        · simp only [X, max_eq_left h] at hω; linarith
      rw [← Real.exp_log (hL13 ω), ← Real.exp_log hℓ, ← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith)
    refine (measure_mono hsub).trans ((ht n t (by linarith)).trans (ENNReal.ofReal_le_ofReal ?_))
    rw [one_mul]
    exact mul_le_mul_of_nonneg_left (gauss_le_logsq hc ht2) hC.le
  refine (lintegral_mono hpt).trans ?_
  exact T20B.lintegral_exp_le_of_tail_logsq hX0 hXm.aemeasurable hs zero_le_one hC (by positivity)
    htail

end S6
end DDDF
end LQGMetric
