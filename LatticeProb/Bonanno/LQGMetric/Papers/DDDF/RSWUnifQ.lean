/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.RSWUnifQ at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.RSWUnif

/-!
# DDDF Proposition 7 (`Prop:RSWphi`), quantile forms (3.36), (3.37)

Task P2-DDDFRSW2. DDDF arXiv:1904.08021, `tightness.tex` l. 653–662: for `[A,B] ⊂ (0,∞)`, one
`C > 0` such that for `(a,b), (a',b') ∈ [A,B]²`, `n ≥ 0`, `ε < 1/2`:
* (3.36) `ℓ^{(n)}_{a',b'}(ε/C) ≤ C ℓ^{(n)}_{a,b}(ε) e^{C√|log(ε/C)|}`;
* (3.37) `ℓ̄^{(n)}_{a',b'}(3ε^{1/C}) ≤ C ℓ̄^{(n)}_{a,b}(ε) e^{C√|log(ε/C)|}` (reading D-DDDF-8:
  DDDF print `3ε^C`; the proof, l. 789, and DF Thm 3.1 give `3ε^{1/C}`).

Quantiles are the generalized quantiles `ellQ` (`ℓ(p) = inf{x : P(L ≤ x) ≥ p}`) and
`ellBarQ` (`ℓ̄(p) = ℓ(1 − p)`), DDDF l. 465. (3.37) is stated for `3ε^{1/C} < 1`, where
`ℓ̄(3ε^{1/C})` is a genuine quantile (DDDF leave the range implicit). The deduction from the
probability forms `rsw_low_unif`, `rsw_high_unif` is the definition of the quantile.
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

/-- a real random variable is `≤ l` with probability `≥ p` for some `l`, when `p < 1` -/
theorem exists_prob_le_ge [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : Measurable X)
    {p : ℝ≥0∞} (hp0 : 0 < p) (hp : p < 1) : ∃ l : ℝ, p ≤ P {ω | X ω ≤ l} := by
  obtain ⟨l, hl⟩ := nonempty_setOf_le_measure_Iic (μ := P.map X) hp0 hp
  refine ⟨l, ?_⟩
  rw [mem_ofPred_eq, Measure.map_apply hX measurableSet_Iic] at hl
  exact hl

/-- **DDDF (3.36)** (small quantiles, uniform over `[A, B]`); also `C ≥ 1/2` (used for Cor 8). -/
theorem rsw_low_quantile (hW : IsWhiteNoise P W) (h10 : Prop10 ξ P W) {A B : ℝ} (hA : 0 < A)
    (hAB : A < B) :
    ∃ C : ℝ, 0 < C ∧ 1 / 2 ≤ C ∧ ∀ a b a' b' : ℝ, a ∈ Icc A B → b ∈ Icc A B → a' ∈ Icc A B →
      b' ∈ Icc A B → ∀ (n : ℕ) (ε : ℝ), 0 < ε → ε < 1 / 2 →
      ellQ ξ P (phiMN W P 0 n) (rectAB a' b') (ENNReal.ofReal (ε / C)) ≤
        C * ellQ ξ P (phiMN W P 0 n) (rectAB a b) (ENNReal.ofReal ε) *
          Real.exp (C * Real.sqrt |Real.log (ε / C)|) := by
  have := hW.isProbabilityMeasure
  obtain ⟨C, hC0, hC⟩ := rsw_low_unif (ξ := ξ) hW h10 hA hAB
  have hAI : A ∈ Icc A B := ⟨le_rfl, hAB.le⟩
  have hφ := fun n => isPhiVersion_phiMN hW (Nat.zero_le n)
  -- `C ≥ 1/2`: otherwise the conclusion of `rsw_low_unif` is a probability `> 1`
  have hC2 : 1 / 2 ≤ C := by
    by_contra hlt
    push Not at hlt
    obtain ⟨ε, hCε, hε2⟩ : ∃ ε : ℝ, C < ε ∧ ε < 1 / 2 := ⟨(C + 1 / 2) / 2, by linarith, by linarith⟩
    obtain ⟨l, hl⟩ := exists_prob_le_ge (P := P)
      (measurable_lenObs (ξ := ξ) (hφ 0).cont (hφ 0).meas (rectAB A A))
      (p := ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 (by linarith))
      (by rw [ENNReal.ofReal_lt_one]; linarith)
    have h := (hC A A A A hAI hAI hAI hAI 0 l ε (by linarith) hε2 hl).trans
      prob_le_one
    rw [ENNReal.ofReal_le_one, div_le_one hC0] at h
    linarith
  refine ⟨C, hC0, hC2, fun a b a' b' ha hb ha' hb' n ε hε hε2 => ?_⟩
  have hp0 : 0 < ENNReal.ofReal ε := ENNReal.ofReal_pos.2 hε
  have hp1 : ENNReal.ofReal ε < 1 := by rw [ENNReal.ofReal_lt_one]; linarith
  have h1 := prob_le_ellQ (ξ := ξ) (P := P) (hφ n).cont (hφ n).meas (rectAB a b) hp0 hp1
  have h2 := hC a b a' b' ha hb ha' hb' n _ ε hε hε2 h1
  unfold ellQ
  refine (le_measure_Iic_iff_lowerQuantile_le (ENNReal.ofReal_pos.2 (div_pos hε hC0))
    (by rw [ENNReal.ofReal_lt_one, div_lt_one hC0]; linarith)).1 ?_
  rw [Measure.map_apply (measurable_lenObs (hφ n).cont (hφ n).meas _) measurableSet_Iic]
  exact h2

/-- **DDDF (3.37)** (high quantiles, uniform over `[A, B]`; reading D-DDDF-8); also `C ≥ 1`. -/
theorem rsw_high_quantile (hW : IsWhiteNoise P W) (hξ : 0 ≤ ξ) (h10 : Prop10 ξ P W) {A B : ℝ}
    (hA : 0 < A) (hAB : A < B) :
    ∃ C : ℝ, 0 < C ∧ (∀ a b a' b' : ℝ, a ∈ Icc A B → b ∈ Icc A B → a' ∈ Icc A B →
      b' ∈ Icc A B → ∀ (n : ℕ) (ε : ℝ), 0 < ε → ε < 1 / 2 → 3 * ε ^ (1 / C) < 1 →
      ellBarQ ξ P (phiMN W P 0 n) (rectAB a' b') (ENNReal.ofReal (3 * ε ^ (1 / C))) ≤
        C * ellBarQ ξ P (phiMN W P 0 n) (rectAB a b) (ENNReal.ofReal ε) *
          Real.exp (C * Real.sqrt |Real.log (ε / C)|)) ∧ 1 ≤ C := by
  have := hW.isProbabilityMeasure
  obtain ⟨C, hC0, hC, hC1⟩ := rsw_high_unif (ξ := ξ) hW hξ h10 hA hAB
  have hφ := fun n => isPhiVersion_phiMN hW (Nat.zero_le n)
  refine ⟨C, hC0, fun a b a' b' ha hb ha' hb' n ε hε hε2 h3 => ?_, hC1⟩
  have hp0 : 0 < ENNReal.ofReal ε := ENNReal.ofReal_pos.2 hε
  have hp1 : ENNReal.ofReal ε < 1 := by rw [ENNReal.ofReal_lt_one]; linarith
  have hq0 : 0 < 1 - ENNReal.ofReal ε := tsub_pos_of_lt hp1
  have hq1 : 1 - ENNReal.ofReal ε < 1 :=
    ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hp0.ne'
  have h1 := prob_le_ellQ (ξ := ξ) (P := P) (hφ n).cont (hφ n).meas (rectAB a b) hq0 hq1
  have e1 : (1 : ℝ≥0∞) - ENNReal.ofReal ε = ENNReal.ofReal (1 - ε) := by
    rw [ENNReal.ofReal_sub _ hε.le, ENNReal.ofReal_one]
  rw [e1] at h1
  have h2 := hC a b a' b' ha hb ha' hb' n _ ε hε hε2 h1
  have hr0 : 0 < 3 * ε ^ (1 / C) := by have := Real.rpow_pos_of_pos hε (1 / C); positivity
  unfold ellBarQ ellQ
  have e3 : (1 : ℝ≥0∞) - ENNReal.ofReal (3 * ε ^ (1 / C)) = ENNReal.ofReal (1 - 3 * ε ^ (1 / C)) := by
    rw [ENNReal.ofReal_sub _ hr0.le, ENNReal.ofReal_one]
  rw [e1, e3]
  refine (le_measure_Iic_iff_lowerQuantile_le (ENNReal.ofReal_pos.2 (by linarith))
    (by rw [ENNReal.ofReal_lt_one]; linarith)).1 ?_
  rw [Measure.map_apply (measurable_lenObs (hφ n).cont (hφ n).meas _) measurableSet_Iic]
  exact h2

end DDDF
end LQGMetric
