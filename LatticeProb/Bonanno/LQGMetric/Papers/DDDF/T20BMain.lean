/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.T20BMain at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20BStep4
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20BTight
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20

/-!
# DDDF Theorem 20 from Step 4 (task P2-DDDFT20b)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1069–1213 (proof of `thm:AssTthm`). With Steps 1–3
and 5 and the final tightness argument proved, the only open input is Step 4 (`T20Step4`):
`dddf_thm20_of_step4` gives, for `p` small, `Λ_∞(φ, p) < ∞`, `sup_n Var log L^{(n)}_{1,1}(ψ) < ∞`
and the tightness of `log L^{(n)}_{1,1}(φ) − log λ_n`; `dddf_thm20_of_step4Visited` reduces further
to the visited-block part of Step 4 (`T20Step4Visited`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **DDDF Theorem 20 given Step 4** (`tightness.tex` l. 1069–1213). -/
theorem dddf_thm20_of_step4 (hW : IsWhiteNoise P W) (Q : PsiParams) (hQ : PsiSmall Q) {ξ : ℝ}
    (hξ : 0 < ξ) (h4 : T20Step4 ξ Q W P) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ →
      (∃ B : ℝ, ∀ n, LambdaN ξ W P n (ENNReal.ofReal p) ≤ B) ∧
      (∃ B : ℝ, ∀ n, Var[L24.logLenPsi ξ Q W P n; P] ≤ B) ∧
      ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ n : ℕ,
        P {ω | M < |Real.log (lenN ξ W P 1 1 n ω) - Real.log (lambdaN ξ W P n)|} ≤
          ENNReal.ofReal ε := by
  obtain ⟨p₁, hp₁, hrec⟩ := dddf_t20_recursive_of_step4 hW Q hQ h4
  obtain ⟨p₂, hp₂, htight⟩ := dddf_thm20_tight (P := P) hW hξ
  refine ⟨min (min p₁ p₂) (1 / 4), lt_min (lt_min hp₁ hp₂) (by norm_num), fun p hp hpp => ?_⟩
  have hpa : p ≤ p₁ := hpp.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hpb : p ≤ p₂ := hpp.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hp4 : p < 1 / 2 := lt_of_le_of_lt (hpp.trans (min_le_right _ _)) (by norm_num)
  obtain ⟨hΛ, -, hV⟩ := dddf_thm20_of_recursive hW Q ξ hp hp4 (hrec p hp hpa)
  exact ⟨hΛ, hV, htight p hp hpb hΛ⟩

/-- **DDDF Theorem 20 given the visited-block part of Step 4.** -/
theorem dddf_thm20_of_step4Visited (hW : IsWhiteNoise P W) (Q : PsiParams) (hQ : PsiSmall Q)
    {ξ : ℝ} (hξ : 0 < ξ) (hV : T20Step4Visited ξ Q W P) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ →
      (∃ B : ℝ, ∀ n, LambdaN ξ W P n (ENNReal.ofReal p) ≤ B) ∧
      (∃ B : ℝ, ∀ n, Var[L24.logLenPsi ξ Q W P n; P] ≤ B) ∧
      ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ n : ℕ,
        P {ω | M < |Real.log (lenN ξ W P 1 1 n ω) - Real.log (lambdaN ξ W P n)|} ≤
          ENNReal.ofReal ε :=
  dddf_thm20_of_step4 hW Q hQ hξ (dddf_t20_step4_of_visited hW Q hV)

end DDDF
end LQGMetric
