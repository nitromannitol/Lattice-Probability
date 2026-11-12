/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S2BridgeLemmas at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2Bridge
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L6EtaVar
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L8Tele

/-!
# DZZ Lemmas 2.5, 2.7, 2.8 unconditionally (task P2-DZZPRE2)

The conditional versions (`dzz_lemma25`, `dzz_lemma27`, `dzz_lemma28`, hypothesis
`BridgeShellBound C`) specialized to `bridgeShellBound_256` (D62 route (1)).
Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 455–461 (L2.5), l. 540–556 (L2.7),
l. 584–604 (L2.8).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace LQGMetric
namespace DZZ

open KilledHeat WhiteNoise SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

universe u

/-- **DZZ Lemma 2.7** (continuous versions, unconditional). -/
theorem dzz_lemma27_uncond :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W → ∀ Z : ℕ → ℂ → Ω → ℝ,
      (∀ j ω, Continuous fun x => Z j x ω) →
      (∀ j x, Z j x =ᵐ[P] fun ω => tildeHInf W ((1 / 2 : ℝ) ^ j) x ω -
        etaInf W ((1 / 2 : ℝ) ^ j) x ω) →
      ∀ lam : ℝ, 0 ≤ lam →
        P.real {ω | ∃ v ∈ ferniqueBox 0 1, ∃ j : ℕ, lam ≤ |Z j v ω|} ≤
          C * Real.exp (-lam ^ 2 / C) :=
  dzz_lemma27.{u} (by norm_num) bridgeShellBound_256

/-- **DZZ Lemma 2.8** on `𝕍^ξ` (continuous versions, unconditional). -/
theorem dzz_lemma28_uncond {ξ : ℝ} (hξ : 0 < ξ) (hξ2 : ξ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W → ∀ Z : ℕ → ℂ → Ω → ℝ,
      (∀ j ω, Continuous fun x => Z j x ω) →
      (∀ j x, Z j x =ᵐ[P] fun ω => phi W ((1 / 2 : ℝ) ^ j) 1 x ω -
        etaInf W ((1 / 2 : ℝ) ^ j) x ω) →
      ∀ lam : ℝ, 0 ≤ lam →
        P.real {ω | ∃ v ∈ ferniqueBox ⟨ξ, ξ⟩ (1 - 2 * ξ), ∃ j : ℕ, lam ≤ |Z j v ω|} ≤
          C * Real.exp (-lam ^ 2 / C) :=
  dzz_lemma28.{u} (by norm_num) bridgeShellBound_256 hξ hξ2

end DZZ
end LQGMetric
