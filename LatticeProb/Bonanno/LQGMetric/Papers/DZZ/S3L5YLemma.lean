/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L5YLemma at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5Main
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5YMain

/-!
# DZZ Lemma 3.5 (P2-DZZ35X)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex`, Lemma 3.5 and its proof
l. 1054–1083): `DZZLemma35U` from `dzz_lemma35U_of_crossing` (S3L5Main) and the crossing claim
`l35Crossing_holds` (S3L5YMain).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory

namespace LQGMetric
namespace DZZ

open WhiteNoise

/-- **DZZ Lemma 3.5.** -/
theorem dzz_lemma35U {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ξ ξd : ℝ} (hξ : 0 < ξ)
    (hξd : ξd < dzzCMc γ) : DZZLemma35U P γ W ξ ξd :=
  dzz_lemma35U_of_crossing hW hγ hγ2 l35Crossing_holds hξ hξd

end DZZ
end LQGMetric
