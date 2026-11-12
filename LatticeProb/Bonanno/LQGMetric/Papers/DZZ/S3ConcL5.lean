/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3ConcL5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3ConcL4
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3ConcJ3

/-!
# DZZ Proposition 3.17 at `μIn` (P2-DZZI3)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`) Prop 3.17 (l. 1519–1652) at the measure `μIn`, with
no open input: DZZ's `𝓔*` estimates (l. 1577–1579, 1637–1639) are `dzzEStar1_dzzMuIn` and
`dzzEStar2_unif` (S3ConcJ3, P2-DZZI2), applied to the canonical white noise
(`isWhiteNoise_wnCanon`); `dzzProp317_dzzMuIn_of_eStar` (S3ConcL4) does the rest.

* `dzzEStar2Le_dzzMuIn`: `DZZEStar2Le` (S3ConcL3) with `α = 2/γ` (as `dzzEStar2_dzzMuIn`).
* **`dzzProp317_dzzMuIn`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace LQGMetric
namespace DZZ

open WhiteNoise

universe u

/-- **`DZZEStar2Le` at `μIn`** with `α = 2/γ` (the proof of `dzzEStar2_dzzMuIn`, S3ConcJ3). -/
theorem dzzEStar2Le_dzzMuIn {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ξ : ℝ}
    (hξ : 0 < ξ) (hξc : ξ < dzzCMc γ) : DZZEStar2Le P γ W ξ := by
  obtain ⟨c, hc, h⟩ := dzzEStar2_unif.{u, u} hW hγ hγ2 hξ hξc
  refine ⟨2 / γ, by positivity, le_rfl, c, hc, fun A B hAB => ?_⟩
  obtain ⟨δ₀, hδ₀, h₀⟩ := h (2 / γ) (by positivity) A B hAB
  exact ⟨δ₀, hδ₀, fun δ hδ => h₀ δ hδ hW⟩

/-- **DZZ Proposition 3.17 at `μIn`** (l. 1519–1652), for `0 < ξ < C_Mc(γ)`. -/
theorem dzzProp317_dzzMuIn {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {ξ : ℝ} (hξ : 0 < ξ) (hξc : ξ < dzzCMc γ) :
    DZZProp317 P (dzzMuIn γ W) ξ :=
  dzzProp317_dzzMuIn_of_eStar hW hγ hγ2 hξ hξc
    (dzzEStar1_dzzMuIn (isWhiteNoise_wnCanon hW) hγ hγ2 hξ hξc)
    (dzzEStar2Le_dzzMuIn (isWhiteNoise_wnCanon hW) hγ hγ2 hξ hξc)

end DZZ
end LQGMetric
