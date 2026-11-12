/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L11R1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L11Scale
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdentWN

/-!
# DG L3.11 at `μ = μ_ĥ`: the locality hypothesis of the `μ_{ĥ^tr}` events (P2-DG105p, D116)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, DG:1267 ("`E_S^ε` is determined by
`ĥ^tr|_{S(2)}`"; `ĥ^tr` is built from the heat kernel killed outside `B(0,1/10)`, DG:944–953).

Open node 2(a) of handoff/P2-DG105l.md, stated exactly as it is consumed by the assembly of
`L311LevelInput` (S3L11R3): for the rescaled white noise `W ∘ wnScaleDy j c` (scale
`s = 2^{-j}`, offset `c`), the event `E_𝕊` of `μ_{ĥ^tr}` on the unit-frame square
`sqOne (1/32) l311UnitB (0,0) = [29/64, 35/64]²` is a.s. equal to an event of the white noise `W`
on `(0, s²) × (s · B_{1/10}([29/64,35/64]²) + c)`.

This file only states the hypothesis (to be proved in Papers/DG/S3L11Loc*).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DG

open WhiteNoise SupTail GMCIdent

variable {Ω : Type*} [MeasurableSpace Ω]

/-- the white-noise region on which the unit-frame event of the grid square with offset `c` at
scale `2^{-j}` depends: times `(0, s²)`, space `s · B_{1/10}(𝕊(1)) + c` (DG:1267) -/
def l311LocReg (j : ℕ) (c : ℂ) : Set (ℝ × ℂ) :=
  Ioo 0 (((2 : ℝ)⁻¹ ^ j) ^ 2) ×ˢ
    (affineC ((2 : ℝ)⁻¹ ^ j) c '' Metric.thickening (1 / 10) (sqOne (1 / 32) l311UnitB (0, 0)))

/-- **Open node 2(a) (locality of `E_𝕊` for `μ_{ĥ^tr}`, DG:1267)**: for every scale `2^{-j}`,
offset `c`, level `ε` and threshold `M`, the event `E_𝕊` (side-midpoint distances of
`[29/64,35/64]²` inside `𝕊(1)`) for `μ_{ĥ^tr}` of the rescaled noise `W ∘ wnScaleDy j c` is a.s.
equal to an event measurable for the white noise on `l311LocReg j c`. -/
def L311TrLocal (P : Measure Ω) {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (γ : ℝ) {y : ℂ}
    {b : ℝ} (hb : 0 < b) (hK : ∀ z ∈ ferniqueBox y b, Metric.ball z (1 / 10) ⊆ openSquare) :
    Prop :=
  ∀ (j : ℕ) (c : ℂ) (ε M : ℝ), ∃ A' : Set Ω, MeasurableSet[wnSigma W (l311LocReg j c)] A' ∧
    {ω | goodSq (muTr (dgN5_wnScaleDy hW j c).1 γ hb hK ω) ε (1 / 32) l311UnitB M (0, 0)} =ᵐ[P] A'

end DG
end LQGMetric
