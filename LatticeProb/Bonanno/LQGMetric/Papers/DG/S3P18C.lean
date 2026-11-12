/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P18C at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P18B
import LatticeProb.Bonanno.LQGMetric.Papers.DG.BallMass

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DG Proposition 3.22 for a field `hV` at `𝕍`-scale, from the `ĥ`-form and L3.7

Source: Ding–Gwynne arXiv:1807.01072, `metric-comparison-final.tex`, Prop 3.22
(`prop-lfpp-upper0`, DG:1722–1727), proof DG:1729–1731 ("By Lemma 3.7, it suffices to prove …
with `ĥ_{ε^β}` in place of `h_{ε^β}`", then `δ = ε^β`) and DG:1772. At `𝕍`-scale (D105 item 1)
`𝕊 ↦ [1/3,2/3]² = p39Sq c₀ (1/3)`, `𝕊(1/2) ↦ [1/6,5/6]² = p39Box c₀ (1/3) (1/6)`, `c₀ = (1+i)/3`.

* `DGLem37V P W hV S` — DG L3.7 (`lem-circle-avg-approx`, DG:1096–1102) at `𝕍`-scale with
  `z = w` and polynomial rate (weaker than DG's superpolynomial rate).
* `dg_prop322_V` — w.p. `≥ 1 − Cδ^p`, `max_{z,w} D^δ_{hV}(z, w; [1/6,5/6]²) ≤ δ^{λ − ζ}`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DG

open WhiteNoise

variable {Ω : Type} [MeasurableSpace Ω]

/-- **DG Lemma 3.7 at `𝕍`-scale** (with `z = w`, polynomial rate): `|hV_δ − ĥ_δ| ≤ ζ log δ⁻¹`
on `S` -/
def DGLem37V (P : Measure Ω) (W : WNSpace → Ω → ℝ) (hV : ℝ → ℂ → Ω → ℝ) (S : Set ℂ) : Prop :=
  ∀ ζ : ℝ, 0 < ζ → ∃ p K δ₀ : ℝ, 0 < p ∧ 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
    P {ω | ¬ ∀ x ∈ S, |hV δ x ω - DDDF.phiVer W P δ 1 x ω| ≤ ζ * Real.log δ⁻¹} ≤
      ENNReal.ofReal (K * δ ^ p)

/-- `c₀ = (1 + i)/3`, `T(0) = c₀` for `T(z) = (z + 1 + i)/3` -/
def p18c0 : ℂ := ⟨1 / 3, 1 / 3⟩

end LQGMetric.DG
