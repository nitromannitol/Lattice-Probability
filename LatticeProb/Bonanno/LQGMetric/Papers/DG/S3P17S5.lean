/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P17S5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P17S4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DG Proposition 3.17: (eqn-lfpp-lower-show) `DGP317Show` (P2-DG317S)

Source: Ding–Gwynne arXiv:1807.01072, `metric-comparison-final.tex`, proof of Prop 3.17,
DG:1523–1591. `dgP317Show_of` proves `DGP317Show P W γ` (Papers/DG/S3P17.lean, the input of
`dgProp3_17_of`) from
* DG Lemma 3.11 at scale (`DGLem311Scaled`, `DGLem311ScaledV`, for a measure `μ` and a domain
  `Q ⊇ [−r, 1+r]²`; the hypotheses of `dg_lemma313`/`dg_lemma314` and of `dg_prop39`), and
* the lower bound `DGP317Lb P μ d Q` (DG `thm-diam` + Lemma 3.2, DG:1587–1589),
with Step 1's probabilities from DG Lemmas 3.13 (both orientations), 3.5 and 3.6 (proved:
`dg_lemma313`, `dg_lemma313V`, `dg_lemma35`, `dg_lemma36`) and the deterministic Steps 2–3
`p17s_good`. All events at `δ` (DGP317Show's parameter, DG's `ε^β`) with `ε = δ^{(2+γ)²}`.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LQGMetric.DG

open Blueprint WhiteNoise

variable {Ω : Type} [MeasurableSpace Ω]

lemma p17s_union2' {P : Measure Ω} {A B : Set Ω} {C₁ C₂ q₁ q₂ p δ : ℝ} (hC₁ : 0 ≤ C₁)
    (hC₂ : 0 ≤ C₂) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (h1 : P A ≤ ENNReal.ofReal (C₁ * δ ^ q₁))
    (h2 : P B ≤ ENNReal.ofReal (C₂ * δ ^ q₂)) (hp1 : p ≤ q₁) (hp2 : p ≤ q₂) :
    P (A ∪ B) ≤ ENNReal.ofReal ((C₁ + C₂) * δ ^ p) := by
  have := p17s_union2 hδ hδ1 h1 h2 hp1 hp2
  rwa [abs_of_nonneg hC₁, abs_of_nonneg hC₂] at this

lemma p17s_abs_bd {P : Measure Ω} {A : Set Ω} {C x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y)
    (h : P A ≤ ENNReal.ofReal (C * x)) : P A ≤ ENNReal.ofReal (|C| * y) :=
  h.trans (ENNReal.ofReal_le_ofReal (mul_le_mul (le_abs_self C) hxy hx (abs_nonneg C)))

end LQGMetric.DG
