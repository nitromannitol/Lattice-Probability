/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLQGMetric.Frozen.IsDistanceExponent at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.HigherDimLFPP.Frozen.IsLFPPKernel
import LatticeProb.Bonanno.HigherDimLFPP.Frozen.IsBandVersion
import LatticeProb.Bonanno.HigherDimLFPP.Frozen.IsLFPPExponent

/-!
# Frozen definition: `IsDistanceExponent`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M7, M9, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[S] l. 50 ("the continuum LFPP distance exponent `Q = Q(ξ)`"), l. 92–93 ("kernel independence of `Q(ξ)`
[is] as in [1, Section 1.2]"), [1] (1.7) and footnote (`Q(ξ)` of [2, Prop 1.1], independent of the
kernel), [2] Proposition 1.1 (`λ_n = 2^{-(1-ξQ)n + o(n)}`); ruling M7: `Q` is the LFPP distance exponent at
`ξ` for every nonnegative admissible kernel and every white-noise realization, in HigherDimLFPP's frozen
model (`IsLFPPExponent`: `log D_ε / log ε → 1 - ξQ` in probability, `D_ε` the cube-internal distance from
`0` to `e₁` for the band field `H_{ε,1}`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- `Q` is the (kernel-independent) LFPP distance exponent at `ξ`: for every admissible kernel and
every white-noise realization, `log D_ε / log ε → 1 - ξ Q` in probability. -/
def IsDistanceExponent (d : ℕ) (ξ Q : ℝ) : Prop :=
  ∀ κ : Rd d → ℝ, HigherDimLFPP.IsLFPPKernel κ →
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : HigherDimLFPP.WN d → Ω → ℝ),
    HigherDimLFPP.IsWhiteNoise P W →
  ∀ H : ℝ → Rd d → Ω → ℝ, (∀ ε ∈ Ioo (0 : ℝ) 1, HigherDimLFPP.IsBandVersion P W κ ε 1 (H ε)) →
    HigherDimLFPP.IsLFPPExponent H P ξ (1 - ξ * Q)

end HigherDimLQGMetric
