/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Frozen.IsLFPPExponent at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.HigherDimLFPP.Frozen.LfppDistance
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Frozen definition: `IsLFPPExponent`

Anchor of the statement surface of the higher-dimensional LFPP formalization (manifest
`HigherDimLFPP/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`).
Source: `source/higher-dimensional-lfpp-limit.pdf`, (1.3).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set

namespace HigherDimLFPP

/-- `λ` is the LFPP exponent at `ζ` (1.3): `log D^ζ_{ε,d} / log ε → λ` in probability as `ε ↓ 0`,
where `D^ζ_{ε,d} = lfppDistance d ζ (H ε)`. -/
def IsLFPPExponent {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (H : ℝ → Rd d → Ω → ℝ)
    (P : Measure Ω) (ζ lam : ℝ) : Prop :=
  TendstoInMeasure P
    (fun ε ω => Real.log (lfppDistance d ζ (fun z => H ε z ω)) / Real.log ε) (𝓝[>] 0)
    (fun _ => lam)

end HigherDimLFPP
