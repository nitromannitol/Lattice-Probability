/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Frozen.IsBandVersion at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.HigherDimLFPP.Frozen.BandVec
import LatticeProb.Bonanno.HigherDimLFPP.Frozen.IsWhiteNoise

/-!
# Frozen definition: `IsBandVersion`

Anchor of the statement surface of the higher-dimensional LFPP formalization (manifest
`HigherDimLFPP/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`).
Source: `source/higher-dimensional-lfpp-limit.pdf`, (1.1)–(1.2) (the path integrals in (1.2) use a continuous version of `H_{ε,1}`).
Ruling H10.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace HigherDimLFPP

/-- `H` is a continuous version of the band field `z ↦ H_{a,b}(z) = W(k_{a,b,z})`. -/
structure IsBandVersion {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WN d → Ω → ℝ) (κ : Rd d → ℝ) (a b : ℝ) (H : Rd d → Ω → ℝ) : Prop where
  continuous : ∀ ω, Continuous fun z => H z ω
  measurable : ∀ z, Measurable (H z)
  ae_eq : ∀ z, H z =ᵐ[P] W (bandVec κ a b z)

end HigherDimLFPP
