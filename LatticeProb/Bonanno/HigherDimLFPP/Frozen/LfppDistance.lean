/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Frozen.LfppDistance at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.HigherDimLFPP.Frozen.IsAdmissiblePath
import LatticeProb.Bonanno.HigherDimLFPP.Frozen.LfppLength

/-!
# Frozen definition: `lfppDistance`

Anchor of the statement surface of the higher-dimensional LFPP formalization (manifest
`HigherDimLFPP/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`).
Source: `source/higher-dimensional-lfpp-limit.pdf`, (1.2).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLFPP

/-- `D^ζ = inf_{P : 0 → e₁, P ⊂ U} ∫_P e^{ζ φ(z)} |dz|` (1.2), for a field `φ` (applied to
`φ = H_{ε,1}`). -/
def lfppDistance (d : ℕ) (ζ : ℝ) (φ : Rd d → ℝ) : ℝ :=
  ⨅ γ : {γ : ℝ → Rd d // IsAdmissiblePath d γ}, lfppLength ζ φ γ.1

end HigherDimLFPP
