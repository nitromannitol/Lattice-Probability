/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.MatedCRTAffineReroot at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTFirstHit

/-!
# Frozen definition: `MatedCRT.affineReroot`

`ψ⁻¹ ∘ c` re-rooted at the hitting time of `ψ(0)`, time `s²t`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- The curve `ψ⁻¹ ∘ c` re-rooted at the hitting time of `z₀ = ψ(0)` and reparametrized by Lebesgue measure, for
`ψ w = z₀ + s e^{iφ} w`: `t ↦ (s e^{iφ})⁻¹ (c(τ_{z₀} + s² t) − z₀)`. -/
def affineReroot (z₀ : ℂ) (s φ : ℝ) (c : C(ℝ, ℂ)) : C(ℝ, ℂ) :=
  ⟨fun t => (((s : ℂ) * Complex.exp (φ * Complex.I))⁻¹) * (c (firstHit c z₀ + s ^ 2 * t) - z₀), by fun_prop⟩

end MatedCRT

end MatedCRTHarmonic
