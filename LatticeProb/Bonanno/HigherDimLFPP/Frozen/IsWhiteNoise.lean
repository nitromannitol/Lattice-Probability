/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Frozen.IsWhiteNoise at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.HigherDimLFPP.Frozen.WN
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.HasLaw

/-!
# Frozen definition: `IsWhiteNoise`

Anchor of the statement surface of the higher-dimensional LFPP formalization (manifest
`HigherDimLFPP/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`).
Source: `source/higher-dimensional-lfpp-limit.pdf`, §1.1.  Ruling H10 (white noise as the isonormal Gaussian process on `WN d`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory

namespace HigherDimLFPP

/-- `W` is white noise: an isonormal Gaussian process on `L²(ℝ × ℝ^d)`.  Every finite linear
combination `∑ cᵢ W(fᵢ)` is centered Gaussian with variance `‖∑ cᵢ fᵢ‖²`. -/
structure IsWhiteNoise {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WN d → Ω → ℝ) : Prop where
  measurable : ∀ f, Measurable (W f)
  hasLaw : ∀ {ι : Type} [Fintype ι] (f : ι → WN d) (c : ι → ℝ),
    HasLaw (fun ω => ∑ i, c i * W (f i) ω) (gaussianReal 0 (‖∑ i, c i • f i‖ ^ 2).toNNReal) P

end HigherDimLFPP
