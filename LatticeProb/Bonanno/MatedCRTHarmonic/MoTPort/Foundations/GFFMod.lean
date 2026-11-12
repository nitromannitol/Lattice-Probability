/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTPort.Foundations.GFFMod at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.GFF
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import LatticeProb.Bonanno.QuantumZipper.Common.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import LatticeProb.Bonanno.LQGMetric.Field.HeatMollifyVar
import LatticeProb.Bonanno.LQGMetric.Field.HeatMollifyCont
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Bounded boundary data; fields modulo `cℤ`; lateral part

* `exists_isGFFBoundary_of_bounded`: `exists_isGFFBoundary` for bounded harmonic data (the case of
  IG1's piecewise-constant boundary data).
* `φ₀` and `normMod c h`: the normalized
  representative of `h` modulo `cℤ`, `(h, φ₀) ∈ [0,c)`, with `φ₀` a fixed bump of mass one
  (IG4 = arXiv:1302.4738, L1103: "fix φ₀ ∈ C_c^∞ with ∫ φ₀ = 1"; `φ₀ := LQGMetric.refTest`).
  Lemmas, all **exact for every field**: measurability, `normMod c (h + c k) = normMod c h`,
  `(normMod c h, φ₀) ∈ [0,c)`, `normMod c h = h` on the transversal, idempotence; the a.s.
  versions for a whole-plane GFF are kept as corollaries. The whole-plane GFF modulo `rℤ`
  (independent uniform constant, IG4 L1103–1108) is `IsWPGFFMod` in `GFFWP.lean`.
* `lateralPartC h := h − (z ↦ h_{|z|}(0))` (DMS Lemma 4.2–4.4, L1996, L2029, L2187: the
  lateral part of a whole-plane field); junk: the radial function is replaced by `0` when it is
  not locally integrable (mathlib `Distribution.ofFun`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace Metric
open scoped Distributions

namespace MatedCRTHarmonic.MoTPort

open LQGMetric GFFBdry

/-! ## Fields modulo `cℤ` -/

namespace NormMod

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

end NormMod

/-! ## Lateral part of a whole-plane field -/

/-- the radial part `z ↦ h_{|z|}(0)` of a field, as a function -/
def radialFun (h : Field) : ℂ → ℝ := fun z => circleAvg h ‖z‖ 0

/-- the lateral part `h − h_{|·|}(0)` (DMS Lemmas 4.2–4.4); the radial part is replaced by the
junk value `0` when `radialFun h` is not locally integrable -/
def lateralPartC (h : Field) : Field := h - ofFunC (radialFun h)

lemma lateralPartC_apply {h : Field} (hr : LocallyIntegrable (radialFun h) volume) (φ : TestC) :
    lateralPartC h φ = h φ - ∫ x, φ x * radialFun h x := by
  show h φ - ofFunC (radialFun h) φ = _
  rw [ofFunC, Distribution.ofFun_apply (hr.locallyIntegrableOn _)]
  rfl

end MatedCRTHarmonic.MoTPort
