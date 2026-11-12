/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCIdent5Ind at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent4Fact
import LatticeProb.Bonanno.LQGMetric.Statement.Dimension
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Instances.Rat
import Mathlib.Analysis.SpecificLimits.Basic
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent3Wn
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L5Kernel
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatMeas
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Topology.Path
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import LatticeProb.Bonanno.LQGMetric.Papers.DG.XiQBound
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.DualExistence
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCSqExist
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.Measurability
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Kernel.Basic
import LatticeProb.Bonanno.QuantumZipper.LQG.Measures
import Mathlib.Logic.Equiv.List
import LatticeProb.Bonanno.QuantumZipper.LQG.Local
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCMass
import Mathlib.Analysis.SpecialFunctions.Sqrt
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2Bridge
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L7Trunc
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseKernel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L7

/-!
DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` (eq-def-tilde-M), l. 676–683) define
`M̃_{γ,δ}(B) = lim_n ∫_B e^{γ h̃^δ_{2^{-n}}(z) − γ²/2 Var h̃^δ_{2^{-n}}(z)} dz`; the band fields
`h̃^δ_{2^{-n}} = √π ∫_{(4^{-n}, δ²) × 𝕍} p_𝕍(s/2; z, w) W(dw, ds)` only use the white noise on the
fine scales `s < δ²`, so `M̃_{γ,δ}` is independent of `h̃_δ` (used in DZZ Prop. 3.2 and for the
moment bounds (eq-LQG-positive-moment), (eq-LQG-negative-moment)). Here, for `δ = 2^{-m}`:

* `bandVer` (`dyVer` of the band field `h̃^δ_{2^{-n}}`) is `Borel ⊗ 𝓖_{fine}`-measurable,
  `𝓖_{fine} = wnSigma W (coarseSet m)ᶜ`, and a version of the band field (`bandVer_ae_eq`; the
  dyadic increments are controlled by DZZ Lemma 2.5 through `h̃^δ_ε = h̃_ε − h̃_δ`);
* `fineDens`: the band density built from `bandVer`; a.s. it equals the density of `bandMeas`
  for a.e. `z` (`ae_ae_bandDens_eq`, Fubini);
* **`exists_fine_version_integral_tildeM`**: for `f ∈ C_c(𝕍)`, `∫ f dM̃_{γ,δ}` has a
  `𝓖_{fine}`-measurable version (limit of `∫ f · fineDens dz`, by `ae_isVagueLimitOn_bandMeas`);
  hence it is independent of `𝓖_{coarse} ∋ h̃_δ` (**`indep_integral_tildeM`**, from
  `indep_wnSigma_compl`).
* Item 3: a zero-boundary GFF on `𝕍` exists on a `Type`-valued space
  (`QuantumZipper.K3.exists_zeroGFFOn`), so the GFF hypothesis of the GMCIdent4 results can be
  dropped (`ae_isVagueLimitOn_bandMeas'`, `isLGDExponent_iff_wn'`).

Own glue (D85); the measurable-version argument is the one of `GMCIdentTilde` (Berestycki
arXiv:1506.09113 §4, l. 649).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric QuantumZipper
open scoped ENNReal NNReal RealInnerProductSpace

namespace LQGMetric
namespace GMCIdent5

open KilledHeat WhiteNoise DZZ GMCIdent GMCIdent2 GMCIdent3 GMCIdent4

variable {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} {W : WNSpace → Ω' → ℝ}

/-! ## Item 3: a zero-boundary GFF on `𝕍` exists -/

/-- a zero-boundary GFF on the open unit square, on a `Type`-valued sample space
(`QuantumZipper.K3.exists_zeroGFFOn`) -/
theorem exists_zeroGFF_openSquare :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : Ω → Measure ℂ → ℝ),
      IsProbabilityMeasure P ∧ IsZeroBoundaryGFFOn openSquare X P :=
  K3.exists_zeroGFFOn openSquare

end GMCIdent5
end LQGMetric
