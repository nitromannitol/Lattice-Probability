/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCIdent4Fact at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent3Wn
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdentCirc
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoise
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCSqRate
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCSqExist
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCSqCov
import LatticeProb.Bonanno.QuantumZipper.Common.Basic
import Mathlib.Analysis.Complex.Schwarz
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.BasicsUnivalent
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCSqLip
import LatticeProb.Bonanno.LQGDimension.Gaussian.SteinIBP
import LatticeProb.Bonanno.LQGMetric.Gaussian.ConcentrationLip
import LatticeProb.Bonanno.LQGMetric.Gaussian.PittVector
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCSqGauss
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCSqReg
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCTest
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.VagueOpenExist
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2Bridge
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L7Trunc
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L5Kernel
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseKernel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L7
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2Box
import LatticeProb.Bonanno.LQGMetric.Gaussian.SupTailField
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseCont
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeRestriction
import Mathlib.Probability.Process.FiniteDimensionalLaws
import LatticeProb.Bonanno.LQGMetric.Gaussian.FerniqueDZZ

/-!
# The DZZ factorization `M_γ = e^{γ h̃_δ − γ²/2 Var h̃_δ} M̃_{γ,δ}` (P2-GMCID4, item 4b)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` (eq-def-tilde-M), l. 676–683):
`M̃_{γ,δ}(B) = lim_n ∫_B e^{γ h̃^δ_{2^{-n}}(z) − γ²/2 Var h̃^δ_{2^{-n}}(z)} dz`. For `δ = 2^{-m}`
and the white-noise field:

* `coarseVer hW m`: a version of `h̃_δ` continuous in `z` (`DZZ.exists_continuous_tildeHInf`);
* `cDens`: `CR(z)^{γ²/2} e^{γ h̃_δ(z) − γ²/2 Var h̃_δ(z)}`, positive and continuous on `𝕍`;
* `tildeM := cDens⁻¹ · M_γ`, so that **`qArea_eq_withDensity_tildeM`**: `M_γ = cDens · M̃_{γ,δ}`;
* `bandMeas n := (wnDens n / cDens) dz`, the band approximation; **`ae_isVagueLimitOn_bandMeas`**:
  a.s. `bandMeas n → M̃_{γ,δ}` vaguely on `𝕍`, i.e. `M̃_{γ,δ}` is DZZ's limit (pathwise from the a.s.
  vague convergence `ae_isVagueLimitOn_wnMeas`, with the random test function `f / cDens`);
* **`bandDens_ae_eq`**: for `n ≥ m` and each `z`, a.s. the band density is DZZ's
  `e^{γ h̃^δ_{2^{-n}}(z) − γ²/2 Var h̃^δ_{2^{-n}}(z)}` (`DZZ.tildeH`).

Own glue (D85); the constant `CR^{γ²/2}` is absorbed in `cDens` (our normalization, handoff
P2-GMCID Notes).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric QuantumZipper
open scoped ENNReal NNReal ComplexConjugate RealInnerProductSpace

namespace LQGMetric
namespace GMCIdent4

open KilledHeat WhiteNoise DZZ GMCIdent GMCIdent2 GMCIdent3

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'} {X : Ω → Measure ℂ → ℝ} {W : WNSpace → Ω' → ℝ}

lemma integral_withDensity_ofReal {μ : Measure ℂ} {d : ℂ → ℝ} (hd : Measurable d)
    (h0 : ∀ z, 0 ≤ d z) (f : ℂ → ℝ) :
    ∫ z, f z ∂(μ.withDensity fun z => ENNReal.ofReal (d z)) = ∫ z, d z * f z ∂μ := by
  change ∫ z, f z ∂(μ.withDensity fun z => ((d z).toNNReal : ℝ≥0∞)) = _
  rw [integral_withDensity_eq_integral_smul hd.real_toNNReal]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (h0 z)]

end GMCIdent4
end LQGMetric
