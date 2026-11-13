/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.GFF.ZeroRegBoundary at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.ZeroRegularization
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleMeanValue
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# RG-2 (REG-BDRY): regularization of the zero-boundary GFF at measures touching `ℝ`

Blueprint `THM11_BLUEPRINT.md` §7, node RG-2. Let `X` satisfy `IsZeroBoundaryGFFH X P` and let
`μ` be an admissible measure (`IsAdmissibleH`: finite, compact support in `Hbar`, bounded
singular log potential) with

* a bounded zero-boundary Green potential `∫⁻ G⁺(x,·) dμ ≤ U` on `ℍ`;
* a Frostman bound `μ(B(x,s)) ≤ M h^{-p} s^α` for `Im x ≥ h > 0`, `s ≤ h/2`;
* the log-log strip decay `μ{Im < exp(-exp t)} ≤ C t^{-(1+η)}` for `t ≥ 1`
  (i.e. `μ{Im < δ} ≤ C (log log 1/δ)^{-1-η}`).

Then (`evalReg_ae_eq_zeroGFF_bdry`) `evalReg (X ω) μ = X ω μ` almost surely.

Proof. Let `νk = μ.bind (foldedCircle · 2^{-k})`. Stochastic Fubini (RG-0) gives
`∫ avgReg (X ω) k dμ = X ω νk`. `X νk − X μ` is a centered Gaussian of variance
`𝓔_G(νk − μ)`, which RG-1 bounds, with `h = e^{-γk}/2`, `γ = α/(4(p+α))`, by
`v_k = A C (log γk)^{-(1+η)} + B' e^{-αk/4}`. Since `v_k log k → 0`, the Gaussian tails
`2 exp(−ε²/(2 v_k))` are eventually `≤ 2k^{-2}`, and Borel–Cantelli gives `X νk → X μ` a.s.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Real

namespace QuantumZipper
namespace ZeroRegBdry

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-! ## Gaussian increments and tails -/

/-- Two-sided Gaussian tail: if `Y ∼ N(0, V)` and `V ≤ c`, then
`P(|Y| ≥ ε) ≤ 2 exp(−ε²/(2c))`. -/
theorem zrb_measureReal_abs_ge_le [IsProbabilityMeasure P] {Y : Ω → ℝ} (hY : Measurable Y)
    {V c : ℝ≥0} (hlaw : P.map Y = gaussianReal 0 V) (hVc : V ≤ c) {ε : ℝ} (hε : 0 ≤ ε) :
    P.real {ω | ε ≤ |Y ω|} ≤ 2 * Real.exp (-ε ^ 2 / (2 * c)) := by
  have hVc' : (V : ℝ) ≤ c := hVc
  have hg : HasSubgaussianMGF id c (gaussianReal 0 V) :=
    { integrable_exp_mul := fun t => by
        simpa using integrable_exp_mul_gaussianReal (μ := 0) (v := V) t
      mgf_le := fun t => by
        rw [mgf_id_gaussianReal]
        simp only [zero_mul, zero_add]
        exact Real.exp_le_exp.2 (by gcongr) }
  have hS : HasSubgaussianMGF Y c P := by
    rw [← HasSubgaussianMGF.id_map_iff hY.aemeasurable, hlaw]; exact hg
  have h1 := hS.measure_ge_le hε
  have h2 := hS.neg.measure_ge_le hε
  have hsub : {ω | ε ≤ |Y ω|} ⊆ {ω | ε ≤ Y ω} ∪ {ω | ε ≤ (-Y) ω} := by
    intro ω hω
    simp only [mem_ofPred_eq, mem_union, Pi.neg_apply] at hω ⊢
    exact le_abs.1 hω
  calc P.real {ω | ε ≤ |Y ω|} ≤ P.real ({ω | ε ≤ Y ω} ∪ {ω | ε ≤ (-Y) ω}) :=
        measureReal_mono hsub
    _ ≤ P.real {ω | ε ≤ Y ω} + P.real {ω | ε ≤ (-Y) ω} := measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-ε ^ 2 / (2 * c)) := by linarith

/-! ## Summability and Borel–Cantelli -/

/-! ## The energy bound along the dyadic scales -/

/-! ## RG-2 -/

end ZeroRegBdry
end QuantumZipper
