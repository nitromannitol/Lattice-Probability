/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.LQG.LocalRule at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports.
   Opens of namespaces with no copied declaration are removed (Positivity). -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.BoundaryExistence
import LatticeProb.Bonanno.QuantumZipper.LQG.Measures
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.GoodSample
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularClosure
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularSampleKolmogorov
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Admissible
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaExistenceAS
import LatticeProb.Bonanno.QuantumZipper.LQG.Local

/-!
# Local rule (5.1) along the dyadic radii

The transformation rule for adding a continuous function, localized to an open set and along the
dyadic radii `2^{-k}` only, **without** `IsLQGGood` (compare `GoodSample.qBoundaryMeasure_add_ofFun`,
which needs the uniform-in-offset limits and the area limit).

* `isVagueLimitOnR_add_ofFun`: `x` regular, `bdryApprox γ x → ν` vaguely on an open `U ⊆ ℝ`,
  `φ` continuous on `W ∩ Hbar` for an open `W ⊇ U`: then `bdryApprox γ (x + ofFun φ) → e^{γφ/2} ν`
  vaguely on `U`. `isVagueLimitR_add_ofFun` is the case `U = ℝ`.
* `isVagueLimitOn_add_ofFun`: the same for `areaApprox` on an open `U ⊆ H`, density `e^{γφ}`.
  (`continuousOn_of_local` turns "continuous on a neighbourhood in `Hbar` of every point" into
  the `W` form.)
* Constants: `bdryApprox_addConst`, `areaApprox_addConst` (exact, whenever the raw dyadic circle
  averages converge, e.g. for regular samples) and the identities for `qBoundaryMeasure`,
  `qBoundaryMeasureOn`, `qAreaMeasure`, `qAreaMeasureOn`.
* Corollaries for `qBoundaryMeasureOn`, `qAreaMeasureOn`, `qBoundaryMeasure`, `qAreaMeasure` of
  `x + ofFun φ`.

Route: on a compact `K ⊆ U`, replace `φ` by a cutoff `φ'` continuous on `Hbar` and equal to `φ`
on a thickening of `K`; for `2^{-k}` small the dyadic circle averages of `x + ofFun φ` and
`x + ofFun φ'` agree near `K`, the densities differ from those of `x` by `e^{γ ∫ φ' dfc/2}`, which
converges to `e^{γφ/2}` uniformly on `K`, and `GoodSample.tendsto_integral_exp_mul` concludes.

Note on constants: the statement "exactly for every `x`" is false with the junk convention of
`limUnder`: if the raw values `x(fc(d_n z, 2^{-k}))` diverge for every `z`, then
`avgReg (addConst x c) = avgReg x` (both are the same junk constant), so
`bdryApprox γ (addConst x c) = bdryApprox γ x ≠ e^{γc/2} • bdryApprox γ x` for `c ≠ 0`. We
therefore assume the raw averages converge (true for regular samples).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace LocalRule

open GoodSample GaussTK

/-! ### Folded circles near their centre, and local congruence of `avgReg` -/

/-! ### Cutoff of a locally continuous function -/

/-! ### The local rule on `ℝ` -/

/-! ### The local rule on `H` -/

/-! ### Uniqueness of local vague limits on `ℝ` -/

/-! ### Corollaries for the chosen limits -/

/-! ### Additive constants -/

theorem IsVagueLimitOn.const_smul {U : Set ℂ} {μs : ℕ → Measure ℂ} {μ : Measure ℂ}
    (h : IsVagueLimitOn U μs μ) {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    IsVagueLimitOn U (fun k => c • μs k) (c • μ) := by
  obtain ⟨h0, hK, ht⟩ := h
  refine ⟨by rw [Measure.smul_apply, h0, smul_zero], fun K hKc hKU => ?_, fun f hf hfc hfU => ?_⟩
  · rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top hc.lt_top (hK K hKc hKU)
  · simp_rw [integral_smul_measure]
    exact (ht f hf hfc hfU).const_smul _

end LocalRule
end QuantumZipper
