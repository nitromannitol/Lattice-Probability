/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.Blueprint.GaussianConcentration at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.Blueprint.Gaussian

/-!
# Blueprint: Gaussian concentration for finite maxima

The paper's (2.1) states `log E e^{t(F - EF)} ≤ t² v² / 2` for a supremum `F` of affine
Gaussian functions with variance parameter at most `v²`.  We record the same bound with the
constant `π²/8` in place of `1/2` (Maurey–Pisier).  Every later use in the paper absorbs this
constant into an unspecified `C`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped RealInnerProductSpace

namespace LQGDimension.Blueprint

/-- Gaussian concentration for a finite maximum of affine functions of a standard Gaussian
vector whose linear parts have norm at most `σ`:
`E exp(t (M - E M)) ≤ exp(π² t² σ² / 8)` for all real `t`. -/
def MaxConcentration : Prop :=
  ∀ (ι E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (F : Finset ι) (v : ι → E) (b : ι → ℝ) (σ : ℝ),
    (∀ i ∈ F, ‖v i‖ ≤ σ) → ∀ t : ℝ,
    ∫ x, Real.exp (t * ((⨆ i : F, ⟪v i, x⟫ + b i) - vecExpectedMax F v b)) ∂(stdGaussian E) ≤
      Real.exp (π ^ 2 / 8 * t ^ 2 * σ ^ 2)

end LQGDimension.Blueprint
