/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.Blueprint.Gaussian at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.Statement.Defs

/-!
# Blueprint: finite Gaussian families

A centered Gaussian family indexed by a finite set is realised as `(⟪v i, x⟫)_i` for vectors
`v i` in a finite-dimensional real inner product space `E` and `x` distributed by
`stdGaussian E`.  The statement-level `gaussianExpectedMax` (defined through
`multivariateGaussian`) is identified with this representation by `GramBridge`.

Each `Prop` below is a proof obligation, discharged in `LQGDimension/Gaussian/`.
Downstream files take these propositions as hypotheses until they are proved.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped RealInnerProductSpace

namespace LQGDimension

/-- The kernel `C`, restricted to the finite set `F`, is positive semidefinite. -/
def PSDOn {ι : Type*} (F : Finset ι) (C : ι → ι → ℝ) : Prop :=
  (Matrix.of fun i j : F => C i j).PosSemidef

/-- `E[max_{i ∈ F} (⟪v i, x⟫ + b i)]` for `x` a standard Gaussian vector of `E`. -/
def vecExpectedMax {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] (F : Finset ι) (v : ι → E) (b : ι → ℝ) : ℝ :=
  ∫ x, (⨆ i : F, ⟪v i, x⟫ + b i) ∂(stdGaussian E)

namespace Blueprint

/-- The multivariate Gaussian with a Gram covariance is the law of the inner products with a
standard Gaussian vector; hence the two expected maxima agree. -/
def GramBridge : Prop :=
  ∀ (ι E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (F : Finset ι) (v : ι → E) (b : ι → ℝ),
    gaussianExpectedMax F (fun i j => ⟪v i, v j⟫) b = vecExpectedMax F v b

/-- Every kernel that is positive semidefinite on a finite set is a Gram kernel there. -/
def GramRepresentation : Prop :=
  ∀ (ι : Type) (F : Finset ι) (C : ι → ι → ℝ), PSDOn F C →
    ∃ v : ι → EuclideanSpace ℝ F, ∀ i ∈ F, ∀ j ∈ F, ⟪v i, v j⟫ = C i j

/-- A finite maximum of affine functions of a standard Gaussian vector is integrable. -/
def MaxIntegrable : Prop :=
  ∀ (ι E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (F : Finset ι) (v : ι → E) (b : ι → ℝ),
    Integrable (fun x => ⨆ i : F, ⟪v i, x⟫ + b i) (stdGaussian E)

/-- **Sudakov–Fernique comparison with deterministic drift** (Chatterjee, Theorem 1.2): if the
canonical distances of the family `w` dominate those of `v`, then so do the expected maxima,
after adding the same drift `b`. -/
def SudakovFernique : Prop :=
  ∀ (ι E E' : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
    [MeasurableSpace E'] [BorelSpace E']
    (F : Finset ι) (v : ι → E) (w : ι → E') (b : ι → ℝ),
    (∀ i ∈ F, ∀ j ∈ F, ‖v i - v j‖ ≤ ‖w i - w j‖) →
    vecExpectedMax F v b ≤ vecExpectedMax F w b

end Blueprint

end LQGDimension
