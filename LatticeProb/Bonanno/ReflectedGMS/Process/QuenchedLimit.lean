/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Process.QuenchedLimit at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.StatementIngredients
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianScaling
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Genuine anisotropic Brownian targets and quenched path-law limits

This file supplies only statement ingredients for parts (d) and (e) of the
reflected-GMS main theorem.  It does not construct either reflected process or
assert the invariance principle.

The target law is the pushforward of a law satisfying the existing genuine
standard-Brownian definition by an actual linear map. Its existence is part
of the final theorem conclusion.  Weak convergence uses mathlib's weak topology on
`ProbabilityMeasure`; the underlying `BrownianPath 2 = C(ℝ≥0, Euc 2)` carries
the local-uniform topology.
-/

set_option autoImplicit false

open Filter MeasureTheory Set
open scoped Matrix NNReal Topology

namespace ReflectedGMS.StatementIngredients

/-- Apply a deterministic linear map to every value of a continuous planar
path. -/
noncomputable def linearImageBrownianPath
    (A : Matrix (Fin 2) (Fin 2) ℝ) (ω : BouRabeeGwynne.BrownianPath 2) :
    BouRabeeGwynne.BrownianPath 2 where
  toFun t := WithLp.toLp 2 (A *ᵥ fun j => ω t j)
  continuous_toFun := by fun_prop

@[simp] lemma linearImageBrownianPath_apply
    (A : Matrix (Fin 2) (Fin 2) ℝ) (ω : BouRabeeGwynne.BrownianPath 2)
    (t : ℝ≥0) (i : Fin 2) :
    linearImageBrownianPath A ω t i = ∑ j : Fin 2, A i j * ω t j := rfl

lemma measurable_linearImageBrownianPath (A : Matrix (Fin 2) (Fin 2) ℝ) :
    Measurable (linearImageBrownianPath A) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact (by fun_prop : Continuous
    (fun ω : BouRabeeGwynne.BrownianPath 2 =>
      WithLp.toLp 2 (A *ᵥ fun j => ω t j))).measurable

/-- The covariance matrix of the linear image `A B` of standard Brownian
motion `B`. -/
def covarianceOfBrownianFactor (A : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  A * A.transpose

/-- Actual linear-image law; the target below requires the base law to satisfy
the existing genuine standard-Brownian predicate. -/
noncomputable def anisotropicBrownianLaw
    (base : ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2))
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2) :=
  base.map (linearImageBrownianPath A)

/-- Deterministic target data for the main quenched limit.  The law is derived
from `factor`, while `covariance_eq` records that its covariance is `A Aᵀ`.
Positive definiteness is the existing reflected-GMS condition. -/
structure AnisotropicBrownianTarget where
  standardLaw : ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2)
  isStandard : BouRabeeGwynne.IsStandardBrownianLaw (d := 2)
    (standardLaw : Measure (BouRabeeGwynne.BrownianPath 2))
  covariance : Matrix (Fin 2) (Fin 2) ℝ
  factor : Matrix (Fin 2) (Fin 2) ℝ
  covariance_eq : covariance = covarianceOfBrownianFactor factor
  positiveDefinite : SymmetricPositiveDefinite covariance

noncomputable def AnisotropicBrownianTarget.pathLaw
    (target : AnisotropicBrownianTarget) :
    ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2) :=
  anisotropicBrownianLaw target.standardLaw target.factor

/-- Rescale a continuous path law by `ω(t) ↦ ε ω(t / ε²)`.

This is exactly the existing `scaledBrownianPath` with its parameter
`r = ε⁻¹`.  Its value at `ε = 0` is irrelevant to the positive-side limit. -/
noncomputable def diffusivelyRescaledPathLaw
    (law : ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2))
    (ε : ℝ≥0) : ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2) :=
  law.map (BouRabeeGwynne.scaledBrownianPath ε⁻¹)

/-- The reused scaler has exactly the manuscript normalization at every
positive scale: spatial multiplication by `ε` and time multiplication by
`ε⁻²` (equivalently, evaluation at `t / ε²`). -/
lemma scaledBrownianPath_inv_apply (ε : ℝ≥0) (hε : 0 < ε)
    (ω : BouRabeeGwynne.BrownianPath 2) (t : ℝ≥0) :
    BouRabeeGwynne.scaledBrownianPath ε⁻¹ ω t =
      (ε : ℝ) • ω (ε⁻¹ ^ 2 * t) := by
  rw [BouRabeeGwynne.scaledBrownianPath_apply]
  simp [hε.ne']

/-- Quenched weak convergence for one fixed environment and one fixed starting
vertex, along all positive real scales `ε → 0`.

Because `environment` and `start` are arguments outside `Tendsto`, this
definition cannot express a starting vertex which varies with `ε`. -/
def QuenchedWeakLimitAtFixedStart {Environment Vertex : Type*}
    (law : Environment → Vertex →
      ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2))
    (target : AnisotropicBrownianTarget) (environment : Environment)
    (start : Vertex) : Prop :=
  Tendsto
    (fun ε => diffusivelyRescaledPathLaw (law environment start) ε)
    (nhdsWithin (0 : ℝ≥0) (Ioi 0))
    (𝓝 target.pathLaw)

/-- The exponential area-clock interpolation and the exact-area-holding-time
interpolation have the same anisotropic Brownian target, for this environment
and this fixed start.  Construction of the two input laws is deliberately a
separate process-level obligation. -/
def TwoClockQuenchedWeakLimitAtFixedStart {Environment Vertex : Type*}
    (exponentialAreaClockLaw exactAreaHoldingTimeLaw :
      Environment → Vertex →
        ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2))
    (target : AnisotropicBrownianTarget) (environment : Environment)
    (start : Vertex) : Prop :=
  QuenchedWeakLimitAtFixedStart exponentialAreaClockLaw target environment start ∧
  QuenchedWeakLimitAtFixedStart exactAreaHoldingTimeLaw target environment start

end ReflectedGMS.StatementIngredients
