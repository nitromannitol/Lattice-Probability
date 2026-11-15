import LatticeProb.Prob.CountablePhaseMap
import LatticeProb.Prob.UnitCubeTVApproximation
import Mathlib.Probability.Kernel.Composition.MapComap

/-! Uniform coordinate resampling on a countable union of finite-dimensional spaces. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace LatticeProb

private theorem measurable_countablePhase_inject {E : Type*} [MeasurableSpace E] (n : ℕ) :
    Measurable (@Sigma.mk ℕ (fun k => E × (Fin k → ℝ)) n) := by
  intro s hs
  change MeasurableSet[⨅ i : ℕ, (inferInstance : MeasurableSpace (E × (Fin i → ℝ))).map
    (Sigma.mk i)] s at hs
  exact (MeasurableSpace.measurableSet_iInf.mp hs) n

private noncomputable def fixedCountUniformKernel {E : Type*} [MeasurableSpace E] (n : ℕ) :
    Kernel (E × (Fin n → ℝ)) (CountablePhaseSpace E) :=
  (markResamplingKernel (Prod.fst : E × (Fin n → ℝ) → E) measurable_fst
    (unitCubeMeasure (Fin n))).map (@Sigma.mk ℕ (fun k => E × (Fin k → ℝ)) n)

/-- Preserve the count and mark, replacing coordinates by independent uniform phases. -/
noncomputable def countableUniformPhaseKernel {E : Type*} [MeasurableSpace E] :
    Kernel (CountablePhaseSpace E) (CountablePhaseSpace E) where
  toFun x := fixedCountUniformKernel x.1 x.2
  measurable' := by
    intro s hs
    change MeasurableSet[⨅ i : ℕ, (inferInstance : MeasurableSpace (E × (Fin i → ℝ))).map
      (Sigma.mk i)] _
    rw [MeasurableSpace.measurableSet_iInf]
    intro n
    exact (fixedCountUniformKernel (E := E) n).measurable hs

/-- The uniform resampling kernel is a probability kernel, also in dimension zero. -/
instance countableUniformPhaseKernel_isMarkovKernel {E : Type*} [MeasurableSpace E] :
    IsMarkovKernel (countableUniformPhaseKernel (E := E)) where
  isProbabilityMeasure x := by
    cases x with
    | mk n p =>
      change IsProbabilityMeasure (fixedCountUniformKernel n p)
      let : IsMarkovKernel (fixedCountUniformKernel (E := E) n) := by
        unfold fixedCountUniformKernel
        exact Kernel.IsMarkovKernel.map _ (measurable_countablePhase_inject n)
      infer_instance

/-- On a fixed count, the kernel is the embedded mark-resampling kernel. -/
theorem countableUniformPhaseKernel_apply {E : Type*} [MeasurableSpace E]
    (n : ℕ) (p : E × (Fin n → ℝ)) :
    countableUniformPhaseKernel ⟨n, p⟩ =
      (markResamplingKernel (Prod.fst : E × (Fin n → ℝ) → E) measurable_fst
        (unitCubeMeasure (Fin n)) p).map (@Sigma.mk ℕ (fun k => E × (Fin k → ℝ)) n) := by
  exact Kernel.map_apply _ (measurable_countablePhase_inject (E := E) n) _

end LatticeProb
