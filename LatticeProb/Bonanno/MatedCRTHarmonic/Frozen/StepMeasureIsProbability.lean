/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.StepMeasureIsProbability at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.LFMultigraph
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Dart
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Dsrc
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.OutDarts
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Deg
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.State
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.StateMeasurableSpace
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.StepMeasure

/-!
# Frozen definition: `LFMultigraph.instIsProbabilityMeasureStateStepMeasure`

`stepMeasure x` is a probability measure (from `exists_inc`). The instance carries Lean's automatic name of the
candidate's anonymous instance (the frozen-anchor checker needs a named export; the constant is unchanged).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace LFMultigraph

variable {V E : Type*} (G : LFMultigraph V E)

instance instIsProbabilityMeasureStateStepMeasure (x : V) : IsProbabilityMeasure (G.stepMeasure x) := by
  classical
  constructor
  have hdeg : G.deg x ≠ 0 := by
    obtain ⟨e, he⟩ := G.exists_inc x
    have hinc : e ∈ (G.finite_inc x).toFinset := (G.finite_inc x).mem_toFinset.mpr he
    unfold deg outDarts
    rw [Finset.card_ne_zero]
    rcases he with h | h
    · exact ⟨(e, false), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hinc, Finset.mem_univ _⟩,
        by simp [dsrc, h]⟩⟩
    · exact ⟨(e, true), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hinc, Finset.mem_univ _⟩,
        by simp [dsrc, h]⟩⟩
  have hd : (G.deg x : ℝ≥0∞) ≠ 0 := by exact_mod_cast hdeg
  rw [stepMeasure, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply]
  have h1 : ∀ d ∈ G.outDarts x,
      (Measure.dirac (show G.State from Sum.inr d)) Set.univ = 1 := fun d _ => measure_univ
  rw [smul_eq_mul, Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel hd (ENNReal.natCast_ne_top _)

end LFMultigraph

end MatedCRTHarmonic
