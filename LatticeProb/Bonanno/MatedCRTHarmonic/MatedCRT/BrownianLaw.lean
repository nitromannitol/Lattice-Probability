/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MatedCRT.BrownianLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib
import LatticeProb.Bonanno.QuantumZipper.Proofs.RS.TransienceCanon
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.BMExistence
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsCorrelatedBM2

/-!
# Correlated two-sided Brownian law for the mated-CRT map

This module constructs a continuous-path law with the covariance specified in [18] §1.1.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

noncomputable section

namespace MatedCRTHarmonic.MatedCRT

def positiveTime (t : ℝ) : ℝ≥0 := ⟨max t 0, le_max_right t 0⟩

def negativeTime (t : ℝ) : ℝ≥0 := ⟨max (-t) 0, le_max_right (-t) 0⟩

@[fun_prop] theorem continuous_positiveTime : Continuous positiveTime := by
  exact (continuous_max.comp (continuous_id.prodMk continuous_const)).subtype_mk
    fun t => le_max_right t 0

@[fun_prop] theorem continuous_negativeTime : Continuous negativeTime := by
  exact (continuous_max.comp (continuous_neg.prodMk continuous_const)).subtype_mk
    fun t => le_max_right (-t) 0

end MatedCRTHarmonic.MatedCRT

noncomputable section
namespace MatedCRTHarmonic.MatedCRT

def rho (γ : ℝ) : ℝ := -Real.cos (Real.pi * γ ^ 2 / 4)
def sigma (γ : ℝ) : ℝ := Real.sqrt (1 - rho γ ^ 2)

theorem rho_sq_add_sigma_sq (γ : ℝ) : rho γ ^ 2 + sigma γ ^ 2 = 1 := by
  unfold sigma
  have hnonneg : 0 ≤ 1 - rho γ ^ 2 := by
    unfold rho
    nlinarith [sq_nonneg (Real.sin (Real.pi * γ ^ 2 / 4)), Real.cos_sq_add_sin_sq (Real.pi * γ ^ 2 / 4)]
  rw [Real.sq_sqrt hnonneg]
  ring

end MatedCRTHarmonic.MatedCRT

namespace MatedCRTHarmonic.MatedCRT

end MatedCRTHarmonic.MatedCRT

namespace MatedCRTHarmonic.MatedCRT

end MatedCRTHarmonic.MatedCRT

namespace MatedCRTHarmonic.MatedCRT

def corrA (γ : ℝ) (i : Fin 2) : ℝ := if i = 0 then 1 else rho γ
def corrB (γ : ℝ) (i : Fin 2) : ℝ := if i = 0 then 0 else sigma γ

end MatedCRTHarmonic.MatedCRT

namespace MatedCRTHarmonic.MatedCRT

end MatedCRTHarmonic.MatedCRT

namespace MatedCRTHarmonic.MatedCRT

theorem measurable_lrCoord (p : Fin 2 × ℝ) :
    Measurable (fun ω : Path2 => lrCoord p.1 p.2 ω) := by
  unfold lrCoord
  split_ifs with h
  · exact measurable_fst.comp (ContinuousMap.measurable_eval p.2)
  · exact measurable_snd.comp (ContinuousMap.measurable_eval p.2)

end MatedCRTHarmonic.MatedCRT
namespace MatedCRTHarmonic

end MatedCRTHarmonic
