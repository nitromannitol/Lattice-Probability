/- Proofs adapted from Leonardo Bonanno’s lean-formalizations
   (https://github.com/leobon12/lean-formalizations),
   BouRabeeGwynne.WalkEdgeSupport, commit fdb5cad. -/
import LatticeProb.Bonanno.BouRabeeGwynne.WalkEdgeSupport

/-! # Positive conductance along active steps -/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace BouRabeeGwynne.FiniteConductanceNetwork

variable {V : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]

/-- A transition from an active vertex has positive conductance almost surely. -/
theorem stepPMF_ae_pos_of_mem (N : FiniteConductanceNetwork V) (A : Set V)
    (hA : ∀ v ∈ A, 0 < N.totalConductance v) (v : V) :
    ∀ᵐ w ∂(N.stepPMF A hA v).toMeasure, v ∈ A → 0 < N.a v w := by
  apply (mem_ae_iff_prob_eq_one (Set.toFinite _).measurableSet).mpr
  apply ((N.stepPMF A hA v).toMeasure_apply_eq_one_iff (Set.toFinite _).measurableSet).mpr
  intro w hw hv
  have hn : N.a v w ≠ 0 := by
    intro hz
    apply (PMF.mem_support_iff _ _).mp hw
    simp only [stepPMF_apply, transitionProbability, hv, ↓reduceIte, hz, zero_div,
      ENNReal.ofReal_zero]
  exact lt_of_le_of_ne (N.nonneg v w) hn.symm

/-- Every step taken before absorption follows an edge of positive conductance. -/
theorem trajectoryLaw_ae_pos_of_mem (N : FiniteConductanceNetwork V) (A : Set V)
    (hA : ∀ v ∈ A, 0 < N.totalConductance v) (v : V) :
    ∀ᵐ ω ∂N.trajectoryLaw A hA v, ∀ n,
      ω n ∈ A → 0 < N.a (ω n) (ω (n + 1)) := by
  apply ae_all_iff.mpr
  intro n
  have h := TrajectoryCoupling.ae_next_relation (Measure.dirac v) (N.historyKernel A hA) n
    (fun p => p.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩ ∈ A →
      0 < N.a (p.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩) p.2)
    (Set.toFinite _).measurableSet
    (fun h => N.stepPMF_ae_pos_of_mem A hA (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩))
  exact h

end BouRabeeGwynne.FiniteConductanceNetwork
end
