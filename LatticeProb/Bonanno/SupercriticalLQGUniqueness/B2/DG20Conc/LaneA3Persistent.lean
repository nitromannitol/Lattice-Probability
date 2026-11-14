/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA3Persistent at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P21Ratio
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20CDefs
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCInputs
import Mathlib.Topology.Instances.ENNReal.Lemmas

 







set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set Filter

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF

 

theorem laneA3_finite_persistent_visits
    {ι : Type*} (s : Finset ι) (visit : ℕ → ι → Prop)
    (h : ∀ i ∈ s, ∃ N : ℕ, ∀ j, N ≤ j → visit j i) :
    ∃ N : ℕ, ∀ j, N ≤ j → ∀ i ∈ s, visit j i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun _ _ _ hi => by simp at hi⟩
  | @insert i s hi ih =>
    obtain ⟨Ni, hNi⟩ := h i (Finset.mem_insert_self ..)
    obtain ⟨Ns, hNs⟩ := ih (fun k hk => h k (Finset.mem_insert_of_mem hk))
    refine ⟨max Ni Ns, fun j hj k hk => ?_⟩
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact hNi j ((le_max_left _ _).trans hj)
    · exact hNs j ((le_max_right _ _).trans hj) k hk

 

end SupercriticalLQGUniqueness.B2.DG20Conc
