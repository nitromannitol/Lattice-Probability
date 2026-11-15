/- Adapted from Leonardo Bonanno’s lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.WalkEdgeSupport at commit fdb5cad; imports are relocated. -/
import LatticeProb.Bonanno.BouRabeeGwynne.TilingClockedExcursion
import LatticeProb.Bonanno.BouRabeeGwynne.ExcursionTrajectory
import LatticeProb.Bonanno.BouRabeeGwynne.LocalGeometry

/-! Actual conductance-walk transitions use a positive edge or are constant.
Consequently the ambient tiling walk has the required mesh-sized steps. -/

open MeasureTheory ProbabilityTheory Set Preorder
open scoped ENNReal

namespace BouRabeeGwynne

namespace FiniteConductanceNetwork

variable {V : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]

lemma stepPMF_ae_edge_or_constant (N : FiniteConductanceNetwork V) (A : Set V)
    (hA : ∀ v ∈ A, 0 < N.totalConductance v) (v : V) :
    ∀ᵐ w ∂(N.stepPMF A hA v).toMeasure, 0 < N.a v w ∨ w = v := by
  apply (mem_ae_iff_prob_eq_one (Set.toFinite _).measurableSet).mpr
  apply ((N.stepPMF A hA v).toMeasure_apply_eq_one_iff (Set.toFinite _).measurableSet).mpr
  intro w hw
  by_cases hv : v ∈ A
  · left
    have hn : N.a v w ≠ 0 := by
      intro hz
      apply (PMF.mem_support_iff _ _).mp hw
      simp only [stepPMF_apply, transitionProbability, hv, ↓reduceIte, hz, zero_div,
        ENNReal.ofReal_zero]
    exact lt_of_le_of_ne (N.nonneg v w) hn.symm
  · right
    rw [N.stepPMF_of_not_mem A hA hv] at hw
    simpa only [PMF.support_pure, Set.mem_singleton_iff] using hw

theorem trajectoryLaw_ae_edge_or_constant (N : FiniteConductanceNetwork V) (A : Set V)
    (hA : ∀ v ∈ A, 0 < N.totalConductance v) (v : V) :
    ∀ᵐ ω ∂N.trajectoryLaw A hA v, ∀ n, 0 < N.a (ω n) (ω (n + 1)) ∨ ω (n + 1) = ω n := by
  apply ae_all_iff.mpr
  intro n
  have h := TrajectoryCoupling.ae_next_relation (Measure.dirac v) (N.historyKernel A hA) n
    (fun p => 0 < N.a (p.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩) p.2 ∨
      p.2 = p.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
    (Set.toFinite _).measurableSet
    (fun h => N.stepPMF_ae_edge_or_constant A hA (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩))
  exact h

end FiniteConductanceNetwork

namespace OrthogonalTiling

theorem trajectoryLaw_ae_step_dist_le_two_mesh {d : ℕ} (T : OrthogonalTiling d)
    (S : Set T.V) [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (A : Set S) (hA : ∀ v ∈ A, 0 < (T.finiteNetwork S).totalConductance v)
    (v : S) (hmesh : T.mesh ≠ ∞) :
    ∀ᵐ ω ∂(T.finiteNetwork S).trajectoryLaw A hA v, ∀ n,
      dist (T.pos (ω n)) (T.pos (ω (n + 1))) ≤ 2 * T.mesh.toReal := by
  filter_upwards [(T.finiteNetwork S).trajectoryLaw_ae_edge_or_constant A hA v] with ω hω
  intro n
  rcases hω n with hedge | hconstant
  · exact T.toTilingData.edge_dist_le_two_mesh (T.conductanceReal_pos_iff.mp hedge) hmesh
  · rw [hconstant, dist_self]
    positivity

end OrthogonalTiling
end BouRabeeGwynne
