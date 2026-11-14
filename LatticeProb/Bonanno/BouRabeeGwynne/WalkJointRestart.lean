/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.WalkJointRestart at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.WalkMemoryless

/-! The joint law of the observed prefix and the entire future of the actual
conductance walk. This retains the dependence on the observed current vertex. -/

open MeasureTheory ProbabilityTheory Set Preorder

namespace BouRabeeGwynne
namespace TrajectoryCoupling

variable {X : Type*} [MeasurableSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]
  (κ : (n : ℕ) → Kernel (Finset.Iic n → X) X) [∀ n, IsMarkovKernel (κ n)]

lemma prefix_compProd_traj (a : ℕ) :
    (Kernel.trajMeasure (X := fun _ => X) μ κ).map (frestrictLe a) ⊗ₘ
        Kernel.traj (X := fun _ => X) κ a =
      (Kernel.trajMeasure (X := fun _ => X) μ κ).map (fun ω => (frestrictLe a ω, ω)) := by
  rw [Measure.compProd_eq_comp_prod, Kernel.trajMeasure,
    Measure.map_comp _ _ (measurable_frestrictLe a), Kernel.traj_map_frestrictLe,
    Measure.comp_assoc, Measure.map_comp _ _ (by fun_prop)]
  congr with h : 1
  rw [Kernel.comp_apply, ← Measure.compProd_eq_comp_prod,
    Kernel.map_apply _ (by fun_prop), Kernel.partialTraj_compProd_traj (Nat.zero_le a)]

end TrajectoryCoupling

namespace FiniteConductanceNetwork

variable {V : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
  (N : FiniteConductanceNetwork V)

/-- The genuine infinite trajectory law, viewed measurably as a function of
the starting vertex. -/
noncomputable def walkPathKernel (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) : Kernel V (ℕ → V) where
  toFun := N.trajectoryLaw A hpos
  measurable' := measurable_of_finite _

noncomputable instance walkPathKernel_isMarkovKernel (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) :
    IsMarkovKernel (N.walkPathKernel A hpos) where
  isProbabilityMeasure v := N.trajectoryLaw_isProbabilityMeasure A hpos v

/-- The future kernel from a finite observed history. -/
noncomputable def restartKernel (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (a : ℕ) :
    Kernel (Finset.Iic a → V) (ℕ → V) :=
  (N.walkPathKernel A hpos).comap
    (fun h => h ⟨a, Finset.mem_Iic.mpr le_rfl⟩) (measurable_pi_apply _)

noncomputable instance restartKernel_isMarkovKernel (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (a : ℕ) :
    IsMarkovKernel (N.restartKernel A hpos a) := by
  unfold restartKernel
  infer_instance

lemma continuation_map_walkShift (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (a : ℕ) :
    (Kernel.traj (X := fun _ => V) (N.historyKernel A hpos) a).map (walkShift a) =
      N.restartKernel A hpos a := by
  ext h : 1
  rw [Kernel.map_apply _ (measurable_walkShift a)]
  exact N.continuation_walkShift_law A hpos a h

/-- Exact deterministic-time Markov factorization, including the whole prefix
and the whole future path as the two coordinates. -/
theorem trajectoryLaw_prefix_future (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (v : V) (a : ℕ) :
    (N.trajectoryLaw A hpos v).map (frestrictLe a) ⊗ₘ N.restartKernel A hpos a =
      (N.trajectoryLaw A hpos v).map (fun ω => (frestrictLe a ω, walkShift a ω)) := by
  rw [← N.continuation_map_walkShift A hpos a,
    Measure.compProd_map (measurable_walkShift a)]
  have hp := TrajectoryCoupling.prefix_compProd_traj
    (Measure.dirac v) (N.historyKernel A hpos) a
  change (N.trajectoryLaw A hpos v).map (frestrictLe a) ⊗ₘ
    Kernel.traj (X := fun _ => V) (N.historyKernel A hpos) a = _ at hp
  rw [hp, Measure.map_map (measurable_id.prodMap (measurable_walkShift a)) (by fun_prop)]
  rfl

end FiniteConductanceNetwork
end BouRabeeGwynne
