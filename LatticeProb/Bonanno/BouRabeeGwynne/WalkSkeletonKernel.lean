/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.WalkSkeletonKernel at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.ClockedWalkExcursion
import LatticeProb.Bonanno.BouRabeeGwynne.AbsorbingExcursionKernel
import LatticeProb.Bonanno.BouRabeeGwynne.ExcursionEndpointExtension

/-! The measurable history kernels for the actual clocked walk skeleton.
Each row retains the whole excursion and is defined at every spatial start. -/

open MeasureTheory ProbabilityTheory Set

namespace BouRabeeGwynne.FiniteConductanceNetwork

variable {d : ℕ} {V J : Type*} [Fintype V] [MeasurableSpace V]
  [MeasurableSingletonClass V] (N : FiniteConductanceNetwork V)

noncomputable def spatialClockedExcursionKernel (pos : V → Euc d)
    (hinj : Function.Injective pos) (B : Set V)
    (hB : ∀ v ∈ B, 0 < N.totalConductance v) : Kernel (Euc d) (ClockedWalkExcursion d) :=
  finiteVertexKernelExtension pos hinj (N.clockedWalkExcursionKernel pos B hB)
    ClockedWalkExcursion.constant ClockedWalkExcursion.measurable_constant

instance spatialClockedExcursionKernel_isMarkov (pos : V → Euc d)
    (hinj : Function.Injective pos) (B : Set V)
    (hB : ∀ v ∈ B, 0 < N.totalConductance v) :
    IsMarkovKernel (N.spatialClockedExcursionKernel pos hinj B hB) := by
  unfold spatialClockedExcursionKernel
  infer_instance

@[simp] lemma spatialClockedExcursionKernel_vertex (pos : V → Euc d)
    (hinj : Function.Injective pos) (B : Set V)
    (hB : ∀ v ∈ B, 0 < N.totalConductance v) (v : V) :
    N.spatialClockedExcursionKernel pos hinj B hB (pos v) =
      N.clockedWalkExcursionKernel pos B hB v :=
  finiteVertexKernelExtension_apply_vertex pos hinj _ _ _ v

lemma spatialClockedExcursionKernel_ae_start (pos : V → Euc d)
    (hinj : Function.Injective pos) (B : Set V)
    (hB : ∀ v ∈ B, 0 < N.totalConductance v) (z : Euc d) :
    ∀ᵐ e ∂N.spatialClockedExcursionKernel pos hinj B hB z,
      ClockedWalkExcursion.start e = z := by
  by_cases hz : z ∈ Set.range pos
  · obtain ⟨v, rfl⟩ := hz
    rw [N.spatialClockedExcursionKernel_vertex]
    exact N.clockedWalkExcursionKernel_ae_start pos B hB v
  · change ∀ᵐ e ∂finiteVertexKernelExtension pos hinj
      (N.clockedWalkExcursionKernel pos B hB) ClockedWalkExcursion.constant
      ClockedWalkExcursion.measurable_constant z, _
    rw [finiteVertexKernelExtension_apply_off_graph pos hinj _ _ _ hz]
    exact (ae_dirac_iff (measurableSet_eq_fun ClockedWalkExcursion.measurable_start
      measurable_const)).mpr rfl

variable [Countable J] [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]

noncomputable def walkSkeletonHistoryKernel (pos : V → Euc d)
    (hinj : Function.Injective pos) (B : J → Set V)
    (hB : ∀ j v, v ∈ B j → 0 < N.totalConductance v)
    (select : ℕ → Euc d → Option J) (hs : ∀ n, Measurable (select n)) (n : ℕ) :
    Kernel (Finset.Iic n → Bool × ClockedWalkExcursion d) (Bool × ClockedWalkExcursion d) :=
  (absorbingExcursionKernel (fun j => N.spatialClockedExcursionKernel pos hinj (B j) (hB j))
    ClockedWalkExcursion.endPoint ClockedWalkExcursion.measurable_endPoint
    ClockedWalkExcursion.constant ClockedWalkExcursion.measurable_constant
    (select n) (hs n)).comap (fun h => h ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (measurable_pi_apply _)

instance walkSkeletonHistoryKernel_isMarkov (pos : V → Euc d)
    (hinj : Function.Injective pos) (B : J → Set V)
    (hB : ∀ j v, v ∈ B j → 0 < N.totalConductance v)
    (select : ℕ → Euc d → Option J) (hs : ∀ n, Measurable (select n)) (n : ℕ) :
    IsMarkovKernel (N.walkSkeletonHistoryKernel pos hinj B hB select hs n) := by
  unfold walkSkeletonHistoryKernel
  infer_instance

end BouRabeeGwynne.FiniteConductanceNetwork
