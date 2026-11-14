/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.WalkBrownianCoupling at commit fdb5cad; local import paths and linter settings are adapted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.WalkSkeletonLaw
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianSkeletonLaw
import LatticeProb.Bonanno.BouRabeeGwynne.FinitePartitionCouplingKernel
import LatticeProb.Bonanno.BouRabeeGwynne.FiniteCellCouplingError
import LatticeProb.Bonanno.BouRabeeGwynne.SkeletonCoupling

/-! A concrete coupling of the original walk and Brownian excursion sequences.
The walk retains its integer clock and padded vertices; matching cells refer
only to the endpoints of active whole excursions. -/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Set Preorder
open scoped unitInterval ENNReal

namespace BouRabeeGwynne

variable {d : ℕ}

/-- The permanent termination flag is excluded from active matching cells. -/
def activeEndpointCell {S : Type*} (endpoint : S → Euc d) (E : Set (Euc d)) :
    Set (Bool × S) := {q | q.1 = false ∧ endpoint q.2 ∈ E}

lemma measurableSet_activeEndpointCell {S : Type*} [MeasurableSpace S]
    (endpoint : S → Euc d) (he : Measurable endpoint) {E : Set (Euc d)}
    (hE : MeasurableSet E) : MeasurableSet (activeEndpointCell endpoint E) :=
  (measurable_fst (measurableSet_singleton false)).inter ((he.comp measurable_snd) hE)

lemma pairwiseDisjoint_activeEndpointCell {S ι : Type*} (endpoint : S → Euc d)
    {E : ι → Set (Euc d)} (hE : Pairwise (fun i j => Disjoint (E i) (E j))) :
    Pairwise (fun i j => Disjoint (activeEndpointCell endpoint (E i))
      (activeEndpointCell endpoint (E j))) := by
  intro i j hij
  exact Set.disjoint_left.mpr (fun q hqi hqj => Set.disjoint_left.mp (hE hij) hqi.2 hqj.2)

/-- The Brownian clock uses successor-indexed selectors. State zero is the
fixed initial excursion, so shifting the selector makes transition n use E_n. -/
def brownianSelectorForWalk {J : Type*} (select : ℕ → Euc d → Option J) :
    ℕ → Euc d → Option J := fun n => select (n - 1)

@[simp] lemma brownianSelectorForWalk_succ {J : Type*}
    (select : ℕ → Euc d → Option J) (n : ℕ) :
    brownianSelectorForWalk select (n + 1) = select n := by
  simp [brownianSelectorForWalk]

/-- Walk matching cells retain the finite graph support explicitly, so an
invalid off-graph history cannot be treated as a successful active state. -/
def walkEndpointCell {V : Type*} (pos : V → Euc d) (E : Set (Euc d)) :
    Set (Bool × ClockedWalkExcursion d) :=
  activeEndpointCell ClockedWalkExcursion.endPoint (E ∩ Set.range pos)

lemma measurableSet_walkEndpointCell {V : Type*} [Finite V] (pos : V → Euc d)
    {E : Set (Euc d)} (hE : MeasurableSet E) : MeasurableSet (walkEndpointCell pos E) :=
  measurableSet_activeEndpointCell _ ClockedWalkExcursion.measurable_endPoint
    (hE.inter (Set.finite_range pos).measurableSet)

lemma pairwiseDisjoint_walkEndpointCell {V ι : Type*} (pos : V → Euc d)
    {E : ι → Set (Euc d)} (hE : Pairwise (fun i j => Disjoint (E i) (E j))) :
    Pairwise (fun i j => Disjoint (walkEndpointCell pos (E i)) (walkEndpointCell pos (E j))) :=
  pairwiseDisjoint_activeEndpointCell _
    (fun i j hij => (hE hij).mono inter_subset_left inter_subset_left)

namespace FiniteConductanceNetwork

variable {V J : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable J] [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
  (N : FiniteConductanceNetwork V) (pos : V → Euc d) (hinj : Function.Injective pos)
  (B : J → Set V) (hB : ∀ j v, v ∈ B j → 0 < N.totalConductance v)
  (U : J → Set (Euc d)) (hU : ∀ j, IsOpen (U j))
  (μ : Measure (BrownianPath d)) [IsProbabilityMeasure μ]
  (select : ℕ → Euc d → Option J) (hs : ∀ n, Measurable (select n))
  (m : ℕ → ℕ) (E : ∀ n, Fin (m n) → Set (Euc d))
  (hE : ∀ n i, MeasurableSet (E n i))
  (hdE : ∀ n, Pairwise (fun i j => Disjoint (E n i) (E n j)))

noncomputable def walkBrownianCouplingKernel (n : ℕ) :
    Kernel (Finset.Iic n → (Bool × ClockedWalkExcursion d) ×
      (Bool × C(unitInterval, Euc d)))
      ((Bool × ClockedWalkExcursion d) × (Bool × C(unitInterval, Euc d))) :=
  finitePartitionCouplingKernel
    ((N.walkSkeletonHistoryKernel pos hinj B hB select hs n).comap
      (TrajectoryCoupling.prefixMap Prod.fst n)
      (TrajectoryCoupling.measurable_prefixMap measurable_fst n))
    ((brownianSkeletonKernel U hU μ (brownianSelectorForWalk select)
      (fun n => hs (n - 1)) n).comap
      (TrajectoryCoupling.prefixMap Prod.snd n)
      (TrajectoryCoupling.measurable_prefixMap measurable_snd n))
    (fun i => measurableSet_walkEndpointCell pos (hE (n + 1) i))
    (fun i => measurableSet_activeEndpointCell (fun c : C(unitInterval, Euc d) => c 1)
      (ContinuousMap.measurable_eval 1) (hE (n + 1) i))
    (pairwiseDisjoint_walkEndpointCell pos (hdE (n + 1)))
    (pairwiseDisjoint_activeEndpointCell _ (hdE (n + 1)))

instance walkBrownianCouplingKernel_isMarkov (n : ℕ) :
    IsMarkovKernel (N.walkBrownianCouplingKernel pos hinj B hB U hU μ select hs m E hE hdE n) := by
  unfold walkBrownianCouplingKernel
  infer_instance

lemma walkBrownianCouplingKernel_marginals (n : ℕ) (h) :
    (N.walkBrownianCouplingKernel pos hinj B hB U hU μ select hs m E hE hdE n h).fst =
      N.walkSkeletonHistoryKernel pos hinj B hB select hs n
        (TrajectoryCoupling.prefixMap Prod.fst n h) ∧
    (N.walkBrownianCouplingKernel pos hinj B hB U hU μ select hs m E hE hdE n h).snd =
      brownianSkeletonKernel U hU μ (brownianSelectorForWalk select)
        (fun n => hs (n - 1)) n (TrajectoryCoupling.prefixMap Prod.snd n h) := by
  exact (finitePartitionCouplingKernel_spec _ _ _ _ _ _ h).imp_right (fun h => h.1)

noncomputable def walkBrownianInitialCoupling (initial : J) (v : V) (z : Euc d) :
    Measure ((Bool × ClockedWalkExcursion d) × (Bool × C(unitInterval, Euc d))) :=
  finitePartitionCoupling (N.walkSkeletonInitialLaw pos B hB initial v)
    (brownianSkeletonInitialLaw U hU μ z initial)
    (fun i : Fin (m 0) => walkEndpointCell pos (E 0 i))
    (fun i : Fin (m 0) => activeEndpointCell (fun c : C(unitInterval, Euc d) => c 1) (E 0 i))

include hE hdE in
lemma walkBrownianInitialCoupling_isProbability (initial : J) (v : V) (z : Euc d) :
    IsProbabilityMeasure (N.walkBrownianInitialCoupling pos B hB U hU μ m E initial v z) := by
  exact (finitePartitionCoupling_spec _ _
    (fun i => measurableSet_walkEndpointCell pos (hE 0 i))
    (fun i => measurableSet_activeEndpointCell _ (ContinuousMap.measurable_eval 1) (hE 0 i))
    (pairwiseDisjoint_walkEndpointCell pos (hdE 0))
    (pairwiseDisjoint_activeEndpointCell _ (hdE 0))).1

include hE hdE in
lemma walkBrownianInitialCoupling_marginals (initial : J) (v : V) (z : Euc d) :
    (N.walkBrownianInitialCoupling pos B hB U hU μ m E initial v z).fst =
      N.walkSkeletonInitialLaw pos B hB initial v ∧
    (N.walkBrownianInitialCoupling pos B hB U hU μ m E initial v z).snd =
      brownianSkeletonInitialLaw U hU μ z initial := by
  exact (finitePartitionCoupling_spec _ _
    (fun i => measurableSet_walkEndpointCell pos (hE 0 i))
    (fun i => measurableSet_activeEndpointCell _ (ContinuousMap.measurable_eval 1) (hE 0 i))
    (pairwiseDisjoint_walkEndpointCell pos (hdE 0))
    (pairwiseDisjoint_activeEndpointCell _ (hdE 0))).2.imp_right (fun h => h.1)

/-- An actual joint measure on whole rich walk and whole Brownian excursion
sequences, obtained from the explicit measurable finite-cell couplings. -/
noncomputable def walkBrownianJointLaw (initial : J) (v : V) (z : Euc d) :
    Measure ((ℕ → Bool × ClockedWalkExcursion d) × (ℕ → Bool × C(unitInterval, Euc d))) := by
  letI := N.walkBrownianInitialCoupling_isProbability pos B hB U hU μ m E hE hdE initial v z
  exact SkeletonCoupling.jointPathLaw
    (N.walkBrownianInitialCoupling pos B hB U hU μ m E initial v z)
    (N.walkBrownianCouplingKernel pos hinj B hB U hU μ select hs m E hE hdE)

/-- Both marginals are pushforwards of the original processes, with their
whole actual excursion histories, rather than only their endpoint marginals. -/
theorem walkBrownianJointLaw_marginals (hd : 1 ≤ d) (hμ : IsStandardBrownianLaw μ)
    (hUb : ∀ j, Bornology.IsBounded (U j))
    {A : Set V} (hBA : ∀ j, B j ⊆ A)
    (hA : ∀ v ∈ A, 0 < N.totalConductance v) (haccess : N.BoundaryAccessible A)
    (initial : J) (v : V) (z : Euc d) :
    (N.walkBrownianJointLaw pos hinj B hB U hU μ select hs m E hE hdE initial v z).fst =
      (N.trajectoryLaw A hA v).map (actualWalkExcursionSequence pos B initial select) ∧
    (N.walkBrownianJointLaw pos hinj B hB U hU μ select hs m E hE hdE initial v z).snd =
      μ.map (fun ω k => brownianSkeletonExcursion U z initial
        (brownianSelectorForWalk select) k ω) := by
  letI := N.walkBrownianInitialCoupling_isProbability pos B hB U hU μ m E hE hdE initial v z
  have hinit := N.walkBrownianInitialCoupling_marginals pos B hB U hU μ m E hE hdE initial v z
  have hstep := N.walkBrownianCouplingKernel_marginals pos hinj B hB U hU μ select hs m E hE hdE
  constructor
  · rw [N.trajectoryLaw_walkSkeleton_map pos hinj B hBA hA hB haccess initial select hs v]
    exact SkeletonCoupling.jointPathLaw_fst _ _ _ _ hinit.1 (fun n h => (hstep n h).1)
  · rw [standardBrownianLaw_skeleton_map hd hμ U hU hUb z initial
      (brownianSelectorForWalk select) (fun n => hs (n - 1))]
    exact SkeletonCoupling.jointPathLaw_snd _ _ _ _ hinit.2 (fun n h => (hstep n h).2)

end FiniteConductanceNetwork
end BouRabeeGwynne
