/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.WalkSkeletonLaw at commit fdb5cad; local import paths and linter settings are adapted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.WalkSkeletonObservation
import LatticeProb.Bonanno.BouRabeeGwynne.WalkSkeletonKernel
import LatticeProb.Bonanno.BouRabeeGwynne.DependentKernelMapAE
import LatticeProb.Bonanno.BouRabeeGwynne.TrajectoryIdentification

/-! The exact full trajectory law of the rich excursions extracted from one
original ambient walk. Spatial selectors act on each marginal's own past. -/

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Set Preorder

namespace BouRabeeGwynne.FiniteConductanceNetwork

variable {d : ℕ} {V J : Type*} [Fintype V] [MeasurableSpace V]
  [MeasurableSingletonClass V] [Countable J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]

noncomputable def actualWalkExcursionSequence (pos : V → Euc d) (B : J → Set V)
    (initial : J) (select : ℕ → Euc d → Option J) (ω : ℕ → V) :
    ℕ → Bool × ClockedWalkExcursion d :=
  fun n => (actualWalkStage pos B initial (fun i v => select i (pos v)) n ω).2

lemma measurable_actualWalkExcursionSequence (pos : V → Euc d) (B : J → Set V)
    (initial : J) (select : ℕ → Euc d → Option J) :
    Measurable (actualWalkExcursionSequence pos B initial select) :=
  Measurable.of_eval fun n =>
    (measurable_actualWalkStage pos B initial (fun i v => select i (pos v)) n).snd

variable (N : FiniteConductanceNetwork V)

noncomputable def walkSkeletonInitialLaw (pos : V → Euc d) (B : J → Set V)
    (hB : ∀ j v, v ∈ B j → 0 < N.totalConductance v) (initial : J) (v : V) :
    Measure (Bool × ClockedWalkExcursion d) :=
  (N.clockedWalkExcursionKernel pos (B initial) (hB initial) v).map (fun e => (false, e))

instance walkSkeletonInitialLaw_isProbability (pos : V → Euc d) (B : J → Set V)
    (hB : ∀ j v, v ∈ B j → 0 < N.totalConductance v) (initial : J) (v : V) :
    IsProbabilityMeasure (N.walkSkeletonInitialLaw pos B hB initial v) :=
  (Measure.isProbabilityMeasure_map_iff
    (measurable_const.prodMk measurable_id).aemeasurable).mpr inferInstance

lemma trajectoryLaw_walkSkeleton_initial (pos : V → Euc d) {A : Set V}
    (B : J → Set V) (hBA : ∀ j, B j ⊆ A)
    (hA : ∀ v ∈ A, 0 < N.totalConductance v)
    (hB : ∀ j v, v ∈ B j → 0 < N.totalConductance v)
    (initial : J) (select : ℕ → Euc d → Option J) (v : V) :
    (N.trajectoryLaw A hA v).map (fun ω => actualWalkExcursionSequence pos B initial select ω 0) =
      N.walkSkeletonInitialLaw pos B hB initial v := by
  have hmark : Measurable (fun e : ClockedWalkExcursion d => (false, e)) :=
    measurable_const.prodMk measurable_id
  change (N.trajectoryLaw A hA v).map
    ((fun e => (false, e)) ∘ ClockedWalkExcursion.ofWalk pos (B initial)) = _
  rw [← Measure.map_map hmark (ClockedWalkExcursion.measurable_ofWalk pos (B initial)),
    N.trajectoryLaw_map_clockedExcursion pos (hBA initial) hA (hB initial)]
  rfl

lemma selectedClockedRestartKernel_eq_walkHistory (pos : V → Euc d)
    (hinj : Function.Injective pos) (B : J → Set V)
    (hB : ∀ j v, v ∈ B j → 0 < N.totalConductance v) (initial : J)
    (select : ℕ → Euc d → Option J) (hs : ∀ n, Measurable (select n)) (n : ℕ)
    (h : ℕ × (ℕ → V))
    (hend : ClockedWalkExcursion.endPoint
      (actualWalkStage pos B initial (fun i v => select i (pos v)) n h.2).2.2 =
      pos (h.2 h.1)) :
    N.selectedClockedRestartKernel pos B hB
      (walkStageSelector (actualWalkStage pos B initial (fun i v => select i (pos v)) n)
        (fun v => select n (pos v)))
      (measurable_walkStageSelector
        (measurable_actualWalkStage pos B initial (fun i v => select i (pos v)) n) _) h =
      N.walkSkeletonHistoryKernel pos hinj B hB select hs n
        (walkSkeletonPrefixOfPast pos B initial (fun i v => select i (pos v)) n h) := by
  change selectedExcursionKernel (fun j => N.clockedWalkExcursionKernel pos (B j) (hB j))
      (ClockedWalkExcursion.constant ∘ pos)
      (ClockedWalkExcursion.measurable_constant.comp (measurable_of_finite pos))
      ((if (actualWalkStage pos B initial (fun i v => select i (pos v)) n h.2).2.1 = true
        then none else select n (pos (h.2 h.1))), h.2 h.1) =
    absorbingExcursionKernel (fun j => N.spatialClockedExcursionKernel pos hinj (B j) (hB j))
      ClockedWalkExcursion.endPoint ClockedWalkExcursion.measurable_endPoint
      ClockedWalkExcursion.constant ClockedWalkExcursion.measurable_constant
      (select n) (hs n) (actualWalkStage pos B initial (fun i v => select i (pos v)) n h.2).2
  generalize he : (actualWalkStage pos B initial (fun i v => select i (pos v)) n h.2).2 = e at hend ⊢
  rcases e with ⟨flag, e⟩
  cases flag with
  | true =>
    change Measure.dirac (true, ClockedWalkExcursion.constant (pos (h.2 h.1))) =
      Measure.dirac (true, ClockedWalkExcursion.constant (ClockedWalkExcursion.endPoint e))
    rw [hend]
  | false =>
    change selectedExcursionKernel (fun j => N.clockedWalkExcursionKernel pos (B j) (hB j))
        (ClockedWalkExcursion.constant ∘ pos)
        (ClockedWalkExcursion.measurable_constant.comp (measurable_of_finite pos))
        (select n (pos (h.2 h.1)), h.2 h.1) =
      selectedExcursionKernel (fun j => N.spatialClockedExcursionKernel pos hinj (B j) (hB j))
        ClockedWalkExcursion.constant ClockedWalkExcursion.measurable_constant
        (select n (ClockedWalkExcursion.endPoint e), ClockedWalkExcursion.endPoint e)
    rw [hend]
    cases hj : select n (pos (h.2 h.1)) with
    | none => rfl
    | some j =>
      simp only [selectedExcursionKernel_some, N.spatialClockedExcursionKernel_vertex]

/-- The full observed excursion history and its next rich state have the
actual own-history transition law. -/
theorem trajectoryLaw_walkSkeleton_history_next (pos : V → Euc d)
    (hinj : Function.Injective pos) {A : Set V} (B : J → Set V)
    (hBA : ∀ j, B j ⊆ A) (hA : ∀ v ∈ A, 0 < N.totalConductance v)
    (hB : ∀ j v, v ∈ B j → 0 < N.totalConductance v)
    (haccess : N.BoundaryAccessible A) (initial : J)
    (select : ℕ → Euc d → Option J) (hs : ∀ n, Measurable (select n)) (v : V) (n : ℕ) :
    (N.trajectoryLaw A hA v).map (fun ω =>
      (frestrictLe n (actualWalkExcursionSequence pos B initial select ω),
        actualWalkExcursionSequence pos B initial select ω (n + 1))) =
      (N.trajectoryLaw A hA v).map
        (fun ω => frestrictLe n (actualWalkExcursionSequence pos B initial select ω))
        ⊗ₘ N.walkSkeletonHistoryKernel pos hinj B hB select hs n := by
  let vselect := fun i v => select i (pos v)
  let τ := fun ω => (actualWalkStage pos B initial vselect n ω).1
  let F := walkSkeletonPrefixOfPast pos B initial vselect n
  let choice := walkStageSelector (actualWalkStage pos B initial vselect n) (vselect n)
  let P := N.trajectoryLaw A hA v
  have hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => V)) τ :=
    actualWalkStage_clock_isStoppingTime pos B initial vselect n
  have hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤ := by
    filter_upwards [N.actualWalkStage_ae_all_clocks_finite pos B hBA hA haccess
      initial vselect v] with ω hω
    exact hω n
  have hobs : Measurable (observedHistory τ) := measurable_observedHistory hτ.measurable'
  have hF : Measurable F := measurable_walkSkeletonPrefixOfPast pos B initial vselect n
  have hc : Measurable choice := measurable_walkStageSelector
    (measurable_actualWalkStage pos B initial vselect n) (vselect n)
  have hend : ∀ᵐ h ∂P.map (observedHistory τ),
      ClockedWalkExcursion.endPoint (actualWalkStage pos B initial vselect n h.2).2.2 =
        pos (h.2 h.1) := by
    apply (ae_map_iff hobs.aemeasurable (measurableSet_eq_fun
      (ClockedWalkExcursion.measurable_endPoint.comp
        ((measurable_actualWalkStage pos B initial vselect n).snd.snd.comp measurable_snd))
      ((measurable_of_finite pos).comp measurable_historyLast))).mpr
    filter_upwards [hfin] with ω hω
    simp only [Function.comp_def]
    rw [actualWalkStage_observedPast pos B initial vselect n ω hω]
    exact actualWalkStage_endPoint_observed pos B initial vselect n ω hω
  have hrow : ∀ᵐ h ∂P.map (observedHistory τ),
      (N.selectedClockedRestartKernel pos B hB choice hc h).map id =
        N.walkSkeletonHistoryKernel pos hinj B hB select hs n (F h) := by
    filter_upwards [hend] with h hh
    rw [Measure.map_id]
    exact N.selectedClockedRestartKernel_eq_walkHistory pos hinj B hB initial select hs n h hh
  have hfactor := compProd_map_dependent_of_kernel_map_ae
    (P.map (observedHistory τ)) (N.selectedClockedRestartKernel pos B hB choice hc)
    (N.walkSkeletonHistoryKernel pos hinj B hB select hs n)
    F (fun _ e => e) hF measurable_snd hrow
  have hrecovery : ∀ᵐ ω ∂P, F (observedHistory τ ω) =
      frestrictLe n (actualWalkExcursionSequence pos B initial select ω) := by
    filter_upwards [hfin] with ω hω
    exact walkSkeletonPrefixOfPast_observed pos B initial vselect n ω hω
  have hpast : (P.map (observedHistory τ)).map F =
      P.map (fun ω => frestrictLe n (actualWalkExcursionSequence pos B initial select ω)) := by
    rw [Measure.map_map hF hobs]
    exact Measure.map_congr hrecovery
  have hnext : Measurable (fun ω : ℕ → V =>
      actualWalkExcursionSequence pos B initial select ω (n + 1)) :=
    (measurable_pi_apply (n + 1)).comp
      (measurable_actualWalkExcursionSequence pos B initial select)
  have hcompress : Measurable (fun p : (ℕ × (ℕ → V)) × (Bool × ClockedWalkExcursion d) =>
      (F p.1, p.2)) := (hF.comp measurable_fst).prodMk measurable_snd
  have hjoint : P.map (fun ω => (observedHistory τ ω,
      actualWalkExcursionSequence pos B initial select ω (n + 1))) =
      P.map (observedHistory τ) ⊗ₘ N.selectedClockedRestartKernel pos B hB choice hc :=
    N.trajectoryLaw_observed_selectedExcursion pos B hBA hA hB choice hc v hτ hfin
  calc
    _ = P.map (fun ω => (F (observedHistory τ ω),
        actualWalkExcursionSequence pos B initial select ω (n + 1))) := by
      apply Measure.map_congr
      filter_upwards [hrecovery] with ω hω
      exact congrArg (fun h => (h, actualWalkExcursionSequence pos B initial select ω (n + 1)))
        hω.symm
    _ = (P.map (fun ω => (observedHistory τ ω,
        actualWalkExcursionSequence pos B initial select ω (n + 1)))).map
          (fun p => (F p.1, p.2)) := by
      rw [Measure.map_map hcompress (hobs.prodMk hnext)]
      rfl
    _ = _ := by rw [hjoint, hfactor, hpast]

/-- The entire rich excursion sequence extracted from the original ambient
walk is the genuine adaptive trajectory measure, including permanent flags. -/
theorem trajectoryLaw_walkSkeleton_map (pos : V → Euc d)
    (hinj : Function.Injective pos) {A : Set V} (B : J → Set V)
    (hBA : ∀ j, B j ⊆ A) (hA : ∀ v ∈ A, 0 < N.totalConductance v)
    (hB : ∀ j v, v ∈ B j → 0 < N.totalConductance v)
    (haccess : N.BoundaryAccessible A) (initial : J)
    (select : ℕ → Euc d → Option J) (hs : ∀ n, Measurable (select n)) (v : V) :
    (N.trajectoryLaw A hA v).map (actualWalkExcursionSequence pos B initial select) =
      Kernel.trajMeasure (X := fun _ => Bool × ClockedWalkExcursion d)
        (N.walkSkeletonInitialLaw pos B hB initial v)
        (N.walkSkeletonHistoryKernel pos hinj B hB select hs) := by
  apply TrajectoryCoupling.map_eq_trajMeasure_of_history_next (N.trajectoryLaw A hA v) _
    (measurable_actualWalkExcursionSequence pos B initial select)
  · exact N.trajectoryLaw_walkSkeleton_initial pos B hBA hA hB initial select v
  · exact N.trajectoryLaw_walkSkeleton_history_next pos hinj B hBA hA hB haccess
      initial select hs v

end BouRabeeGwynne.FiniteConductanceNetwork
