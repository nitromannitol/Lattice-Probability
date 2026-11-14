/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.WalkSelectedRestart at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.WalkStrongMarkov
import LatticeProb.Bonanno.BouRabeeGwynne.WalkAbsorption
import LatticeProb.Bonanno.BouRabeeGwynne.AbsorbingExcursionKernel
import LatticeProb.Bonanno.BouRabeeGwynne.DependentKernelMap

/-! Exact conditional laws for whole clocked excursions selected from the
observed past of the original ambient walk. -/

open MeasureTheory ProbabilityTheory Set

namespace BouRabeeGwynne.FiniteConductanceNetwork

variable {d : ℕ} {V J : Type*} [Fintype V] [MeasurableSpace V]
  [MeasurableSingletonClass V] [Countable J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]

noncomputable def selectedClockedExcursion (pos : V → Euc d) (B : J → Set V)
    (p : Option J × V) (ω : ℕ → V) : Bool × ClockedWalkExcursion d :=
  match p.1 with
  | none => (true, ClockedWalkExcursion.constant (pos p.2))
  | some j => (false, ClockedWalkExcursion.ofWalk pos (B j) ω)

lemma measurable_selectedClockedExcursion (pos : V → Euc d) (B : J → Set V) :
    Measurable (fun p : (Option J × V) × (ℕ → V) =>
      selectedClockedExcursion pos B p.1 p.2) := by
  apply measurable_from_prod_countable_right
  rintro ⟨j, v⟩
  cases j with
  | none =>
    change Measurable (fun _ : ℕ → V => (true, ClockedWalkExcursion.constant (pos v)))
    exact measurable_const
  | some j => exact measurable_const.prodMk (ClockedWalkExcursion.measurable_ofWalk pos (B j))

variable (N : FiniteConductanceNetwork V)

/-- This is the same selected kernel used by the coupled skeleton, pulled
back along the actual observed terminal vertex and the past-dependent choice. -/
noncomputable def selectedClockedRestartKernel (pos : V → Euc d) (B : J → Set V)
    (hB : ∀ j v, v ∈ B j → 0 < N.totalConductance v)
    (select : (ℕ × (ℕ → V)) → Option J) (hs : Measurable select) :
    Kernel (ℕ × (ℕ → V)) (Bool × ClockedWalkExcursion d) :=
  (selectedExcursionKernel (fun j => N.clockedWalkExcursionKernel pos (B j) (hB j))
    (ClockedWalkExcursion.constant ∘ pos)
    (ClockedWalkExcursion.measurable_constant.comp (measurable_of_finite pos))).comap
      (fun h => (select h, h.2 h.1)) (hs.prodMk measurable_historyLast)

instance selectedClockedRestartKernel_isMarkov (pos : V → Euc d) (B : J → Set V)
    (hB : ∀ j v, v ∈ B j → 0 < N.totalConductance v)
    (select : (ℕ × (ℕ → V)) → Option J) (hs : Measurable select) :
    IsMarkovKernel (N.selectedClockedRestartKernel pos B hB select hs) := by
  unfold selectedClockedRestartKernel
  infer_instance

lemma observedRestartKernel_map_selectedClockedExcursion (pos : V → Euc d)
    {A : Set V} (B : J → Set V) (hBA : ∀ j, B j ⊆ A)
    (hA : ∀ v ∈ A, 0 < N.totalConductance v)
    (hB : ∀ j v, v ∈ B j → 0 < N.totalConductance v)
    (select : (ℕ × (ℕ → V)) → Option J) (hs : Measurable select)
    (h : ℕ × (ℕ → V)) :
    (N.observedRestartKernel A hA h).map
        (selectedClockedExcursion pos B (select h, h.2 h.1)) =
      N.selectedClockedRestartKernel pos B hB select hs h := by
  change (N.trajectoryLaw A hA (h.2 h.1)).map
      (selectedClockedExcursion pos B (select h, h.2 h.1)) =
    selectedExcursionKernel (fun j => N.clockedWalkExcursionKernel pos (B j) (hB j))
      (ClockedWalkExcursion.constant ∘ pos)
      (ClockedWalkExcursion.measurable_constant.comp (measurable_of_finite pos))
      (select h, h.2 h.1)
  cases hj : select h with
  | none =>
    change (N.trajectoryLaw A hA (h.2 h.1)).map
      (fun _ : ℕ → V => (true, ClockedWalkExcursion.constant (pos (h.2 h.1)))) =
      Measure.dirac (true, ClockedWalkExcursion.constant (pos (h.2 h.1)))
    rw [Measure.map_const, measure_univ, one_smul]
  | some j =>
    rw [selectedExcursionKernel_some]
    change (N.trajectoryLaw A hA (h.2 h.1)).map
        ((fun e => (false, e)) ∘ ClockedWalkExcursion.ofWalk pos (B j)) = _
    have hmark : Measurable (fun e : ClockedWalkExcursion d => (false, e)) :=
      measurable_const.prodMk measurable_id
    rw [← Measure.map_map hmark
      (ClockedWalkExcursion.measurable_ofWalk pos (B j)),
      N.trajectoryLaw_map_clockedExcursion pos (hBA j) hA (hB j)]

/-- The entire observed past and the next selected whole excursion have the
joint law given by the genuine selected kernel. The first component has not
been replaced by the endpoint marginal. -/
theorem trajectoryLaw_observed_selectedExcursion (pos : V → Euc d)
    {A : Set V} (B : J → Set V) (hBA : ∀ j, B j ⊆ A)
    (hA : ∀ v ∈ A, 0 < N.totalConductance v)
    (hB : ∀ j v, v ∈ B j → 0 < N.totalConductance v)
    (select : (ℕ × (ℕ → V)) → Option J) (hs : Measurable select) (v : V)
    {τ : (ℕ → V) → WithTop ℕ}
    (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => V)) τ)
    (hfin : ∀ᵐ ω ∂N.trajectoryLaw A hA v, τ ω ≠ ⊤) :
    (N.trajectoryLaw A hA v).map (fun ω =>
      (observedHistory τ ω, selectedClockedExcursion pos B
        (select (observedHistory τ ω), (observedHistory τ ω).2 (observedHistory τ ω).1)
        (futureAt τ ω))) =
      (N.trajectoryLaw A hA v).map (observedHistory τ)
        ⊗ₘ N.selectedClockedRestartKernel pos B hB select hs := by
  let g : (ℕ × (ℕ → V)) → (ℕ → V) → Bool × ClockedWalkExcursion d :=
    fun h ω => selectedClockedExcursion pos B (select h, h.2 h.1) ω
  have hg : Measurable (fun p : (ℕ × (ℕ → V)) × (ℕ → V) => g p.1 p.2) :=
    (measurable_selectedClockedExcursion pos B).comp
      (((hs.prodMk measurable_historyLast).comp measurable_fst).prodMk measurable_snd)
  have hobs := measurable_observedHistory hτ.measurable'
  have hfuture := measurable_futureAt hτ.measurable'
  have hpair : Measurable (fun p : (ℕ × (ℕ → V)) × (ℕ → V) =>
      (id p.1, g p.1 p.2)) := measurable_fst.prodMk hg
  have hjoint : Measurable (fun ω : ℕ → V => (observedHistory τ ω, futureAt τ ω)) :=
    hobs.prodMk hfuture
  have hfactor := compProd_map_dependent_of_kernel_map
    ((N.trajectoryLaw A hA v).map (observedHistory τ))
    (N.observedRestartKernel A hA) (N.selectedClockedRestartKernel pos B hB select hs)
    id g measurable_id hg
    (N.observedRestartKernel_map_selectedClockedExcursion pos B hBA hA hB select hs)
  rw [Measure.map_id, N.trajectoryLaw_observed_future A hA v hτ hfin,
    Measure.map_map hpair hjoint] at hfactor
  exact hfactor

end BouRabeeGwynne.FiniteConductanceNetwork
