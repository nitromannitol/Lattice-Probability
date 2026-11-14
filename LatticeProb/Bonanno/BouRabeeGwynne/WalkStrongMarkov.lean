/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.WalkStrongMarkov at commit fdb5cad; local imports are rewritten and one unused-section-variable lint check is disabled. -/
import LatticeProb.Bonanno.BouRabeeGwynne.WalkStoppedHistory

/-! Full-path strong Markov factorization for the actual finite conductance
walk, obtained by restricting the deterministic-time joint law and summing
over the finite values of the original stopping time. -/

open MeasureTheory ProbabilityTheory Set Preorder

namespace BouRabeeGwynne
namespace FiniteConductanceNetwork

variable {V : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
  (N : FiniteConductanceNetwork V)

set_option linter.unusedSectionVars false in
lemma measurable_historyLast : Measurable (fun h : ℕ × (ℕ → V) => h.2 h.1) :=
  measurable_from_prod_countable_right fun n => measurable_pi_apply n

/-- A fresh genuine walk started at the terminal vertex of an observed history. -/
noncomputable def observedRestartKernel (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) : Kernel (ℕ × (ℕ → V)) (ℕ → V) :=
  (N.walkPathKernel A hpos).comap (fun h => h.2 h.1) measurable_historyLast

noncomputable instance observedRestartKernel_isMarkovKernel (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) :
    IsMarkovKernel (N.observedRestartKernel A hpos) := by
  unfold observedRestartKernel
  infer_instance

lemma trajectoryLaw_prefix_future_restrict (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (v : V) (n : ℕ)
    {s : Set (Finset.Iic n → V)} (hs : MeasurableSet s) :
    ((N.trajectoryLaw A hpos v).restrict (frestrictLe n ⁻¹' s)).map (frestrictLe n)
        ⊗ₘ N.restartKernel A hpos n =
      ((N.trajectoryLaw A hpos v).restrict (frestrictLe n ⁻¹' s)).map
        (fun ω => (frestrictLe n ω, walkShift n ω)) := by
  rw [← Measure.restrict_map (measurable_frestrictLe n) hs,
    TrajectoryCoupling.compProd_restrict_first _ _ hs,
    N.trajectoryLaw_prefix_future A hpos v n,
    Measure.restrict_map ((measurable_frestrictLe n).prodMk (measurable_walkShift n))
      (hs.preimage measurable_fst)]
  rfl

lemma trajectoryLaw_observed_future_slice (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (v : V)
    {τ : (ℕ → V) → WithTop ℕ}
    (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => V)) τ) (n : ℕ) :
    ((N.trajectoryLaw A hpos v).restrict {ω | τ ω = n}).map (observedHistory τ)
        ⊗ₘ N.observedRestartKernel A hpos =
      ((N.trajectoryLaw A hpos v).restrict {ω | τ ω = n}).map
        (fun ω => (observedHistory τ ω, futureAt τ ω)) := by
  obtain ⟨s, hs, hseq⟩ := stopping_event_prefix hτ n
  let μn := (N.trajectoryLaw A hpos v).restrict {ω | τ ω = n}
  have hm : MeasurableSet {ω | τ ω = n} :=
    measurableSet_eq_fun hτ.measurable' measurable_const
  have hae : ∀ᵐ ω ∂μn, τ ω = n := ae_restrict_mem hm
  have hobs : μn.map (observedHistory τ) =
      μn.map (paddedHistory n ∘ frestrictLe n) := by
    apply Measure.map_congr
    filter_upwards [hae] with ω hω
    exact observedHistory_of_eq hω
  have hjoint : μn.map (fun ω => (observedHistory τ ω, futureAt τ ω)) =
      μn.map (fun ω => (paddedHistory n (frestrictLe n ω), walkShift n ω)) := by
    apply Measure.map_congr
    filter_upwards [hae] with ω hω
    rw [observedHistory_of_eq hω, futureAt_of_eq hω]
  have hrestart (h : Finset.Iic n → V) :
      (N.restartKernel A hpos n h).map id =
        N.observedRestartKernel A hpos (paddedHistory n h) := by
    rw [Measure.map_id]
    simp only [restartKernel, observedRestartKernel, Kernel.comap_apply,
      paddedHistory, min_self]
  have hprefix := N.trajectoryLaw_prefix_future_restrict A hpos v n hs
  rw [hseq] at hprefix
  change μn.map (frestrictLe n) ⊗ₘ N.restartKernel A hpos n = _ at hprefix
  change μn.map (observedHistory τ) ⊗ₘ N.observedRestartKernel A hpos = _
  rw [hobs, hjoint,
    ← Measure.map_map (measurable_paddedHistory n) (measurable_frestrictLe n),
    ← compProd_map_prod_of_kernel_map _ _ _ _ _ (measurable_paddedHistory n)
      measurable_id hrestart,
    hprefix,
    Measure.map_map ((measurable_paddedHistory n).prodMap measurable_id)
      ((measurable_frestrictLe n).prodMk (measurable_walkShift n))]
  rfl

/-- The observed finite history and the entire future path have the exact
strong Markov joint law. The stopping time itself retains its possible value
`⊤`; its finiteness is used only almost surely under the actual walk law. -/
theorem trajectoryLaw_observed_future (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (v : V)
    {τ : (ℕ → V) → WithTop ℕ}
    (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => V)) τ)
    (hfin : ∀ᵐ ω ∂N.trajectoryLaw A hpos v, τ ω ≠ ⊤) :
    (N.trajectoryLaw A hpos v).map (observedHistory τ)
        ⊗ₘ N.observedRestartKernel A hpos =
      (N.trajectoryLaw A hpos v).map
        (fun ω => (observedHistory τ ω, futureAt τ ω)) := by
  have hμ := measure_eq_sum_stopping_slices (N.trajectoryLaw A hpos v) hτ.measurable' hfin
  have hobs := measurable_observedHistory hτ.measurable'
  have hjoint := hobs.prodMk (measurable_futureAt hτ.measurable')
  calc
    _ = (Measure.sum (fun n : ℕ => (N.trajectoryLaw A hpos v).restrict {ω | τ ω = n})).map
          (observedHistory τ) ⊗ₘ N.observedRestartKernel A hpos := by rw [← hμ]
    _ = Measure.sum (fun n : ℕ =>
        ((N.trajectoryLaw A hpos v).restrict {ω | τ ω = n}).map (observedHistory τ)
          ⊗ₘ N.observedRestartKernel A hpos) := by
      rw [Measure.map_sum hobs.aemeasurable, Measure.compProd_sum_left]
    _ = Measure.sum (fun n : ℕ =>
        ((N.trajectoryLaw A hpos v).restrict {ω | τ ω = n}).map
          (fun ω => (observedHistory τ ω, futureAt τ ω))) := by
      congr 1
      funext n
      exact N.trajectoryLaw_observed_future_slice A hpos v hτ n
    _ = _ := by rw [← Measure.map_sum hjoint.aemeasurable, ← hμ]

end FiniteConductanceNetwork
end BouRabeeGwynne
