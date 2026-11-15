import LatticeProb.Prob.OpenEntryClockEndpoints
import LatticeProb.Prob.AlternatingClockEndpoints
import LatticeProb.Topology.ExtendedAlternatingTermination
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

/-! # Alternating entry and exit clocks of transient paths -/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace LatticeProb

/-- For a transient continuous path, finite entries into a bounded set are
uniformly bounded in time, independently of the starting clock. -/
theorem exists_upper_bound_openEntryAfter_of_transient
    {Ω E : Type*} [MetricSpace E] [ProperSpace E]
    (f : Ω → ℝ → E) (ω : Ω) (U : Set E)
    (hf : Continuous (f ω))
    (htr : Tendsto (f ω) (cocompact ℝ) (cocompact E))
    (hU : Bornology.IsBounded U) :
    ∃ b : ℝ, ∀ a : Ω → WithTop ℝ, openEntryAfter f a U ω ≠ ⊤ →
      openEntryAfter f a U ω ≤ (b : WithTop ℝ) := by
  have hmem : (f ω) ⁻¹' (closure U)ᶜ ∈ cocompact ℝ :=
    htr hU.isCompact_closure.compl_mem_cocompact
  obtain ⟨K, hK, hKsub⟩ := mem_cocompact.mp hmem
  obtain ⟨b, hb⟩ := hK.bddAbove
  refine ⟨b, fun a hfin => ?_⟩
  have hend := openEntryAfter_mem_closure f a U ω hf hfin
  have htime : (openEntryAfter f a U ω).untopD 0 ∈ K := by
    by_contra hn
    exact hKsub hn hend
  have hcoe : (((openEntryAfter f a U ω).untopD 0 : ℝ) : WithTop ℝ) =
      openEntryAfter f a U ω := by
    generalize heq : openEntryAfter f a U ω = x at hfin ⊢
    lift x to ℝ using hfin
    rfl
  rw [← hcoe]
  exact WithTop.coe_le_coe.mpr (hb htime)

/-- Alternating entries into a bounded set and exits from a neighborhood of
its closure terminate for each transient path. -/
theorem exists_top_alternatingEntryClock_of_transient
    {Ω : Type*} {d : ℕ} (f : Ω → C(ℝ, EuclideanSpace ℝ (Fin d)))
    (a : Ω → WithTop ℝ) (ω : Ω) (U V : Set (EuclideanSpace ℝ (Fin d)))
    (htr : Tendsto (f ω) (cocompact ℝ) (cocompact _))
    (hU : Bornology.IsBounded U) (hV : IsOpen V) (hUV : closure U ⊆ V) :
    ∃ n, openEntryAfter (fun ω t => f ω t) (alternatingExitClock f a U V n) U ω = ⊤ := by
  obtain ⟨b, hb⟩ := exists_upper_bound_openEntryAfter_of_transient
    (fun ω t => f ω t) ω U (f ω).continuous htr hU
  let s : ℕ → WithTop ℝ := fun n =>
    openEntryAfter (fun ω t => f ω t) (alternatingExitClock f a U V n) U ω
  let t : ℕ → WithTop ℝ := fun n => alternatingExitClock f a U V (n + 1) ω
  apply exists_top_of_bounded_alternating_clocks (f ω) (f ω).continuous
    isClosed_closure hV hUV s t b
  · intro n hn
    exact hb _ hn
  · intro n
    change openEntryAfter (fun ω t => f ω t) (alternatingExitClock f a U V n) U ω ≤
      closedExitAfter f (openEntryAfter (fun ω t => f ω t)
        (alternatingExitClock f a U V n) U) V ω
    exact le_closedExitAfter f _ V ω
  · intro n
    change alternatingExitClock f a U V (n + 1) ω ≤
      openEntryAfter (fun ω t => f ω t) (alternatingExitClock f a U V (n + 1)) U ω
    exact le_openEntryAfter _ _ U ω
  · intro n hn
    exact openEntryAfter_mem_closure _ _ U ω (f ω).continuous hn
  · intro n hn
    exact closedExitAfter_not_mem f _ hV ω hn

end LatticeProb
