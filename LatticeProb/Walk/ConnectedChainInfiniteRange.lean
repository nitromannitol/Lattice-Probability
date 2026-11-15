import LatticeProb.Bonanno.MatedCRTHarmonic.GMS3.Walk
import Mathlib.Combinatorics.SimpleGraph.Walk.Traversal

/-! # Infinite range of a connected Markov chain -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open MatedCRTHarmonic.Markov
open scoped ENNReal

namespace LatticeProb

variable {S : Type*} [MeasurableSpace S] [MeasurableSingletonClass S]
  (κ : Kernel S S) [IsMarkovKernel κ] (G : SimpleGraph S)
  (hG : G.Connected) (hstep : ∀ x y, G.Adj x y → 0 < κ x {y})

include hG hstep

/-- A chain with positive transition probabilities along the edges of a connected
    graph has a positive probability of hitting any nonempty set. -/
theorem chainLaw_hit_pos_of_connected {A : Set S} (hA : A.Nonempty) (x : S) :
    0 < chainLaw κ x {ω | hitTime A ω < ⊤} := by
  obtain ⟨y, hy⟩ := hA
  obtain ⟨p⟩ := hG.preconnected x y
  exact chainLaw_hitTime_lt_top_pos κ p.getVert p.length p.getVert_zero
    (by simpa using hy) (fun i hi => hstep _ _ (p.adj_getVert_succ hi))

/-- On an infinite connected graph, such a chain exits each finite set almost surely. -/
theorem chainLaw_ae_exit_finite [Infinite S] {A : Set S} (hA : A.Finite) (x : S) :
    ∀ᵐ ω ∂chainLaw κ x, ∃ n, ω n ∉ A := by
  have hne : Aᶜ.Nonempty := by
    by_contra h
    have : A = Set.univ := Set.eq_univ_iff_forall.mpr (fun y => by
      by_contra hy
      exact h ⟨y, hy⟩)
    exact Set.infinite_univ (this ▸ hA)
  have hpos : ∀ s ∈ A, 0 < chainLaw κ s {ω : ℕ → S | ∃ n, ω n ∉ A} := by
    intro s _
    simpa only [hitTime_lt_top_iff, Set.mem_compl_iff] using
      chainLaw_hit_pos_of_connected κ G hG hstep hne s
  have h := MatedCRTHarmonic.GMS3.chainLaw_exists_notMem_eq_one κ hA hpos x
  have hexit : MeasurableSet {ω : ℕ → S | ∃ n, ω n ∉ A} := by
    have heq : {ω : ℕ → S | ∃ n, ω n ∉ A} =
        ⋃ n : ℕ, (fun ω : ℕ → S => ω n) ⁻¹' Aᶜ := by
      ext ω
      simp
    rw [heq]
    exact MeasurableSet.iUnion fun n => hA.measurableSet.compl.preimage (measurable_pi_apply n)
  exact (mem_ae_iff_prob_eq_one hexit).2 h

/-- A Markov chain on an infinite connected graph visits infinitely many vertices
    almost surely if every graph edge has positive transition probability. -/
theorem chainLaw_ae_infinite_range [Countable S] [Infinite S] (x : S) :
    ∀ᵐ ω ∂chainLaw κ x, (Set.range ω).Infinite := by
  have he : ∀ᵐ ω ∂chainLaw κ x, ∀ A : Finset S, ∃ n, ω n ∉ A := by
    rw [ae_all_iff]
    intro A
    exact chainLaw_ae_exit_finite κ G hG hstep A.finite_toSet x
  filter_upwards [he] with ω hω hfinite
  obtain ⟨n, hn⟩ := hω hfinite.toFinset
  exact hn (hfinite.mem_toFinset.mpr (Set.mem_range_self n))

end LatticeProb
end
