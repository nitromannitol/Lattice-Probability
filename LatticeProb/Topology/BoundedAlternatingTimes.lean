import Mathlib

/-! # Alternating visits in bounded time -/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace LatticeProb

/-- A continuous curve cannot alternate indefinitely between a closed set and
    the complement of an open neighborhood while its entry times are bounded. -/
theorem not_bounded_alternating_times {E : Type*} [TopologicalSpace E]
    (f : ℝ → E) (hf : Continuous f) {C O : Set E}
    (hC : IsClosed C) (hO : IsOpen O) (hCO : C ⊆ O)
    (s t : ℕ → ℝ) (b : ℝ) (hbound : ∀ n, s n ≤ b)
    (hst : ∀ n, s n ≤ t n) (hts : ∀ n, t n ≤ s (n + 1))
    (hs : ∀ n, f (s n) ∈ C) (ht : ∀ n, f (t n) ∉ O) : False := by
  have hmono : Monotone s := monotone_nat_of_le_succ fun n => (hst n).trans (hts n)
  have hbounded : BddAbove (range s) := ⟨b, by rintro _ ⟨n, rfl⟩; exact hbound n⟩
  have hlim : Tendsto s atTop (𝓝 (⨆ n, s n)) := tendsto_atTop_ciSup hmono hbounded
  have hlimnext : Tendsto (fun n => s (n + 1)) atTop (𝓝 (⨆ n, s n)) :=
    hlim.comp (tendsto_add_atTop_nat 1)
  have hlimt : Tendsto t atTop (𝓝 (⨆ n, s n)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hlim hlimnext hst hts
  have hmem : f (⨆ n, s n) ∈ C :=
    hC.mem_of_tendsto ((hf.tendsto _).comp hlim) (Eventually.of_forall hs)
  have hnot : f (⨆ n, s n) ∉ O :=
    hO.isClosed_compl.mem_of_tendsto ((hf.tendsto _).comp hlimt) (Eventually.of_forall ht)
  exact hnot (hCO hmem)

end LatticeProb
