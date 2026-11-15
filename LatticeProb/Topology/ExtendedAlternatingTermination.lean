import LatticeProb.Topology.BoundedAlternatingTimes

/-! # Termination of bounded alternating clocks -/

set_option autoImplicit false

namespace LatticeProb

/-- Ordered entry and exit clocks reach infinity if finite entries are bounded
    and their endpoints alternate between a closed set and the complement of
    an open neighborhood. -/
theorem exists_top_of_bounded_alternating_clocks {E : Type*} [TopologicalSpace E]
    (f : ℝ → E) (hf : Continuous f) {C O : Set E}
    (hC : IsClosed C) (hO : IsOpen O) (hCO : C ⊆ O)
    (s t : ℕ → WithTop ℝ) (b : ℝ)
    (hbound : ∀ n, s n ≠ ⊤ → s n ≤ (b : WithTop ℝ))
    (hst : ∀ n, s n ≤ t n) (hts : ∀ n, t n ≤ s (n + 1))
    (hs : ∀ n, s n ≠ ⊤ → f ((s n).untopD 0) ∈ C)
    (ht : ∀ n, t n ≠ ⊤ → f ((t n).untopD 0) ∉ O) :
    ∃ n, s n = ⊤ := by
  classical
  by_contra h
  have hsfin : ∀ n, s n ≠ ⊤ := by simpa only [not_exists] using h
  have htfin : ∀ n, t n ≠ ⊤ := by
    intro n hn
    apply hsfin (n + 1)
    exact top_le_iff.mp (hn ▸ hts n)
  have coe_untopD_of_ne_top (x : WithTop ℝ) (hx : x ≠ ⊤) :
      ((x.untopD 0 : ℝ) : WithTop ℝ) = x := by
    lift x to ℝ using hx
    rfl
  apply not_bounded_alternating_times f hf hC hO hCO
    (fun n => (s n).untopD 0) (fun n => (t n).untopD 0) b
  · intro n
    have h' := hbound n (hsfin n)
    rw [← coe_untopD_of_ne_top (s n) (hsfin n)] at h'
    exact WithTop.coe_le_coe.mp h'
  · intro n
    have h' := hst n
    rw [← coe_untopD_of_ne_top (s n) (hsfin n),
      ← coe_untopD_of_ne_top (t n) (htfin n)] at h'
    exact WithTop.coe_le_coe.mp h'
  · intro n
    have h' := hts n
    rw [← coe_untopD_of_ne_top (t n) (htfin n),
      ← coe_untopD_of_ne_top (s (n + 1)) (hsfin (n + 1))] at h'
    exact WithTop.coe_le_coe.mp h'
  · exact fun n => hs n (hsfin n)
  · exact fun n => ht n (htfin n)

end LatticeProb
