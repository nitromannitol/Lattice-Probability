import LatticeProb.Topology.BoundedVisitEndpointVersions

/-! # Observable endpoint versions from visits before a cutoff -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- Bounded endpoints have observable versions if each rational visit event before
    a cutoff has an observable almost-everywhere representative. -/
theorem exists_observable_endpoints_of_ae_visits_before
    {Ω : Type*} [MeasurableSpace Ω] (obs : MeasurableSpace Ω) (P : Measure Ω)
    (visit : Ω → ℚ → Prop) (a b : Ω → ℝ) (s t c : ℝ) (hst : s ≤ t)
    (hvisit : ∀ q : ℚ, (q : ℝ) < c → ∃ E : Set Ω,
      @MeasurableSet Ω obs E ∧ {ω | visit ω q} =ᵐ[P] E)
    (hgood : ∀ᵐ ω ∂P,
      s ≤ a ω ∧ b ω ≤ t ∧ b ω < c ∧
      (∀ q, visit ω q → a ω ≤ q ∧ (q : ℝ) ≤ b ω) ∧
      (∀ r, a ω < r → ∃ q : ℚ, visit ω q ∧ (q : ℝ) < r) ∧
      (∀ r, r < b ω → ∃ q : ℚ, visit ω q ∧ r < (q : ℝ))) :
    ∃ a' b' : Ω → ℝ, @Measurable Ω ℝ obs _ a' ∧ @Measurable Ω ℝ obs _ b' ∧
      (∀ᵐ ω ∂P, a' ω = a ω ∧ b' ω = b ω) := by
  classical
  have hrep : ∀ q : ℚ, ∃ E : Set Ω, @MeasurableSet Ω obs E ∧
      {ω | visit ω q ∧ (q : ℝ) < c} =ᵐ[P] E := by
    intro q
    by_cases hq : (q : ℝ) < c
    · obtain ⟨E, hE, heq⟩ := hvisit q hq
      exact ⟨E, hE, by simpa only [hq, and_true] using heq⟩
    · refine ⟨∅, @MeasurableSet.empty Ω obs, ?_⟩
      exact Filter.Eventually.of_forall (by intro ω; simp [hq])
  choose E hEm hEq using hrep
  have hEqAll : ∀ᵐ ω ∂P, ∀ q, (visit ω q ∧ (q : ℝ) < c) ↔ ω ∈ E q :=
    ae_all_iff.mpr fun q => by
      filter_upwards [hEq q] with ω hω
      exact iff_of_eq hω
  apply exists_measurable_endpoints_of_bounded_ae_visits obs P (fun ω q => ω ∈ E q)
    a b s t hst hEm
  filter_upwards [hgood, hEqAll] with ω hg he
  have hbefore : ∀ q, visit ω q → (q : ℝ) < c :=
    fun q hq => lt_of_le_of_lt ((hg.2.2.2.1 q hq).2) hg.2.2.1
  refine ⟨hg.1, hg.2.1, ?_, ?_, ?_⟩
  · intro q hq
    exact hg.2.2.2.1 q ((he q).2 hq).1
  · intro r hr
    obtain ⟨q, hq, hqr⟩ := hg.2.2.2.2.1 r hr
    exact ⟨q, (he q).1 ⟨hq, hbefore q hq⟩, hqr⟩
  · intro r hr
    obtain ⟨q, hq, hrq⟩ := hg.2.2.2.2.2 r hr
    exact ⟨q, (he q).1 ⟨hq, hbefore q hq⟩, hrq⟩

end LatticeProb
