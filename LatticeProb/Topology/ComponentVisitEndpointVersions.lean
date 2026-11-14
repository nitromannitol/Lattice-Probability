import LatticeProb.Topology.ComponentVisitEndpoints

/-! # Almost surely measurable endpoints of open curve visits -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- Measurable rational visits determine measurable versions of two endpoints when the
visit bounds and endpoint approximations hold almost everywhere. -/
theorem exists_measurable_endpoints_of_ae_rational_visits
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (visit : Ω → ℚ → Prop) (a b : Ω → ℝ)
    (hvisit : ∀ q, MeasurableSet {ω | visit ω q})
    (hgood : ∀ᵐ ω ∂P,
      (∀ q, visit ω q → a ω ≤ q ∧ (q : ℝ) ≤ b ω) ∧
      (∀ t, a ω < t → ∃ q : ℚ, visit ω q ∧ (q : ℝ) < t) ∧
      (∀ t, t < b ω → ∃ q : ℚ, visit ω q ∧ t < (q : ℝ))) :
    ∃ a' b' : Ω → ℝ, Measurable a' ∧ Measurable b' ∧
      (∀ᵐ ω ∂P, a' ω = a ω ∧ b' ω = b ω) := by
  classical
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  let a' : Ω → ℝ := N.piecewise (fun _ => 0) a
  let b' : Ω → ℝ := N.piecewise (fun _ => 1) b
  let visit' : Ω → ℚ → Prop := fun ω q =>
    (ω ∉ N ∧ visit ω q) ∨ (ω ∈ N ∧ (q : ℝ) ∈ Ioo (0 : ℝ) 1)
  have hmodel := rational_visits_of_open_ae_interval volume (Ioo (0 : ℝ) 1) 0 1
    isOpen_Ioo (by norm_num) (Filter.Eventually.of_forall fun _ => Iff.rfl)
  have hv : ∀ q, MeasurableSet {ω | visit' ω q} := by
    intro q
    change MeasurableSet ((Nᶜ ∩ {ω | visit ω q}) ∪ (N ∩ {ω | (q : ℝ) ∈ Ioo (0 : ℝ) 1}))
    by_cases hq : (q : ℝ) ∈ Ioo (0 : ℝ) 1
    · simpa only [hq, ofPred_true, inter_univ] using
        (hNm.compl.inter (hvisit q)).union hNm
    · simpa only [hq, ofPred_false, inter_empty, union_empty] using
        hNm.compl.inter (hvisit q)
  have hprops : ∀ ω,
      (∀ q, visit' ω q → a' ω ≤ q ∧ (q : ℝ) ≤ b' ω) ∧
      (∀ t, a' ω < t → ∃ q : ℚ, visit' ω q ∧ (q : ℝ) < t) ∧
      (∀ t, t < b' ω → ∃ q : ℚ, visit' ω q ∧ t < (q : ℝ)) := by
    intro ω
    by_cases hω : ω ∈ N
    · simp only [a', b', Set.piecewise_eq_of_mem _ _ _ hω]
      simp only [visit', hω, not_true_eq_false, false_and, true_and, false_or]
      exact hmodel
    · have hg := not_not.mp (fun hn => hω (hNsub hn))
      simp only [a', b', Set.piecewise_eq_of_notMem _ _ _ hω]
      simp only [visit', hω, not_false_eq_true, true_and, false_and, or_false]
      exact hg
  have hm := measurable_endpoints_of_rational_visits visit' a' b' hv
    (fun ω => (hprops ω).1) (fun ω => (hprops ω).2.1) (fun ω => (hprops ω).2.2)
  refine ⟨a', b', hm.1, hm.2, ?_⟩
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω
  simp only [a', b', Set.piecewise_eq_of_notMem _ _ _ hω, and_self]

/-- Almost-sure geometric and visit hypotheses yield measurable versions of the two
endpoints, without requiring their exceptional set to be measurable. -/
theorem exists_measurable_endpoints_of_ae_open_curve_visits
    {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E] [PerfectSpace E]
    (P : Measure Ω) (η : Ω → ℝ → E) (U : Ω → Set E) (a b : Ω → ℝ)
    (hvisit : ∀ q : ℚ, MeasurableSet {ω | η ω q ∈ U ω})
    (hgood : ∀ᵐ ω ∂P, Continuous (η ω) ∧ IsOpen (U ω) ∧ (U ω).Nonempty ∧
      η ω '' Icc (a ω) (b ω) = closure (U ω) ∧
      ∀ᵐ t ∂volume, η ω t ∈ U ω ↔ t ∈ Ioo (a ω) (b ω)) :
    ∃ a' b' : Ω → ℝ, Measurable a' ∧ Measurable b' ∧
      (∀ᵐ ω ∂P, a' ω = a ω ∧ b' ω = b ω) := by
  apply exists_measurable_endpoints_of_ae_rational_visits P (fun ω q => η ω q ∈ U ω) a b hvisit
  filter_upwards [hgood] with ω hω
  exact rational_visits_of_open_ae_interval volume (η ω ⁻¹' U ω) (a ω) (b ω)
    (hω.2.1.preimage hω.1)
    (interval_lt_of_image_eq_closure_open (η ω) (U ω) (a ω) (b ω)
      hω.2.1 hω.2.2.1 hω.2.2.2.1) hω.2.2.2.2

end LatticeProb
