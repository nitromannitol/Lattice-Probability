import LatticeProb.Topology.RestrictedComponentVisitCode
import LatticeProb.Topology.BoundedVisitEndpointGeneral

/-! # Component visit endpoints with independent ambient measure -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- An observable version of the rational visit code determines observable endpoint
versions when the open visit set agrees almost everywhere with a bounded interval. -/
theorem exists_observable_endpoints_of_component_visit_code_general
    {Ω E : Type*} [mΩ : MeasurableSpace Ω] [TopologicalSpace E] [LocallyConnectedSpace E]
    (obs : MeasurableSpace Ω) (P : @Measure Ω mΩ) (f : Ω → C(ℝ, E))
    (x : Ω → E) (K : Set ℝ) (code : Ω → ℚ → Bool) (a b : Ω → ℝ)
    (s t : ℝ) (hst : s ≤ t)
    (hcode : @Measurable Ω (ℚ → Bool) obs _ code)
    (heq : ∀ᵐ ω ∂P, code ω = curveComponentVisitCode K (f ω) (x ω))
    (hgood : ∀ᵐ ω ∂P,
      s ≤ a ω ∧ a ω < b ω ∧ b ω ≤ t ∧
      ∀ᵐ r ∂volume, f ω r ∈ connectedComponentIn (interior (f ω '' K)) (x ω) ↔
        r ∈ Ioo (a ω) (b ω)) :
    ∃ a' b' : Ω → ℝ, @Measurable Ω ℝ obs _ a' ∧ @Measurable Ω ℝ obs _ b' ∧
      (∀ᵐ ω ∂P, a' ω = a ω ∧ b' ω = b ω) := by
  classical
  let visit : Ω → ℚ → Prop := fun ω q => code ω q = true
  have hvisit (q : ℚ) : @MeasurableSet Ω obs {ω | visit ω q} := by
    let : MeasurableSpace Ω := obs
    exact ((measurable_pi_apply q).comp hcode) (measurableSet_singleton true)
  apply @exists_measurable_endpoints_of_bounded_ae_visits_general Ω mΩ obs P visit a b s t hst hvisit
  filter_upwards [heq, hgood] with ω he hg
  let U := connectedComponentIn (interior (f ω '' K)) (x ω)
  have hv (q : ℚ) : visit ω q ↔ f ω q ∈ U := by
    simp [visit, he, curveComponentVisitCode, U]
  have hp := rational_visits_of_open_ae_interval volume (f ω ⁻¹' U) (a ω) (b ω)
    (isOpen_interior.connectedComponentIn.preimage (f ω).continuous) hg.2.1 hg.2.2.2
  refine ⟨hg.1, hg.2.2.1, ?_, ?_, ?_⟩
  · intro q hq
    exact hp.1 q ((hv q).mp hq)
  · intro r hr
    obtain ⟨q, hq, hqr⟩ := hp.2.1 r hr
    exact ⟨q, (hv q).mpr hq, hqr⟩
  · intro r hr
    obtain ⟨q, hq, hrq⟩ := hp.2.2 r hr
    exact ⟨q, (hv q).mpr hq, hrq⟩


/-- A binary code of visits at rational times in a fixed closed interval determines
observable versions of bounded component-visit endpoints. -/
theorem exists_observable_endpoints_of_restricted_component_visit_code_general
    {Ω E : Type*} [mΩ : MeasurableSpace Ω] [TopologicalSpace E] [LocallyConnectedSpace E]
    (obs : MeasurableSpace Ω) (P : @Measure Ω mΩ) (f : Ω → C(ℝ, E))
    (x : Ω → E) (K : Set ℝ) (s t : ℝ) (hst : s ≤ t)
    (code : Ω → {q : ℚ // (q : ℝ) ∈ Icc s t} → Bool) (a b : Ω → ℝ)
    (hcode : @Measurable Ω ({q : ℚ // (q : ℝ) ∈ Icc s t} → Bool) obs _ code)
    (heq : ∀ᵐ ω ∂P, ∀ q : {q : ℚ // (q : ℝ) ∈ Icc s t},
      code ω q = curveComponentVisitCode K (f ω) (x ω) q.1)
    (hgood : ∀ᵐ ω ∂P,
      s ≤ a ω ∧ a ω < b ω ∧ b ω ≤ t ∧
      ∀ᵐ r ∂volume, f ω r ∈ connectedComponentIn (interior (f ω '' K)) (x ω) ↔
        r ∈ Ioo (a ω) (b ω)) :
    ∃ a' b' : Ω → ℝ, @Measurable Ω ℝ obs _ a' ∧ @Measurable Ω ℝ obs _ b' ∧
      (∀ᵐ ω ∂P, a' ω = a ω ∧ b' ω = b ω) := by
  classical
  let extended : Ω → ℚ → Bool := fun ω q =>
    if hq : (q : ℝ) ∈ Icc s t then code ω ⟨q, hq⟩ else false
  have hext : @Measurable Ω (ℚ → Bool) obs _ extended := by
    let : MeasurableSpace Ω := obs
    apply measurable_pi_iff.mpr
    intro q
    by_cases hq : (q : ℝ) ∈ Icc s t
    · simpa only [extended, dite_eq_left hq, Function.comp_def] using (measurable_pi_apply ⟨q, hq⟩).comp hcode
    · simpa only [extended, dite_eq_right hq] using (measurable_const : Measurable (fun _ : Ω => false))
  apply @exists_observable_endpoints_of_component_visit_code_general Ω E mΩ inferInstance inferInstance obs P f x K extended a b s t hst hext
    ?_ hgood
  filter_upwards [heq, hgood] with ω he hg
  funext q
  by_cases hq : (q : ℝ) ∈ Icc s t
  · simpa only [extended, dite_eq_left hq] using he ⟨q, hq⟩
  · have hp := rational_visits_of_open_ae_interval volume
      (f ω ⁻¹' connectedComponentIn (interior (f ω '' K)) (x ω)) (a ω) (b ω)
      (isOpen_interior.connectedComponentIn.preimage (f ω).continuous) hg.2.1 hg.2.2.2
    have hn : f ω q ∉ connectedComponentIn (interior (f ω '' K)) (x ω) := by
      intro hv
      have hv' := hp.1 q hv
      exact hq ⟨hg.1.trans hv'.1, hv'.2.trans hg.2.2.1⟩
    simp only [extended, dite_eq_right hq, curveComponentVisitCode, hn, ite_false]


end LatticeProb
