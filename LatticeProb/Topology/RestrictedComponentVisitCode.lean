import LatticeProb.Topology.CurveComponentVisitCode

/-! # Endpoint versions from restricted component visit codes -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- A binary code of visits at rational times in a fixed closed interval determines
observable versions of bounded component-visit endpoints. -/
theorem exists_observable_endpoints_of_restricted_component_visit_code
    {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E] [LocallyConnectedSpace E]
    (obs : MeasurableSpace Ω) (P : Measure Ω) (f : Ω → C(ℝ, E))
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
  apply exists_observable_endpoints_of_component_visit_code obs P f x K extended a b s t hst hext
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
