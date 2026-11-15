import LatticeProb.Topology.CurveComponentVisitEndpointVersions
import LatticeProb.Topology.BoundedVisitEndpointVersions

/-! # Rational visit codes for curve components -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- The rational times at which a curve visits a selected component of the interior
of its compact image, represented as a binary sequence indexed by the rationals. -/
noncomputable def curveComponentVisitCode {E : Type*} [TopologicalSpace E]
    (K : Set ℝ) (f : C(ℝ, E)) (x : E) : ℚ → Bool := by
  classical
  exact fun q => if f q ∈ connectedComponentIn (interior (f '' K)) x then true else false

/-- The rational visit code is measurable as a countable product of binary coordinates. -/
theorem measurable_curveComponentVisitCode
    {Ω E ι : Type*} [MeasurableSpace Ω] [TopologicalSpace E] [T2Space E]
    [TopologicalSpace.SeparableSpace E] [MeasurableSpace E] [BorelSpace E] [Countable ι]
    (B : ι → Set E) (f : Ω → C(ℝ, E)) (x : Ω → E) {K : Set ℝ}
    (hK : IsCompact K) (hf : Measurable f) (hx : Measurable x)
    (hopen : ∀ i, IsOpen (B i)) (hconn : ∀ i, IsPreconnected (B i))
    (hbasis : ∀ (V : Set E), IsOpen V → ∀ z ∈ V, ∃ i, z ∈ B i ∧ B i ⊆ V) :
    Measurable (fun ω => curveComponentVisitCode K (f ω) (x ω)) := by
  classical
  apply measurable_pi_iff.mpr
  intro q
  have hq := measurableSet_curve_mem_component_interior_image B f x hK hf hx q
    hopen hconn hbasis
  simpa only [curveComponentVisitCode] using
    (Measurable.ite hq (measurable_const : Measurable (fun _ : Ω => true))
      (measurable_const : Measurable (fun _ : Ω => false)))

/-- An observable version of the rational visit code determines observable endpoint
versions when the open visit set agrees almost everywhere with a bounded interval. -/
theorem exists_observable_endpoints_of_component_visit_code
    {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E] [LocallyConnectedSpace E]
    (obs : MeasurableSpace Ω) (P : Measure Ω) (f : Ω → C(ℝ, E))
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
  apply exists_measurable_endpoints_of_bounded_ae_visits obs P visit a b s t hst hvisit
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

end LatticeProb
