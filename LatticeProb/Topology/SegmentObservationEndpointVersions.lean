import LatticeProb.Topology.CurveComponentVisitEndpointVersions
import LatticeProb.Topology.BoundedVisitEndpointVersions

/-! # Endpoint localization from a compact curve segment -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- Bounded component visit endpoints admit versions measurable from observations
of a compact segment, even when the almost-everywhere assumptions use another
measurable space. -/
theorem exists_observable_endpoints_of_segment_observations
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (obs : MeasurableSpace Ω) (P : Measure Ω) (B : ι → Set ℂ) (f : Ω → C(ℝ, ℂ)) (x : Ω → ℂ)
    (s t : ℝ) (hst : s ≤ t) (a b : Ω → ℝ)
    (hf : ∀ r ∈ Icc s t, @Measurable Ω ℂ obs _ (fun ω => f ω r))
    (hx : @Measurable Ω ℂ obs _ x)
    (hopen : ∀ i, IsOpen (B i)) (hconn : ∀ i, IsPreconnected (B i))
    (hbasis : ∀ (V : Set ℂ), IsOpen V → ∀ z ∈ V, ∃ i, z ∈ B i ∧ B i ⊆ V)
    (hgood : ∀ᵐ ω ∂P,
      let U := connectedComponentIn (interior (f ω '' Icc s t)) (x ω)
      s ≤ a ω ∧ a ω < b ω ∧ b ω ≤ t ∧
      ∀ᵐ r ∂volume, f ω r ∈ U ↔ r ∈ Ioo (a ω) (b ω)) :
    ∃ a' b' : Ω → ℝ, @Measurable Ω ℝ obs _ a' ∧ @Measurable Ω ℝ obs _ b' ∧
      (∀ᵐ ω ∂P, a' ω = a ω ∧ b' ω = b ω) := by
  let clip : ℝ → ℝ := fun r => min t (max s r)
  have hclip : Continuous clip := continuous_const.min (continuous_const.max continuous_id)
  have hclip_mem (r : ℝ) : clip r ∈ Icc s t := by
    dsimp [clip]
    exact ⟨le_min hst (le_max_left _ _), min_le_left _ _⟩
  have hclip_eq {r : ℝ} (hr : r ∈ Icc s t) : clip r = r := by
    simp [clip, max_eq_right hr.1, min_eq_right hr.2]
  let g : Ω → C(ℝ, ℂ) := fun ω => ⟨fun r => f ω (clip r), (f ω).continuous.comp hclip⟩
  have hg : @Measurable Ω C(ℝ, ℂ) obs _ g := by
    let : MeasurableSpace Ω := obs
    apply ContinuousMap.measurable_iff_eval.2
    intro r
    exact hf (clip r) (hclip_mem r)
  have himage (ω : Ω) : g ω '' Icc s t = f ω '' Icc s t := by
    apply image_congr
    intro r hr
    exact congrArg (f ω) (hclip_eq hr)
  let visit : Ω → ℚ → Prop := fun ω q =>
    (q : ℝ) ∈ Icc s t ∧ f ω q ∈ connectedComponentIn (interior (f ω '' Icc s t)) (x ω)
  have hvisit (q : ℚ) : @MeasurableSet Ω obs {ω | visit ω q} := by
    let : MeasurableSpace Ω := obs
    by_cases hq : (q : ℝ) ∈ Icc s t
    · have hm := measurableSet_mem_connectedComponentIn_interior_image (K := Icc s t) B g x
        (fun ω => f ω q) isCompact_Icc hg hx (hf q hq) hopen hconn hbasis
      simpa only [visit, hq, true_and, himage] using hm
    · simpa only [visit, hq, false_and, ofPred_false] using (MeasurableSet.empty : MeasurableSet (∅ : Set Ω))
  apply exists_measurable_endpoints_of_bounded_ae_visits obs P visit a b s t hst hvisit
  filter_upwards [hgood] with ω hω
  let U := connectedComponentIn (interior (f ω '' Icc s t)) (x ω)
  have hprops := rational_visits_of_open_ae_interval volume (f ω ⁻¹' U) (a ω) (b ω)
    (isOpen_interior.connectedComponentIn.preimage (f ω).continuous) hω.2.1 hω.2.2.2
  have hin (q : ℚ) (hq : f ω q ∈ U) : (q : ℝ) ∈ Icc s t := by
    have hq' := hprops.1 q hq
    exact ⟨hω.1.trans hq'.1, hq'.2.trans hω.2.2.1⟩
  refine ⟨hω.1, hω.2.2.1, ?_, ?_, ?_⟩
  · intro q hq
    exact hprops.1 q hq.2
  · intro r hr
    obtain ⟨q, hq, hqr⟩ := hprops.2.1 r hr
    exact ⟨q, ⟨hin q hq, hq⟩, hqr⟩
  · intro r hr
    obtain ⟨q, hq, hrq⟩ := hprops.2.2 r hr
    exact ⟨q, ⟨hin q hq, hq⟩, hrq⟩

end LatticeProb
