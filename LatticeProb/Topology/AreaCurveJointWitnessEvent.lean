import LatticeProb.Prob.AreaCurveLocalFiniteEvent
import LatticeProb.Topology.StrictComponentIntervalWitness
import LatticeProb.Topology.PrescribedComponentWitnessMeasurable

/-! # Measurability of area-curve component witness events -/

set_option autoImplicit false
set_option maxHeartbeats 400000

open Function MeasureTheory Set

namespace LatticeProb

private theorem measurable_anchor {Ω : Type*} [MeasurableSpace Ω]
    (f : Ω → C(ℝ, ℂ)) (hf : Measurable f) (s u t : ℝ) :
    MeasurableSet {ω | f ω u ∈ interior (f ω '' Icc s t)} := by
  obtain ⟨B, hBsub, hBcount, hBbasis⟩ :=
    (TopologicalSpace.IsTopologicalBasis.isOpen_isPreconnected (α := ℂ)).exists_countable
  have : Countable B := hBcount.to_subtype
  have h := measurableSet_curve_mem_interior_image (fun i : B => i.val)
    f (K := Icc s t) isCompact_Icc hf
    (fun i => (hBsub i.property).1)
    (fun V hV z hz => by
      obtain ⟨U, hU, hzU, hUV⟩ := hBbasis.isOpen_iff.mp hV z hz
      exact ⟨⟨U, hU⟩, hzU, hUV⟩)
  exact h.preimage (measurable_id.prodMk measurable_const)

private theorem nullMeasurable_strict_witness {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω → C(ℝ, ℂ))
    (hf : Measurable f) (s u t : ℝ) :
    NullMeasurableSet {ω | ∃ a b : ℝ, s ≤ a ∧ a < b ∧ b ≤ t ∧
      closure (connectedComponentIn (interior (f ω '' Icc s t)) (f ω u)) =
        f ω '' Icc a b} P := by
  let V : Ω → C(ℝ, ℂ) × ℂ := fun ω => (f ω, f ω u)
  have hV : Measurable V := hf.prodMk ((ContinuousMap.measurable_eval u).comp hf)
  have : IsFiniteMeasure (P.map V) := Measure.isFiniteMeasure_map P V
  have hw := (nullMeasurableSet_exists_strict_bounded_component_interval s t
    (P.map V)).preimage (hV.quasiMeasurePreserving P)
  change NullMeasurableSet {ω | ∃ a b : ℝ, s ≤ a ∧ a < b ∧ b ≤ t ∧
      closure (connectedComponentIn (interior (f ω '' Icc s t)) (f ω u)) =
        f ω '' Icc a b} P at hw
  exact hw

/-- Properness, an interior anchor, local finiteness, mass parametrization,
a strict component-interval witness, and a null-measurable condition together
form a null-measurable event. -/
theorem nullMeasurableSet_area_curve_component_witness
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (f : Ω → C(ℝ, ℂ)) (hf : Measurable f)
    (ν : Ω → Measure ℂ) (hν : Measurable ν) (s u t : ℝ)
    (R : Set Ω) (hR : NullMeasurableSet R P) :
    NullMeasurableSet {ω | ω ∈ R ∧ IsProperMap (f ω) ∧ Surjective (f ω) ∧
      f ω u ∈ interior (f ω '' Icc s t) ∧ IsFiniteMeasureOnCompacts (ν ω) ∧
      (∀ a b : ℝ, a ≤ b → ν ω (f ω '' Icc a b) = ENNReal.ofReal (b - a)) ∧
      ∃ a b : ℝ, s ≤ a ∧ a < b ∧ b ≤ t ∧
        closure (connectedComponentIn (interior (f ω '' Icc s t)) (f ω u)) =
          f ω '' Icc a b} P := by
  have hp : MeasurableSet {ω | IsProperMap (f ω) ∧ Surjective (f ω)} :=
    ContinuousMap.measurableSet_isProperMap_and_surjective_curve.preimage hf
  have hi := measurable_anchor f hf s u t
  have ha : MeasurableSet {ω | IsFiniteMeasureOnCompacts (ν ω) ∧
      ∀ a b : ℝ, a ≤ b → ν ω (f ω '' Icc a b) = ENNReal.ofReal (b - a)} :=
    measurableSet_locallyFinite_curve_mass_parametrized hν (fun ω => (f ω).continuous)
      (fun v => (ContinuousMap.measurable_eval v).comp hf)
  have hw := nullMeasurable_strict_witness P f hf s u t
  convert hR.inter (hp.nullMeasurableSet.inter (hi.nullMeasurableSet.inter
    (ha.nullMeasurableSet.inter hw))) using 1
  ext ω
  simp only [mem_ofPred_eq, mem_inter_iff]
  constructor
  · rintro ⟨hR', hp', hs', hi', hf', ha', hw'⟩
    exact ⟨hR', ⟨⟨hp', hs'⟩, hi', ⟨hf', ha'⟩, hw'⟩⟩
  · rintro ⟨hR', ⟨⟨hp', hs'⟩, hi', ⟨hf', ha'⟩, hw'⟩⟩
    exact ⟨hR', hp', hs', hi', hf', ha', hw'⟩

end LatticeProb
