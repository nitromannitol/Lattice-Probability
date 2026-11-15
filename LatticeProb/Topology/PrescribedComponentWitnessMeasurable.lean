import LatticeProb.Topology.ComponentIntervalWitness
import LatticeProb.Topology.CurveInteriorFubini
import LatticeProb.Topology.MeasurableProperSurjectiveCurve
import Mathlib.Topology.Connected.LocallyConnected

/-! # Measurable prescribed component witnesses -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- For measurable prescribed endpoints, proper surjectivity, interior anchor
membership, and the bounded component interval witness form a measurable event. -/
theorem measurableSet_prescribed_component_witness
    {X : Type*} [MeasurableSpace X] (a b : X → ℝ)
    (ha : Measurable a) (hb : Measurable b) (s u t : ℝ) :
    MeasurableSet {p : X × C(ℝ, ℂ) |
      IsProperMap p.2 ∧ Function.Surjective p.2 ∧
      p.2 u ∈ interior (p.2 '' Icc s t) ∧
      s ≤ a p.1 ∧ a p.1 ≤ b p.1 ∧ b p.1 ≤ t ∧
      p.2 '' Icc (a p.1) (b p.1) =
        closure (connectedComponentIn (interior (p.2 '' Icc s t)) (p.2 u))} := by
  have hp : MeasurableSet {p : X × C(ℝ, ℂ) |
      IsProperMap p.2 ∧ Function.Surjective p.2} :=
    ContinuousMap.measurableSet_isProperMap_and_surjective_curve.preimage measurable_snd
  obtain ⟨B, hBsub, hBcount, hBbasis⟩ :=
    (TopologicalSpace.IsTopologicalBasis.isOpen_isPreconnected (α := ℂ)).exists_countable
  have : Countable B := hBcount.to_subtype
  have hi : MeasurableSet {p : X × C(ℝ, ℂ) |
      p.2 u ∈ interior (p.2 '' Icc s t)} := by
    have h := measurableSet_curve_mem_interior_image (fun i : B => i.val)
      (fun p : X × C(ℝ, ℂ) => p.2) (K := Icc s t) isCompact_Icc measurable_snd
      (fun i => (hBsub i.property).1)
      (fun V hV z hz => by
        obtain ⟨U, hU, hzU, hUV⟩ := hBbasis.isOpen_iff.mp hV z hz
        exact ⟨⟨U, hU⟩, hzU, hUV⟩)
    exact h.preimage (measurable_id.prodMk measurable_const)
  have hw : MeasurableSet {p : X × C(ℝ, ℂ) |
      s ≤ a p.1 ∧ a p.1 ≤ b p.1 ∧ b p.1 ≤ t ∧
      closure (connectedComponentIn (interior (p.2 '' Icc s t)) (p.2 u)) =
        p.2 '' Icc (a p.1) (b p.1)} := by
    have hm : Measurable (fun p : X × C(ℝ, ℂ) =>
        ((p.2, p.2 u), (a p.1, b p.1))) :=
      (measurable_snd.prodMk ((ContinuousMap.measurable_eval u).comp measurable_snd)).prodMk
        ((ha.comp measurable_fst).prodMk (hb.comp measurable_fst))
    exact (measurableSet_bounded_component_interval s t).preimage hm
  convert hp.inter (hi.inter hw) using 1
  ext p
  simp only [mem_ofPred_eq, mem_inter_iff]
  tauto

end LatticeProb
