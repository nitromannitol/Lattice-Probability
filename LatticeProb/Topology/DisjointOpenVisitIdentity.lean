import LatticeProb.Topology.ComponentVisitIdentity
import Mathlib.Topology.Bases

/-! # Simultaneous visit times for disjoint open regions -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- For a disjoint family of nonempty open regions, interval visit identities
hold simultaneously at almost every time. Each region's interval-image identity,
frontier nullity, and mass identity are hypotheses. -/
theorem ae_visit_disjoint_open_eq_intervals
    {E : Type*} [TopologicalSpace E] [TopologicalSpace.SeparableSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (η : ℝ → E) (μ : Measure E) (C : Set (Set E)) (a b : Set E → ℝ)
    (hη : Measurable η) (hmap : Measure.map η volume = μ)
    (hdis : C.PairwiseDisjoint id)
    (hopen : ∀ U ∈ C, IsOpen U) (hne : ∀ U ∈ C, U.Nonempty)
    (hfront : ∀ U ∈ C, μ (frontier U) = 0)
    (himage : ∀ U ∈ C, η '' Icc (a U) (b U) = closure U)
    (hmass : ∀ U ∈ C, μ (η '' Icc (a U) (b U)) = volume (Icc (a U) (b U))) :
    ∀ᵐ t ∂volume, ∀ U ∈ C, η t ∈ U ↔ t ∈ Ioo (a U) (b U) := by
  have hcount : C.Countable := hdis.countable_of_isOpen hopen hne
  have : Countable C := hcount.to_subtype
  have hall : ∀ᵐ t ∂volume, ∀ U : C, η t ∈ U.1 ↔ t ∈ Ioo (a U.1) (b U.1) := by
    apply ae_all_iff.mpr
    intro U
    exact ae_visit_open_eq_interval η μ U.1 (a U.1) (b U.1) hη hmap
      (hopen U.1 U.2) (hfront U.1 U.2) (himage U.1 U.2) (hmass U.1 U.2)
  filter_upwards [hall] with t ht U hU
  exact ht ⟨U, hU⟩

end LatticeProb
