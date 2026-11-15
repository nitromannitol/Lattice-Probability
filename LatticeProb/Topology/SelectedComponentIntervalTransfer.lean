import LatticeProb.Topology.ComponentEndpointSelection
import LatticeProb.Topology.PrescribedComponentWitnessMeasurable
import LatticeProb.Topology.PrescribedComponentIntervalTransfer

/-! # Selection and transfer of component interval endpoints -/

set_option autoImplicit false

open Function MeasureTheory Set

namespace LatticeProb

/-- A measurable choice of strict component interval endpoints for a family of
proper area-parametrized curves also works for proper surjective curves with the
same fibres and the same parameter marginal. -/
theorem exists_measurable_component_endpoints_of_marginal_fibers
    {X Ω : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace Ω] (μ : Measure (X × C(ℝ, ℂ))) [IsFiniteMeasure μ]
    (P : Measure Ω) (Z : Ω → X) (g : Ω → C(ℝ, ℂ))
    (hZ : Measurable Z) (hlaw : P.map Z = μ.map Prod.fst)
    (R : X → ℝ → ℝ → Prop) (s u t : ℝ) {A : Set (X × C(ℝ, ℂ))}
    (hA : NullMeasurableSet A μ) (hfull : ∀ᵐ p ∂μ, p ∈ A)
    (hsource : ∀ p ∈ A, IsProperMap p.2 ∧ Surjective p.2 ∧
      (∀ v w, p.2 v = p.2 w ↔ R p.1 v w) ∧
      p.2 u ∈ interior (p.2 '' Icc s t) ∧
      (∃ ν : Measure ℂ, ∀ v w, v < w →
        ν (p.2 '' Icc v w) = ENNReal.ofReal (w - v)) ∧
      ∃ a b : ℝ, s ≤ a ∧ a < b ∧ b ≤ t ∧
        p.2 '' Icc a b = closure (connectedComponentIn (interior (p.2 '' Icc s t)) (p.2 u)))
    (htarget : ∀ᵐ ω ∂P, IsProperMap (g ω) ∧ Surjective (g ω) ∧
      ∀ v w, g ω v = g ω w ↔ R (Z ω) v w) :
    ∃ F : X → ℝ × ℝ, Measurable F ∧
      (∀ᵐ p ∂μ, s ≤ (F p.1).1 ∧ (F p.1).1 < (F p.1).2 ∧ (F p.1).2 ≤ t ∧
        p.2 '' Icc (F p.1).1 (F p.1).2 =
          closure (connectedComponentIn (interior (p.2 '' Icc s t)) (p.2 u))) ∧
      (∀ᵐ ω ∂P, s ≤ (F (Z ω)).1 ∧ (F (Z ω)).1 < (F (Z ω)).2 ∧
        (F (Z ω)).2 ≤ t ∧ g ω '' Icc (F (Z ω)).1 (F (Z ω)).2 =
          closure (connectedComponentIn (interior (g ω '' Icc s t)) (g ω u))) := by
  have : PolishSpace C(ℝ, ℂ) := LQGMetric.polishSpace_continuousMap ℝ ℂ
  obtain ⟨F, hF, hselect⟩ :=
    exists_measurable_component_endpoints_of_joint_witnesses μ R s u t hA hfull hsource
  let a : X → ℝ := fun x => (F x).1
  let b : X → ℝ := fun x => (F x).2
  have ha : Measurable a := measurable_fst.comp hF
  have hb : Measurable b := measurable_snd.comp hF
  let W : Set (X × C(ℝ, ℂ)) := {p |
    IsProperMap p.2 ∧ Surjective p.2 ∧ p.2 u ∈ interior (p.2 '' Icc s t) ∧
    s ≤ a p.1 ∧ a p.1 ≤ b p.1 ∧ b p.1 ≤ t ∧
    p.2 '' Icc (a p.1) (b p.1) =
      closure (connectedComponentIn (interior (p.2 '' Icc s t)) (p.2 u))}
  let D : Set (X × C(ℝ, ℂ)) := {p | a p.1 < b p.1}
  have hW : MeasurableSet W := measurableSet_prescribed_component_witness a b ha hb s u t
  have hD : MeasurableSet D := measurableSet_lt (ha.comp measurable_fst) (hb.comp measurable_fst)
  have hgood : ∀ᵐ p ∂μ, p ∈ A ∩ (W ∩ D) := by
    filter_upwards [hfull, hselect] with p hp hs
    obtain ⟨hproper, hsurj, _, hinterior, _⟩ := hsource p hp
    exact ⟨hp, ⟨⟨hproper, hsurj, hinterior, hs.1, le_of_lt hs.2.1, hs.2.2⟩, hs.2.1⟩⟩
  have hwitness := ae_exists_witness_of_marginal_law μ P Z hZ hlaw
    (hA.inter (hW.inter hD).nullMeasurableSet) hgood
  refine ⟨F, hF, hselect, ?_⟩
  filter_upwards [hwitness, htarget] with ω hw ht
  obtain ⟨f, hf⟩ := hw
  obtain ⟨hproper, hsurj, hr, hinterior, _⟩ := hsource (Z ω, f) hf.1
  have heq : ∀ v w, f v = f w ↔ g ω v = g ω w :=
    fun v w => (hr v w).trans (ht.2.2 v w).symm
  refine ⟨hf.2.1.2.2.2.1, hf.2.2, hf.2.1.2.2.2.2.2.1, ?_⟩
  exact image_eq_componentClosure_of_proper_maps_same_fibers f (g ω) hproper ht.1 hsurj ht.2.1
    heq (Icc s t) (Icc (a (Z ω)) (b (Z ω))) u hinterior hf.2.1.2.2.2.2.2.2

end LatticeProb
