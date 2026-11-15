import LatticeProb.Topology.PrescribedComponentIntervalTransfer
import LatticeProb.Topology.PrescribedComponentWitnessMeasurable

/-! # Transfer of measurable prescribed component witnesses -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- Prescribed measurable component endpoints transfer between proper surjective
curves with common fibres and the same parameter marginal. -/
theorem ae_prescribed_component_interval_of_ae_marginal_fibers
    {X Ω : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace Ω] (μ : Measure (X × C(ℝ, ℂ))) [IsFiniteMeasure μ]
    (P : Measure Ω) (Z : Ω → X) (g : Ω → C(ℝ, ℂ))
    (hZ : Measurable Z) (hlaw : P.map Z = μ.map Prod.fst)
    (R : X → ℝ → ℝ → Prop) (a b : X → ℝ) (ha : Measurable a) (hb : Measurable b)
    (s u t : ℝ)
    (hR : NullMeasurableSet {p : X × C(ℝ, ℂ) |
      ∀ v w, p.2 v = p.2 w ↔ R p.1 v w} μ)
    (hsourceR : ∀ᵐ p ∂μ, ∀ v w, p.2 v = p.2 w ↔ R p.1 v w)
    (hsource : ∀ᵐ p ∂μ, IsProperMap p.2 ∧ Function.Surjective p.2 ∧
      p.2 u ∈ interior (p.2 '' Icc s t) ∧
      s ≤ a p.1 ∧ a p.1 ≤ b p.1 ∧ b p.1 ≤ t ∧
      p.2 '' Icc (a p.1) (b p.1) =
        closure (connectedComponentIn (interior (p.2 '' Icc s t)) (p.2 u)))
    (htarget : ∀ᵐ ω ∂P, IsProperMap (g ω) ∧ Function.Surjective (g ω) ∧
      ∀ v w, g ω v = g ω w ↔ R (Z ω) v w) :
    ∀ᵐ ω ∂P, s ≤ a (Z ω) ∧ a (Z ω) ≤ b (Z ω) ∧ b (Z ω) ≤ t ∧
      g ω '' Icc (a (Z ω)) (b (Z ω)) =
        closure (connectedComponentIn (interior (g ω '' Icc s t)) (g ω u)) := by
  let W : Set (X × C(ℝ, ℂ)) := {p |
    IsProperMap p.2 ∧ Function.Surjective p.2 ∧
    p.2 u ∈ interior (p.2 '' Icc s t) ∧
    s ≤ a p.1 ∧ a p.1 ≤ b p.1 ∧ b p.1 ≤ t ∧
    p.2 '' Icc (a p.1) (b p.1) =
      closure (connectedComponentIn (interior (p.2 '' Icc s t)) (p.2 u))}
  let F : Set (X × C(ℝ, ℂ)) := {p | ∀ v w, p.2 v = p.2 w ↔ R p.1 v w}
  have hW : NullMeasurableSet W μ :=
    (measurableSet_prescribed_component_witness a b ha hb s u t).nullMeasurableSet
  apply ae_prescribed_component_interval_of_marginal_fibers μ P Z g hZ hlaw R a b s u t
    (A := W ∩ F) (hW.inter hR)
  · filter_upwards [hsource, hsourceR] with p hw hr
    exact ⟨hw, hr⟩
  · intro p hp
    exact ⟨hp.1.1, hp.1.2.1, hp.2, hp.1.2.2⟩
  · exact htarget

end LatticeProb
