import LatticeProb.Topology.ComponentIntervalMarginalTransfer

/-! # Transfer of prescribed component intervals through a marginal law -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- Prescribed component interval endpoints transfer through a marginal law
when the source and target curves are proper surjections with the same fibres. -/
theorem ae_prescribed_component_interval_of_marginal_fibers
    {X Ω : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace Ω] (μ : Measure (X × C(ℝ, ℂ))) [IsFiniteMeasure μ]
    (P : Measure Ω) (Z : Ω → X) (g : Ω → C(ℝ, ℂ))
    (hZ : Measurable Z) (hlaw : P.map Z = μ.map Prod.fst)
    (R : X → ℝ → ℝ → Prop) (a b : X → ℝ) (s u t : ℝ)
    {A : Set (X × C(ℝ, ℂ))}
    (hA : NullMeasurableSet A μ) (hfull : ∀ᵐ p ∂μ, p ∈ A)
    (hsource : ∀ p ∈ A, IsProperMap p.2 ∧ Function.Surjective p.2 ∧
      (∀ v w, p.2 v = p.2 w ↔ R p.1 v w) ∧
      p.2 u ∈ interior (p.2 '' Icc s t) ∧
      s ≤ a p.1 ∧ a p.1 ≤ b p.1 ∧ b p.1 ≤ t ∧
      p.2 '' Icc (a p.1) (b p.1) =
        closure (connectedComponentIn (interior (p.2 '' Icc s t)) (p.2 u)))
    (htarget : ∀ᵐ ω ∂P, IsProperMap (g ω) ∧ Function.Surjective (g ω) ∧
      ∀ v w, g ω v = g ω w ↔ R (Z ω) v w) :
    ∀ᵐ ω ∂P, s ≤ a (Z ω) ∧ a (Z ω) ≤ b (Z ω) ∧ b (Z ω) ≤ t ∧
      g ω '' Icc (a (Z ω)) (b (Z ω)) =
        closure (connectedComponentIn (interior (g ω '' Icc s t)) (g ω u)) := by
  have : PolishSpace C(ℝ, ℂ) := LQGMetric.polishSpace_continuousMap ℝ ℂ
  filter_upwards [ae_exists_witness_of_marginal_law μ P Z hZ hlaw hA hfull, htarget] with ω hw ht
  obtain ⟨f, hf⟩ := hw
  obtain ⟨hp, hs, hr, hu, ha, hab, hb, hi⟩ := hsource (Z ω, f) hf
  have heq : ∀ v w, f v = f w ↔ g ω v = g ω w := by
    intro v w
    exact (hr v w).trans (ht.2.2 v w).symm
  refine ⟨ha, hab, hb, ?_⟩
  exact image_eq_componentClosure_of_proper_maps_same_fibers f (g ω) hp ht.1 hs ht.2.1
    heq (Icc s t) (Icc (a (Z ω)) (b (Z ω))) u hu hi

end LatticeProb
