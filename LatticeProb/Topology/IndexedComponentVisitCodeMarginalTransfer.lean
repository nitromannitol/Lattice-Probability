import LatticeProb.Prob.AnalyticWitnessTransfer
import LatticeProb.Topology.ProperFiberComponentTransfer
import LatticeProb.Topology.CurveComponentVisitCodeHomeomorph

/-! # Transfer of indexed component visit codes through a marginal law -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- An indexed source decoder for component visits transfers to a proper surjective
curve with the same parameter marginal and the same parameter-dependent fibres. -/
theorem ae_indexed_component_visit_code_of_marginal_fibers
    {X Ω I : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace Ω] (μ : Measure (X × C(ℝ, ℂ))) [IsFiniteMeasure μ]
    (P : Measure Ω) (Z : Ω → X) (g : Ω → C(ℝ, ℂ))
    (hZ : Measurable Z) (hlaw : P.map Z = μ.map Prod.fst)
    (R : X → ℝ → ℝ → Prop) (r : I → ℚ) (d : X → I → Bool) (K : Set ℝ) (u : ℝ)
    {A : Set (X × C(ℝ, ℂ))}
    (hA : NullMeasurableSet A μ) (hfull : ∀ᵐ p ∂μ, p ∈ A)
    (hsource : ∀ p ∈ A, IsProperMap p.2 ∧ Function.Surjective p.2 ∧
      (∀ v w, p.2 v = p.2 w ↔ R p.1 v w) ∧
      (∀ i, curveComponentVisitCode K p.2 (p.2 u) (r i) = d p.1 i))
    (htarget : ∀ᵐ ω ∂P, IsProperMap (g ω) ∧ Function.Surjective (g ω) ∧
      ∀ v w, g ω v = g ω w ↔ R (Z ω) v w) :
    ∀ᵐ ω ∂P, ∀ i, curveComponentVisitCode K (g ω) (g ω u) (r i) = d (Z ω) i := by
  have : PolishSpace C(ℝ, ℂ) := LQGMetric.polishSpace_continuousMap ℝ ℂ
  filter_upwards [ae_exists_witness_of_marginal_law μ P Z hZ hlaw hA hfull, htarget] with ω hw ht
  obtain ⟨f, hf⟩ := hw
  obtain ⟨hp, hs, hr, hd⟩ := hsource (Z ω, f) hf
  have heq : ∀ v w, f v = f w ↔ g ω v = g ω w := by
    intro v w
    exact (hr v w).trans (ht.2.2 v w).symm
  obtain ⟨e, he, _⟩ := exists_homeomorph_of_proper_maps_same_fibers_components
    f (g ω) hp ht.1 hs ht.2.1 heq
  have hefun : (⟨e, e.continuous⟩ : C(ℂ, ℂ)).comp f = g ω := by
    ext v
    exact he v
  have hc := curveComponentVisitCode_comp_homeomorph e f (f u) K
  rw [hefun, he u] at hc
  intro i
  exact (congrFun hc (r i)).trans (hd i)

end LatticeProb
