import LatticeProb.Topology.CurveSegmentFrontierArc
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

/-! # Shared frontier arcs of random curve segments -/

set_option autoImplicit false

open Set MeasureTheory
open scoped unitInterval

namespace LatticeProb

private abbrev CurveParameters := C(ℝ, ℂ) × (ℝ × (ℝ × (ℝ × ℝ)))

private theorem analyticSet_curveParameters_frontier_arc
    {ι : Type*} [Countable ι] (B : ι → Set ℂ)
    (hopen : ∀ i, IsOpen (B i))
    (hbasis : ∀ (V : Set ℂ), IsOpen V → ∀ z ∈ V, ∃ i, z ∈ B i ∧ B i ⊆ V) :
    AnalyticSet {p : CurveParameters | ∃ γ : C(unitInterval, ℂ), Function.Injective γ ∧
      (∀ t, γ t ∈ frontier (p.1 '' uIcc p.2.1 p.2.2.1)) ∧
      (∀ t, γ t ∈ frontier (p.1 '' uIcc p.2.2.2.1 p.2.2.2.2))} := by
  apply analyticSet_exists_injective_path_in_curve_segment_frontiers B
    Prod.fst (fun p : CurveParameters => p.2.1) (fun p : CurveParameters => p.2.2.1)
    (fun p : CurveParameters => p.2.2.2.1) (fun p : CurveParameters => p.2.2.2.2)
  · exact continuous_fst
  · exact continuous_fst.comp continuous_snd
  · exact continuous_fst.comp (continuous_snd.comp continuous_snd)
  · exact continuous_fst.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))
  · exact continuous_snd.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))
  · exact hopen
  · exact hbasis

private theorem nullMeasurableSet_preimage_analytic
    {Ω α : Type*} [MeasurableSpace Ω] [TopologicalSpace α] [PolishSpace α]
    [MeasurableSpace α] [BorelSpace α] (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : Ω → α) (hf : Measurable f) (s : Set α) (hs : AnalyticSet s) :
    NullMeasurableSet (f ⁻¹' s) μ := by
  let : IsFiniteMeasure (μ.map f) := μ.isFiniteMeasure_map f
  exact (AnalyticSet.nullMeasurableSet (μ.map f) hs).preimage (hf.quasiMeasurePreserving μ)

/-- For a measurable random curve and measurable, possibly dependent endpoints, the
existence of a common injective frontier path is null measurable for any finite law. -/
theorem nullMeasurableSet_exists_injective_path_in_random_curve_segment_frontiers
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] (B : ι → Set ℂ)
    (η : Ω → C(ℝ, ℂ)) (a b c d : Ω → ℝ)
    (hη : Measurable η) (ha : Measurable a) (hb : Measurable b)
    (hc : Measurable c) (hd : Measurable d)
    (hopen : ∀ i, IsOpen (B i))
    (hbasis : ∀ (V : Set ℂ), IsOpen V → ∀ z ∈ V, ∃ i, z ∈ B i ∧ B i ⊆ V)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    NullMeasurableSet {ω : Ω | ∃ γ : C(unitInterval, ℂ), Function.Injective γ ∧
      (∀ t, γ t ∈ frontier (η ω '' uIcc (a ω) (b ω))) ∧
      (∀ t, γ t ∈ frontier (η ω '' uIcc (c ω) (d ω)))} μ := by
  let f : Ω → CurveParameters := fun ω => (η ω, a ω, b ω, c ω, d ω)
  have hf : Measurable f := hη.prodMk (ha.prodMk (hb.prodMk (hc.prodMk hd)))
  exact nullMeasurableSet_preimage_analytic μ f hf _
    (analyticSet_curveParameters_frontier_arc B hopen hbasis)

end LatticeProb
