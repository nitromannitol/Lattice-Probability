import LatticeProb.Topology.CompactImageFrontierArc
import LatticeProb.Topology.MovingIntervalCurve

/-! # Common frontier arcs of curve segments -/

set_option autoImplicit false

open Set MeasureTheory
open scoped unitInterval

namespace LatticeProb

/-- The event that two varying curve segments have a common injective frontier path
is analytic, for arbitrary endpoint order and coincident endpoints. -/
theorem analyticSet_exists_injective_path_in_curve_segment_frontiers
    {Ω ι : Type*} [TopologicalSpace Ω] [PolishSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    [Countable ι] (B : ι → Set ℂ) (η : Ω → C(ℝ, ℂ)) (a b c d : Ω → ℝ)
    (hη : Continuous η) (ha : Continuous a) (hb : Continuous b)
    (hc : Continuous c) (hd : Continuous d)
    (hopen : ∀ i, IsOpen (B i))
    (hbasis : ∀ (V : Set ℂ), IsOpen V → ∀ z ∈ V, ∃ i, z ∈ B i ∧ B i ⊆ V) :
    AnalyticSet {ω : Ω | ∃ γ : C(unitInterval, ℂ), Function.Injective γ ∧
      (∀ t, γ t ∈ frontier (η ω '' uIcc (a ω) (b ω))) ∧
      (∀ t, γ t ∈ frontier (η ω '' uIcc (c ω) (d ω)))} := by
  let F : Ω × unitInterval → ℂ := fun p => movingIntervalCurve (η p.1) (a p.1) (b p.1) p.2
  let G : Ω × unitInterval → ℂ := fun p => movingIntervalCurve (η p.1) (c p.1) (d p.1) p.2
  have hF : Continuous F := by
    have h : Continuous (fun ω => movingIntervalCurve (η ω) (a ω) (b ω)) :=
      continuous_movingIntervalCurve.comp (hη.prodMk (ha.prodMk hb))
    exact continuous_eval.comp ((h.comp continuous_fst).prodMk continuous_snd)
  have hG : Continuous G := by
    have h : Continuous (fun ω => movingIntervalCurve (η ω) (c ω) (d ω)) :=
      continuous_movingIntervalCurve.comp (hη.prodMk (hc.prodMk hd))
    exact continuous_eval.comp ((h.comp continuous_fst).prodMk continuous_snd)
  have h := analyticSet_exists_injective_path_in_compact_image_frontiers B F G hF hG hopen hbasis
  simpa only [F, G, image_univ, range_movingIntervalCurve] using h

/-- The common-frontier path event is null measurable under every finite Borel law. -/
theorem nullMeasurableSet_exists_injective_path_in_curve_segment_frontiers
    {Ω ι : Type*} [TopologicalSpace Ω] [PolishSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    [Countable ι] (B : ι → Set ℂ) (η : Ω → C(ℝ, ℂ)) (a b c d : Ω → ℝ)
    (hη : Continuous η) (ha : Continuous a) (hb : Continuous b)
    (hc : Continuous c) (hd : Continuous d)
    (hopen : ∀ i, IsOpen (B i))
    (hbasis : ∀ (V : Set ℂ), IsOpen V → ∀ z ∈ V, ∃ i, z ∈ B i ∧ B i ⊆ V)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    NullMeasurableSet {ω : Ω | ∃ γ : C(unitInterval, ℂ), Function.Injective γ ∧
      (∀ t, γ t ∈ frontier (η ω '' uIcc (a ω) (b ω))) ∧
      (∀ t, γ t ∈ frontier (η ω '' uIcc (c ω) (d ω)))} μ :=
  AnalyticSet.nullMeasurableSet μ
    (analyticSet_exists_injective_path_in_curve_segment_frontiers B η a b c d
      hη ha hb hc hd hopen hbasis)

end LatticeProb
