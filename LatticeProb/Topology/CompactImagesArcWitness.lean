import LatticeProb.Topology.InjectiveCurveMeasurable
import LatticeProb.Prob.AnalyticUniversalMeasurable
import LatticeProb.Bonanno.LQGMetric.Prob.PolishContinuousMap

/-! # Arc witnesses in compact images -/

set_option autoImplicit false

open Set MeasureTheory Topology

namespace LatticeProb

/-- Containment of a continuous path in a continuously varying compact image is closed. -/
theorem isClosed_path_range_subset_compact_image
    {Ω K J E : Type} [TopologicalSpace Ω] [TopologicalSpace K] [CompactSpace K]
    [TopologicalSpace J] [LocallyCompactSpace J] [MetricSpace E]
    (f : Ω × K → E) (hf : Continuous f) :
    IsClosed {p : Ω × C(J, E) | ∀ t : J, ∃ x : K, p.2 t = f (p.1, x)} := by
  have h (t : J) : IsClosed {p : Ω × C(J, E) | ∃ x : K, p.2 t = f (p.1, x)} := by
    let A : Set ((Ω × C(J, E)) × K) :=
      {q | q.1.2 t = f (q.1.1, q.2)}
    have hA : IsClosed A := by
      apply isClosed_eq
      · fun_prop
      · exact hf.comp (by fun_prop)
    have heq : {p : Ω × C(J, E) | ∃ x : K, p.2 t = f (p.1, x)} = Prod.fst '' A := by
      ext p
      constructor
      · rintro ⟨x, hx⟩
        exact ⟨(p, x), hx, rfl⟩
      · rintro ⟨⟨p', x⟩, hx, rfl⟩
        exact ⟨x, hx⟩
    rw [heq]
    exact isClosedMap_fst_of_compactSpace _ hA
  convert isClosed_iInter h using 1
  ext p
  simp only [mem_ofPred_eq, mem_iInter]

/-- The event that two compact images contain a common injectively parametrized
unit-interval path is analytic. -/
theorem analyticSet_exists_injective_path_in_compact_images
    {Ω K : Type} [TopologicalSpace Ω] [PolishSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    [TopologicalSpace K] [CompactSpace K]
    (f g : Ω × K → ℂ) (hf : Continuous f) (hg : Continuous g) :
    AnalyticSet {ω : Ω | ∃ γ : C(Icc (0 : ℝ) 1, ℂ), Function.Injective γ ∧
      (∀ t, ∃ x : K, γ t = f (ω, x)) ∧
      (∀ t, ∃ x : K, γ t = g (ω, x))} := by
  let J := Icc (0 : ℝ) 1
  have : PolishSpace C(J, ℂ) := LQGMetric.polishSpace_continuousMap J ℂ
  let A : Set (Ω × C(J, ℂ)) := {p | Function.Injective p.2 ∧
    (∀ t, ∃ x : K, p.2 t = f (p.1, x)) ∧
    (∀ t, ∃ x : K, p.2 t = g (p.1, x))}
  have hA : MeasurableSet A := by
    exact (measurableSet_injective_continuousMap.preimage measurable_snd).inter
      ((isClosed_path_range_subset_compact_image f hf).measurableSet.inter
       (isClosed_path_range_subset_compact_image g hg).measurableSet)
  have heq : {ω : Ω | ∃ γ : C(Icc (0 : ℝ) 1, ℂ), Function.Injective γ ∧
      (∀ t, ∃ x : K, γ t = f (ω, x)) ∧
      (∀ t, ∃ x : K, γ t = g (ω, x))} = Prod.fst '' A := by
    ext ω
    constructor
    · rintro ⟨γ, hγ⟩
      exact ⟨(ω, γ), hγ, rfl⟩
    · rintro ⟨⟨ω', γ⟩, hγ, rfl⟩
      exact ⟨γ, hγ⟩
  rw [heq]
  exact hA.analyticSet.image_of_continuous continuous_fst

/-- The common-path event is null measurable for every finite Borel measure. -/
theorem nullMeasurableSet_exists_injective_path_in_compact_images
    {Ω K : Type} [TopologicalSpace Ω] [PolishSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    [TopologicalSpace K] [CompactSpace K]
    (f g : Ω × K → ℂ) (hf : Continuous f) (hg : Continuous g)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    NullMeasurableSet {ω : Ω | ∃ γ : C(Icc (0 : ℝ) 1, ℂ), Function.Injective γ ∧
      (∀ t, ∃ x : K, γ t = f (ω, x)) ∧
      (∀ t, ∃ x : K, γ t = g (ω, x))} μ :=
  AnalyticSet.nullMeasurableSet μ (analyticSet_exists_injective_path_in_compact_images f g hf hg)

end LatticeProb
