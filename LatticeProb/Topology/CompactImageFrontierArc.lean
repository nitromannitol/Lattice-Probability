import LatticeProb.Topology.CompactImageFrontier
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-! # Arc witnesses in compact-image frontiers -/

set_option autoImplicit false

open Set MeasureTheory Topology

namespace LatticeProb

/-- Containment of a continuous path in a varying compact-image frontier is Borel. -/
theorem measurableSet_path_range_subset_compact_image_frontier
    {Ω K J E ι : Type*} [TopologicalSpace Ω] [SecondCountableTopology Ω]
    [MeasurableSpace Ω] [BorelSpace Ω] [TopologicalSpace K] [CompactSpace K]
    [TopologicalSpace J] [LocallyCompactSpace J] [TopologicalSpace.SeparableSpace J]
    [TopologicalSpace E] [T2Space E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E] [Countable ι]
    (B : ι → Set E) (f : Ω × K → E) (hf : Continuous f)
    (hopen : ∀ i, IsOpen (B i))
    (hbasis : ∀ (V : Set E), IsOpen V → ∀ z ∈ V, ∃ i, z ∈ B i ∧ B i ⊆ V) :
    MeasurableSet {p : Ω × C(J, E) |
      ∀ t, p.2 t ∈ frontier ((fun x : K => f (p.1, x)) '' univ)} := by
  obtain ⟨D, hDc, hD⟩ := TopologicalSpace.exists_countable_dense J
  have heq : {p : Ω × C(J, E) |
      ∀ t, p.2 t ∈ frontier ((fun x : K => f (p.1, x)) '' univ)} =
      ⋂ t ∈ D, {p : Ω × C(J, E) |
        p.2 t ∈ frontier ((fun x : K => f (p.1, x)) '' univ)} := by
    ext p
    simp only [mem_ofPred_eq, mem_iInter]
    constructor
    · intro h t _
      exact h t
    · intro h t
      have hc : IsClosed (p.2 ⁻¹' frontier ((fun x : K => f (p.1, x)) '' univ)) :=
        isClosed_frontier.preimage p.2.continuous
      have hsub : D ⊆ p.2 ⁻¹' frontier ((fun x : K => f (p.1, x)) '' univ) := h
      exact closure_minimal hsub hc (hD t)
  rw [heq]
  refine MeasurableSet.biInter hDc fun t _ => ?_
  exact (measurableSet_mem_frontier_compact_image B f hf hopen hbasis).preimage
    ((continuous_fst.prodMk (by fun_prop)).measurable)

/-- The event that two compact-image frontiers contain a common injective
unit-interval path is analytic. -/
theorem analyticSet_exists_injective_path_in_compact_image_frontiers
    {Ω K ι : Type*} [TopologicalSpace Ω] [PolishSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    [TopologicalSpace K] [CompactSpace K] [Countable ι]
    (B : ι → Set ℂ) (f g : Ω × K → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hopen : ∀ i, IsOpen (B i))
    (hbasis : ∀ (V : Set ℂ), IsOpen V → ∀ z ∈ V, ∃ i, z ∈ B i ∧ B i ⊆ V) :
    AnalyticSet {ω : Ω | ∃ γ : C(Icc (0 : ℝ) 1, ℂ), Function.Injective γ ∧
      (∀ t, γ t ∈ frontier ((fun x : K => f (ω, x)) '' univ)) ∧
      (∀ t, γ t ∈ frontier ((fun x : K => g (ω, x)) '' univ))} := by
  let J := Icc (0 : ℝ) 1
  have : PolishSpace C(J, ℂ) := LQGMetric.polishSpace_continuousMap J ℂ
  let A : Set (Ω × C(J, ℂ)) := {p | Function.Injective p.2 ∧
    (∀ t, p.2 t ∈ frontier ((fun x : K => f (p.1, x)) '' univ)) ∧
    (∀ t, p.2 t ∈ frontier ((fun x : K => g (p.1, x)) '' univ))}
  have hA : MeasurableSet A :=
    (measurableSet_injective_continuousMap.preimage measurable_snd).inter
      ((measurableSet_path_range_subset_compact_image_frontier B f hf hopen hbasis).inter
       (measurableSet_path_range_subset_compact_image_frontier B g hg hopen hbasis))
  have heq : {ω : Ω | ∃ γ : C(Icc (0 : ℝ) 1, ℂ), Function.Injective γ ∧
      (∀ t, γ t ∈ frontier ((fun x : K => f (ω, x)) '' univ)) ∧
      (∀ t, γ t ∈ frontier ((fun x : K => g (ω, x)) '' univ))} = Prod.fst '' A := by
    ext ω
    constructor
    · rintro ⟨γ, hγ⟩
      exact ⟨(ω, γ), hγ, rfl⟩
    · rintro ⟨⟨ω', γ⟩, hγ, rfl⟩
      exact ⟨γ, hγ⟩
  rw [heq]
  exact hA.analyticSet.image_of_continuous continuous_fst

/-- The common-frontier path event is null measurable for every finite Borel measure. -/
theorem nullMeasurableSet_exists_injective_path_in_compact_image_frontiers
    {Ω K ι : Type*} [TopologicalSpace Ω] [PolishSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    [TopologicalSpace K] [CompactSpace K] [Countable ι]
    (B : ι → Set ℂ) (f g : Ω × K → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hopen : ∀ i, IsOpen (B i))
    (hbasis : ∀ (V : Set ℂ), IsOpen V → ∀ z ∈ V, ∃ i, z ∈ B i ∧ B i ⊆ V)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    NullMeasurableSet {ω : Ω | ∃ γ : C(Icc (0 : ℝ) 1, ℂ), Function.Injective γ ∧
      (∀ t, γ t ∈ frontier ((fun x : K => f (ω, x)) '' univ)) ∧
      (∀ t, γ t ∈ frontier ((fun x : K => g (ω, x)) '' univ))} μ :=
  AnalyticSet.nullMeasurableSet μ
    (analyticSet_exists_injective_path_in_compact_image_frontiers B f g hf hg hopen hbasis)

end LatticeProb
