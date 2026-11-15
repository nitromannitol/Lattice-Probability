import LatticeProb.Topology.CompactImagesArcWitness

/-! # Boundaries of continuously varying compact images -/

set_option autoImplicit false

open Set MeasureTheory Topology

namespace LatticeProb

/-- Joint membership in a continuously varying compact image is closed. -/
theorem isClosed_mem_compact_image
    {Ω K E : Type*} [TopologicalSpace Ω] [TopologicalSpace K] [CompactSpace K]
    [TopologicalSpace E] [T2Space E]
    (f : Ω × K → E) (hf : Continuous f) :
    IsClosed {p : Ω × E | p.2 ∈ (fun x : K => f (p.1, x)) '' univ} := by
  let A : Set ((Ω × E) × K) := {q | q.1.2 = f (q.1.1, q.2)}
  have hA : IsClosed A := isClosed_eq (by fun_prop) (hf.comp (by fun_prop))
  have heq : {p : Ω × E | p.2 ∈ (fun x : K => f (p.1, x)) '' univ} =
      Prod.fst '' A := by
    ext p
    constructor
    · rintro ⟨x, _, hx⟩
      exact ⟨(p, x), hx.symm, rfl⟩
    · rintro ⟨⟨p', x⟩, hx, rfl⟩
      exact ⟨x, mem_univ _, hx.symm⟩
  rw [heq]
  exact isClosedMap_fst_of_compactSpace _ hA

/-- For an open set, coverage by a continuously varying compact image is Borel. -/
theorem measurableSet_open_subset_compact_image
    {Ω K E : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    [TopologicalSpace K] [CompactSpace K] [TopologicalSpace E] [T2Space E]
    [TopologicalSpace.SeparableSpace E] (f : Ω × K → E) (hf : Continuous f)
    {U : Set E} (hU : IsOpen U) :
    MeasurableSet {ω : Ω | U ⊆ (fun x : K => f (ω, x)) '' univ} := by
  obtain ⟨D, hDc, hD⟩ := TopologicalSpace.exists_countable_dense E
  have hset : {ω : Ω | U ⊆ (fun x : K => f (ω, x)) '' univ} =
      ⋂ z ∈ U ∩ D, {ω : Ω | z ∈ (fun x : K => f (ω, x)) '' univ} := by
    ext ω
    simp only [mem_iInter, mem_ofPred_eq]
    constructor
    · intro h z hz
      exact h hz.1
    · intro h
      exact (hD.open_subset_closure_inter hU).trans
        (closure_minimal (fun z hz => h z hz)
          (isCompact_univ.image (hf.comp (by fun_prop))).isClosed)
  rw [hset]
  refine MeasurableSet.biInter (hDc.mono inter_subset_right) fun z _ => ?_
  exact ((isClosed_mem_compact_image f hf).preimage
    (continuous_id.prodMk continuous_const)).measurableSet

/-- Joint membership in the interior of a continuously varying compact image is Borel. -/
theorem measurableSet_mem_interior_compact_image
    {Ω K E ι : Type*} [TopologicalSpace Ω] [SecondCountableTopology Ω]
    [MeasurableSpace Ω] [BorelSpace Ω] [TopologicalSpace K] [CompactSpace K]
    [TopologicalSpace E] [T2Space E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E] [Countable ι]
    (B : ι → Set E) (f : Ω × K → E) (hf : Continuous f)
    (hopen : ∀ i, IsOpen (B i))
    (hbasis : ∀ (V : Set E), IsOpen V → ∀ z ∈ V, ∃ i, z ∈ B i ∧ B i ⊆ V) :
    MeasurableSet {p : Ω × E | p.2 ∈ interior ((fun x : K => f (p.1, x)) '' univ)} := by
  have heq : {p : Ω × E | p.2 ∈ interior ((fun x : K => f (p.1, x)) '' univ)} =
      ⋃ i, ({p : Ω × E | p.2 ∈ B i} ∩
        {p | B i ⊆ (fun x : K => f (p.1, x)) '' univ}) := by
    ext p
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    constructor
    · intro hp
      obtain ⟨i, hi, hisub⟩ := hbasis _ isOpen_interior _ hp
      exact ⟨i, hi, hisub.trans interior_subset⟩
    · rintro ⟨i, hi, hisub⟩
      exact interior_maximal hisub (hopen i) hi
  rw [heq]
  exact MeasurableSet.iUnion fun i =>
    ((hopen i).measurableSet.preimage measurable_snd).inter
      ((measurableSet_open_subset_compact_image f hf (hopen i)).preimage measurable_fst)

/-- Joint membership in the frontier of a continuously varying compact image is Borel. -/
theorem measurableSet_mem_frontier_compact_image
    {Ω K E ι : Type*} [TopologicalSpace Ω] [SecondCountableTopology Ω]
    [MeasurableSpace Ω] [BorelSpace Ω] [TopologicalSpace K] [CompactSpace K]
    [TopologicalSpace E] [T2Space E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E] [Countable ι]
    (B : ι → Set E) (f : Ω × K → E) (hf : Continuous f)
    (hopen : ∀ i, IsOpen (B i))
    (hbasis : ∀ (V : Set E), IsOpen V → ∀ z ∈ V, ∃ i, z ∈ B i ∧ B i ⊆ V) :
    MeasurableSet {p : Ω × E | p.2 ∈ frontier ((fun x : K => f (p.1, x)) '' univ)} := by
  have heq : {p : Ω × E | p.2 ∈ frontier ((fun x : K => f (p.1, x)) '' univ)} =
      {p : Ω × E | p.2 ∈ (fun x : K => f (p.1, x)) '' univ} \ 
      {p : Ω × E | p.2 ∈ interior ((fun x : K => f (p.1, x)) '' univ)} := by
    apply Set.ext
    intro p
    change p.2 ∈ frontier ((fun x : K => f (p.1, x)) '' univ) ↔
      p.2 ∈ (fun x : K => f (p.1, x)) '' univ ∧
      p.2 ∉ interior ((fun x : K => f (p.1, x)) '' univ)
    have hc : Continuous (fun x : K => f (p.1, x)) :=
      hf.comp (continuous_const.prodMk continuous_id)
    rw [frontier, (isCompact_univ.image hc).isClosed.closure_eq]
    rfl
  rw [heq]
  exact (isClosed_mem_compact_image f hf).measurableSet.diff
    (measurableSet_mem_interior_compact_image B f hf hopen hbasis)

end LatticeProb
