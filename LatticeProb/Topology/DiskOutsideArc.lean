/-
# Injective outside completions of disk paths

Finite loop pruning turns an outside polygonal completion into an injective
finite segment path with the same original circle endpoints. Its trace meets
any disk path between these endpoints exactly at the endpoints. If a second
disk path is disjoint from the first, it also avoids the outside completion.
-/
import LatticeProb.Topology.DiskOutsideCompletion
import LatticeProb.Topology.PolygonalArc



open Set

namespace LatticeProb.Topology

/-- An injective path has distinct endpoints, since zero and one are distinct
parameters of the unit interval. -/
theorem path_source_ne_target_of_injective {X : Type*} [TopologicalSpace X]
    {a b : X} {p : Path a b} (hp : Function.Injective p) : a ≠ b := by
  intro hab
  have hparam : (0 : unitInterval) = 1 := hp (p.source.trans (hab.trans p.target.symm))
  have hreal : (0 : ℝ) = 1 := congrArg Subtype.val hparam
  exact zero_ne_one hreal

/-- **Injective outside completion.** Distinct original unit-circle endpoints
have an injective finite polygonal path meeting the closed coordinate disk
exactly at those endpoints, with all other trace points strictly outside. -/
theorem exists_injective_polygonal_outside_completion (θ φ : ℝ)
    (hne : ((Real.cos θ, Real.sin θ) : ℝ × ℝ) ≠ (Real.cos φ, Real.sin φ)) :
    ∃ us : List (ℝ × ℝ), ∃ hu : us ≠ [], IsSimplePolygonalChain us ∧
      us.head hu = (Real.cos θ, Real.sin θ) ∧
      us.getLast hu = (Real.cos φ, Real.sin φ) ∧
      ∃ q : Path (Real.cos θ, Real.sin θ) (Real.cos φ, Real.sin φ),
        Function.Injective q ∧ range q = polygonalChain us ∧
        range q \ {(Real.cos θ, Real.sin θ), (Real.cos φ, Real.sin φ)} ⊆
          {z | 1 < z.1 ^ 2 + z.2 ^ 2} ∧
        range q ∩ {z | z.1 ^ 2 + z.2 ^ 2 ≤ 1} =
          {(Real.cos θ, Real.sin θ), (Real.cos φ, Real.sin φ)} := by
  obtain ⟨vs, hv, hvhead, hvlast, hvout, hvD⟩ := exists_polygonal_outside_completion θ φ
  have hvne : vs.head hv ≠ vs.getLast hv := by
    rw [hvhead, hvlast]
    exact hne
  obtain ⟨us, hu, hs, hhead, hlast, hsub, hinj, hrange⟩ :=
    exists_injective_polygonal_arc vs hv hvne
  have huhead := hhead.trans hvhead
  have hulast := hlast.trans hvlast
  let q := (polygonalChainPath us hu).cast huhead.symm hulast.symm
  have hqrange : range q = polygonalChain us := hrange
  have hqsub : range q ⊆ polygonalChain vs := hqrange ▸ hsub
  refine ⟨us, hu, hs, huhead, hulast, q, hinj, hqrange,
    fun _ hz => hvout ⟨hqsub hz.1, hz.2⟩, subset_antisymm ?_ ?_⟩
  · intro z hz
    rw [← hvD]
    exact ⟨hqsub hz.1, hz.2⟩
  · intro z hz
    rcases mem_insert_iff.mp hz with rfl | hz
    · exact ⟨q.source_mem_range, (Real.cos_sq_add_sin_sq θ).le⟩
    · have hzb : z = (Real.cos φ, Real.sin φ) := mem_singleton_iff.mp hz
      subst z
      exact ⟨q.target_mem_range, (Real.cos_sq_add_sin_sq φ).le⟩

/-- An actual injective disk path admits a finite injective outside completion
meeting its trace exactly at the original circle endpoints. Injectivity of the
given path supplies the endpoint distinction inside the proof. -/
theorem exists_outside_arc_for_injective_disk_path (θ φ : ℝ)
    (p : Path (Real.cos θ, Real.sin θ) (Real.cos φ, Real.sin φ))
    (hp : Function.Injective p)
    (hpD : range p ⊆ {z | z.1 ^ 2 + z.2 ^ 2 ≤ 1}) :
    ∃ us : List (ℝ × ℝ), ∃ hu : us ≠ [],
      us.head hu = (Real.cos θ, Real.sin θ) ∧
      us.getLast hu = (Real.cos φ, Real.sin φ) ∧
      ∃ q : Path (Real.cos θ, Real.sin θ) (Real.cos φ, Real.sin φ),
        Function.Injective q ∧ range q = polygonalChain us ∧
        range q \ {(Real.cos θ, Real.sin θ), (Real.cos φ, Real.sin φ)} ⊆
          {z | 1 < z.1 ^ 2 + z.2 ^ 2} ∧
        range q ∩ {z | z.1 ^ 2 + z.2 ^ 2 ≤ 1} =
          {(Real.cos θ, Real.sin θ), (Real.cos φ, Real.sin φ)} ∧
        range p ∩ range q =
          {(Real.cos θ, Real.sin θ), (Real.cos φ, Real.sin φ)} := by
  obtain ⟨us, hu, _, hhead, hlast, q, hq, hqrange, hqout, hqD⟩ :=
    exists_injective_polygonal_outside_completion θ φ (path_source_ne_target_of_injective hp)
  refine ⟨us, hu, hhead, hlast, q, hq, hqrange, hqout, hqD, subset_antisymm ?_ ?_⟩
  · intro z hz
    rw [← hqD]
    exact ⟨hz.2, hpD hz.1⟩
  · intro z hz
    rcases mem_insert_iff.mp hz with rfl | hz
    · exact ⟨p.source_mem_range, q.source_mem_range⟩
    · have hzb : z = (Real.cos φ, Real.sin φ) := mem_singleton_iff.mp hz
      subst z
      exact ⟨p.target_mem_range, q.target_mem_range⟩

/-- Two actual disk paths with disjoint traces retain that disjointness after
the first injective path is completed outside the disk. This is an internal
path-data result: it constructs the outside arc and does not assert separation
or an alternating-endpoint contradiction. -/
theorem exists_outside_arc_avoiding_disjoint_disk_path (θ₁ θ₂ θ₃ θ₄ : ℝ)
    (p : Path (Real.cos θ₁, Real.sin θ₁) (Real.cos θ₃, Real.sin θ₃))
    (r : Path (Real.cos θ₂, Real.sin θ₂) (Real.cos θ₄, Real.sin θ₄))
    (hp : Function.Injective p)
    (hpD : range p ⊆ {z | z.1 ^ 2 + z.2 ^ 2 ≤ 1})
    (hrD : range r ⊆ {z | z.1 ^ 2 + z.2 ^ 2 ≤ 1})
    (hpr : Disjoint (range p) (range r)) :
    ∃ us : List (ℝ × ℝ), ∃ hu : us ≠ [],
      us.head hu = (Real.cos θ₁, Real.sin θ₁) ∧
      us.getLast hu = (Real.cos θ₃, Real.sin θ₃) ∧
      ∃ q : Path (Real.cos θ₁, Real.sin θ₁) (Real.cos θ₃, Real.sin θ₃),
        Function.Injective q ∧ range q = polygonalChain us ∧
        range q \ {(Real.cos θ₁, Real.sin θ₁), (Real.cos θ₃, Real.sin θ₃)} ⊆
          {z | 1 < z.1 ^ 2 + z.2 ^ 2} ∧
        range p ∩ range q =
          {(Real.cos θ₁, Real.sin θ₁), (Real.cos θ₃, Real.sin θ₃)} ∧
        Disjoint (range q) (range r) := by
  obtain ⟨us, hu, hhead, hlast, q, hq, hqrange, hqout, hqD, hmeet⟩ :=
    exists_outside_arc_for_injective_disk_path θ₁ θ₃ p hp hpD
  refine ⟨us, hu, hhead, hlast, q, hq, hqrange, hqout, hmeet,
    disjoint_left.mpr ?_⟩
  intro z hzq hzr
  have hzends : z ∈ ({(Real.cos θ₁, Real.sin θ₁), (Real.cos θ₃, Real.sin θ₃)} :
      Set (ℝ × ℝ)) := by
    rw [← hqD]
    exact ⟨hzq, hrD hzr⟩
  have hzp : z ∈ range p := by
    rcases mem_insert_iff.mp hzends with rfl | hz
    · exact p.source_mem_range
    · rw [mem_singleton_iff] at hz
      rw [hz]
      exact p.target_mem_range
  exact disjoint_left.mp hpr hzp hzr

end LatticeProb.Topology
