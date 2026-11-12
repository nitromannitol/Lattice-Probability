import LatticeProb.Network.WalkUnitFlow

/-!
# The expected crossing flow of a random path

Let `P : Ω → List V` be a random walk path on a probability space `(Ω, μ)` taking finitely many
values, all in a finite set `R`, with measurable fibers. Its *expected crossing flow* is

  `θ(a, b) = ∑_{p ∈ R} μ(P = p) · walkFlow p a b`,

the expectation of the net number of crossings of the edge `(a, b)`. This is the flow used in the
upper bound for effective resistances by random paths (the method of random paths):

* `sum_expectedWalkFlow_eq_ite`: if every realization of `P` is a unit flow from `x` out of `A`,
  then so is `θ`;
* `abs_expectedWalkFlow_le`: if every realization is self-avoiding,
  `|θ(a, b)| ≤ μ(a ∈ P)`, the probability that the path visits `a`.

The random paths of interest choose a path through the cells met by a random segment. Such a
choice depends only on the finite set of indices `y ∈ Y` whose event `E y` occurs
(`hitFinset Y E ω`); `measurableSet_preimage_comp_hitFinset` shows that any choice of this form has
measurable fibers, so no measurable selection theorem is needed.
-/

namespace LatticeProb

open Finset MeasureTheory

variable {V Ω : Type*} [DecidableEq V] [MeasurableSpace Ω]

/-- The expected net crossing flow `∑_{p ∈ R} μ(P = p) · walkFlow p a b` of a random path `P`
whose values lie in the finite set `R`. -/
noncomputable def expectedWalkFlow (μ : Measure Ω) (P : Ω → List V) (R : Finset (List V))
    (a b : V) : ℝ :=
  ∑ p ∈ R, μ.real (P ⁻¹' {p}) * walkFlow p a b

theorem expectedWalkFlow_antisymm (μ : Measure Ω) (P : Ω → List V) (R : Finset (List V))
    (a b : V) : expectedWalkFlow μ P R a b = -expectedWalkFlow μ P R b a := by
  simp only [expectedWalkFlow, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun p _ => by rw [walkFlow_antisymm p a b]; ring

/-- The expected flow is carried by the edges of a symmetric relation carrying every path. -/
theorem expectedWalkFlow_eq_zero_of_not_rel {R' : V → V → Prop} (hR' : ∀ u v, R' u v → R' v u)
    (μ : Measure Ω) {P : Ω → List V} (R : Finset (List V))
    (hP : ∀ ω, (P ω).IsChain R') {a b : V} (hab : ¬ R' a b) :
    expectedWalkFlow μ P R a b = 0 := by
  refine Finset.sum_eq_zero fun p _ => ?_
  by_cases h : ∃ ω, P ω = p
  · obtain ⟨ω, rfl⟩ := h
    rw [walkFlow_eq_zero_of_not_rel hR' (hP ω) hab, mul_zero]
  · have : P ⁻¹' {p} = ∅ := Set.eq_empty_of_forall_notMem fun ω hω => h ⟨ω, hω⟩
    simp [this]

omit [DecidableEq V] in
/-- The weights `μ(P = p)`, `p ∈ R`, sum to one. -/
theorem sum_measureReal_preimage_eq_one (μ : Measure Ω) [IsProbabilityMeasure μ] {P : Ω → List V}
    {R : Finset (List V)} (hR : ∀ ω, P ω ∈ R) (hmeas : ∀ p ∈ R, MeasurableSet (P ⁻¹' {p})) :
    ∑ p ∈ R, μ.real (P ⁻¹' {p}) = 1 := by
  rw [sum_measureReal_preimage_singleton R hmeas]
  have : P ⁻¹' (R : Set (List V)) = Set.univ := Set.eq_univ_of_forall fun ω => hR ω
  rw [this, probReal_univ]

/-- **The expected flow of a random unit flow is a unit flow.** If every realization of the random
path `P` has divergence `1{a = x}` on `A`, so does the expected crossing flow. -/
theorem sum_expectedWalkFlow_eq_ite (μ : Measure Ω) [IsProbabilityMeasure μ] {P : Ω → List V}
    {R : Finset (List V)} (hR : ∀ ω, P ω ∈ R) (hmeas : ∀ p ∈ R, MeasurableSet (P ⁻¹' {p}))
    {S A : Finset V} {x : V}
    (hdiv : ∀ ω, ∀ a ∈ A, ∑ b ∈ S, walkFlow (P ω) a b = if a = x then 1 else 0) :
    ∀ a ∈ A, ∑ b ∈ S, expectedWalkFlow μ P R a b = if a = x then 1 else 0 := by
  intro a ha
  simp only [expectedWalkFlow]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  calc ∑ p ∈ R, μ.real (P ⁻¹' {p}) * ∑ b ∈ S, walkFlow p a b
      = ∑ p ∈ R, μ.real (P ⁻¹' {p}) * (if a = x then 1 else 0) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        by_cases h : ∃ ω, P ω = p
        · obtain ⟨ω, rfl⟩ := h
          rw [hdiv ω a ha]
        · have : P ⁻¹' {p} = ∅ := Set.eq_empty_of_forall_notMem fun ω hω => h ⟨ω, hω⟩
          simp [this]
    _ = if a = x then 1 else 0 := by
        rw [← Finset.sum_mul, sum_measureReal_preimage_eq_one μ hR hmeas, one_mul]

/-- **Expected crossing flow versus visiting probability.** If every realization of the random
path is self-avoiding, the expected net crossing flow through an edge at `a` is at most the
probability that the path visits `a`. -/
theorem abs_expectedWalkFlow_le (μ : Measure Ω) [IsFiniteMeasure μ] {P : Ω → List V}
    {R : Finset (List V)} (hR : ∀ ω, P ω ∈ R) (hmeas : ∀ p ∈ R, MeasurableSet (P ⁻¹' {p}))
    (hP : ∀ ω, (P ω).Nodup) (a b : V) :
    |expectedWalkFlow μ P R a b| ≤ μ.real {ω | a ∈ P ω} := by
  have key : ∀ p ∈ R, |μ.real (P ⁻¹' {p}) * walkFlow p a b|
      ≤ if a ∈ p then μ.real (P ⁻¹' {p}) else 0 := by
    intro p _
    by_cases h : ∃ ω, P ω = p
    · obtain ⟨ω, rfl⟩ := h
      rw [abs_mul, abs_of_nonneg measureReal_nonneg]
      calc μ.real (P ⁻¹' {P ω}) * |walkFlow (P ω) a b|
          ≤ μ.real (P ⁻¹' {P ω}) * (if a ∈ P ω then 1 else 0) :=
            mul_le_mul_of_nonneg_left (abs_walkFlow_le_ite (hP ω) a b) measureReal_nonneg
        _ = if a ∈ P ω then μ.real (P ⁻¹' {P ω}) else 0 := by split_ifs <;> simp
    · have : P ⁻¹' {p} = ∅ := Set.eq_empty_of_forall_notMem fun ω hω => h ⟨ω, hω⟩
      simp [this]
  calc |expectedWalkFlow μ P R a b|
      ≤ ∑ p ∈ R, |μ.real (P ⁻¹' {p}) * walkFlow p a b| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ R, if a ∈ p then μ.real (P ⁻¹' {p}) else 0 := Finset.sum_le_sum key
    _ = ∑ p ∈ R.filter (fun p => a ∈ p), μ.real (P ⁻¹' {p}) := (Finset.sum_filter _ _).symm
    _ = μ.real (P ⁻¹' ↑(R.filter (fun p => a ∈ p))) :=
        sum_measureReal_preimage_singleton _ fun p hp => hmeas p (Finset.mem_filter.1 hp).1
    _ = μ.real {ω | a ∈ P ω} := by
        congr 1
        ext ω
        simp [hR ω]

/-- `abs_expectedWalkFlow_le` with the visiting event enlarged to an event `G`: if the path visits
`a` only on `G`, then `|θ(a, b)| ≤ μ(G)`. -/
theorem abs_expectedWalkFlow_le_of_subset (μ : Measure Ω) [IsFiniteMeasure μ] {P : Ω → List V}
    {R : Finset (List V)} (hR : ∀ ω, P ω ∈ R) (hmeas : ∀ p ∈ R, MeasurableSet (P ⁻¹' {p}))
    (hP : ∀ ω, (P ω).Nodup) {a : V} {G : Set Ω} (hG : ∀ ω, a ∈ P ω → ω ∈ G) (b : V) :
    |expectedWalkFlow μ P R a b| ≤ μ.real G :=
  (abs_expectedWalkFlow_le μ hR hmeas hP a b).trans (measureReal_mono fun ω hω => hG ω hω)

section HitFinset

variable {ι : Type*}

open scoped Classical in
/-- The finite set of indices `y ∈ Y` whose event `E y` contains `ω`. -/
noncomputable def hitFinset (Y : Finset ι) (E : ι → Set Ω) (ω : Ω) : Finset ι :=
  Y.filter fun y => ω ∈ E y

omit [MeasurableSpace Ω] in
open scoped Classical in
theorem mem_hitFinset {Y : Finset ι} {E : ι → Set Ω} {ω : Ω} {y : ι} :
    y ∈ hitFinset Y E ω ↔ y ∈ Y ∧ ω ∈ E y := by
  unfold hitFinset
  exact Finset.mem_filter

omit [MeasurableSpace Ω] in
theorem hitFinset_subset (Y : Finset ι) (E : ι → Set Ω) (ω : Ω) : hitFinset Y E ω ⊆ Y :=
  fun _ hy => (mem_hitFinset.1 hy).1

/-- The events `{hitFinset Y E = T}` are measurable when every `E y`, `y ∈ Y`, is. -/
theorem measurableSet_hitFinset_eq {Y : Finset ι} {E : ι → Set Ω}
    (hE : ∀ y ∈ Y, MeasurableSet (E y)) (T : Finset ι) :
    MeasurableSet {ω | hitFinset Y E ω = T} := by
  classical
  by_cases hT : T ⊆ Y
  · have : {ω | hitFinset Y E ω = T} = ⋂ y ∈ Y, {ω | ω ∈ E y ↔ y ∈ T} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      constructor
      · rintro h y hy
        rw [← h, mem_hitFinset]
        tauto
      · intro h
        ext y
        rw [mem_hitFinset]
        constructor
        · rintro ⟨hy, hω⟩
          exact (h y hy).1 hω
        · intro hy
          exact ⟨hT hy, (h y (hT hy)).2 hy⟩
    rw [this]
    refine Finset.measurableSet_biInter Y fun y hy => ?_
    by_cases hyT : y ∈ T
    · convert hE y hy using 1
      ext ω
      simp [hyT]
    · convert (hE y hy).compl using 1
      ext ω
      simp [hyT]
  · have : {ω | hitFinset Y E ω = T} = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun ω hω => hT ?_
      rw [← (show hitFinset Y E ω = T from hω)]
      exact hitFinset_subset Y E ω
    rw [this]
    exact MeasurableSet.empty

/-- **Choices through the hit set have measurable fibers.** For any function `F` of the hit set,
the random variable `ω ↦ F (hitFinset Y E ω)` has measurable fibers. -/
theorem measurableSet_preimage_comp_hitFinset {β : Type*} {Y : Finset ι} {E : ι → Set Ω}
    (hE : ∀ y ∈ Y, MeasurableSet (E y)) (F : Finset ι → β) (p : β) :
    MeasurableSet ((fun ω => F (hitFinset Y E ω)) ⁻¹' {p}) := by
  classical
  have : (fun ω => F (hitFinset Y E ω)) ⁻¹' {p} =
      ⋃ T ∈ Y.powerset.filter (fun T => F T = p), {ω | hitFinset Y E ω = T} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_ofPred_eq,
      Finset.mem_filter, Finset.mem_powerset, exists_prop]
    constructor
    · intro h
      exact ⟨_, ⟨hitFinset_subset Y E ω, h⟩, rfl⟩
    · rintro ⟨T, ⟨-, hT⟩, rfl⟩
      exact hT
  rw [this]
  exact Finset.measurableSet_biUnion _ fun T _ => measurableSet_hitFinset_eq hE T

omit [MeasurableSpace Ω] in
/-- A choice through the hit set takes values in the image of the power set of `Y`. -/
theorem comp_hitFinset_mem_image {β : Type*} [DecidableEq β] (Y : Finset ι) (E : ι → Set Ω)
    (F : Finset ι → β) (ω : Ω) : F (hitFinset Y E ω) ∈ Y.powerset.image F :=
  Finset.mem_image_of_mem F (Finset.mem_powerset.2 (hitFinset_subset Y E ω))

end HitFinset

end LatticeProb
