/-
Revealing an independent family along a path chosen from what has been seen.

A process that reads an independent family one coordinate at a time, choosing
the next coordinate from the values it has already read and never reading a
coordinate twice, sees a sequence of fresh independent draws.  This is the
fact behind every "the particle follows a random walk" statement in the
papers: the instruction stacks sit at the sites, so the instruction a particle
reads is a coordinate of a fixed independent family, and the coordinate it
reads next depends on where the earlier instructions took it.

The exploration is given by its index map `idx n : (Π i, X i) → ι`, the
coordinate read at step `n`, and the two hypotheses of `IsExploration`: the
indices are never repeated, and `idx n` does not read a coordinate outside the
first `n` indices it has itself produced.

The values are read through `g i : X i → α`, so that coordinates whose laws
differ may still reveal a common law: in the lattice application `X (y, j)` is
the site the `j`-th departure from `y` moves to, whose law depends on `y`,
while `g (y, j) z = z - y` is the step, whose law does not.
-/
import LatticeProb.Prob.Coordinate

noncomputable section

namespace LatticeProb

open MeasureTheory ProbabilityTheory

variable {ι : Type*} [MeasurableSpace ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
  {α : Type*} [MeasurableSpace α]

omit [MeasurableSpace ι] in
/-- **A set against one coordinate.**  A set that is unchanged by overwriting
the coordinate `j` is independent of that coordinate. -/
theorem measure_inter_eval_of_update_invariant [DecidableEq ι]
    (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)] {j : ι} (c : X j)
    {A : Set (Π i, X i)} (hA : MeasurableSet A)
    (hinv : ∀ ω, Function.update ω j c ∈ A ↔ ω ∈ A)
    {t : Set (X j)} (ht : MeasurableSet t) :
    Measure.infinitePi μ (A ∩ {ω | ω j ∈ t})
      = Measure.infinitePi μ A * μ j t := by
  classical
  set F : (Π i, X i) → ℝ := Set.indicator A (fun _ => 1) with hF
  have hFmeas : Measurable F := (measurable_const.indicator hA)
  have hFinv : ∀ ω, F (Function.update ω j c) = F ω := by
    intro ω
    by_cases h : ω ∈ A
    · rw [hF, Set.indicator_of_mem ((hinv ω).mpr h), Set.indicator_of_mem h]
    · rw [hF, Set.indicator_of_notMem (fun hc => h ((hinv ω).mp hc)),
        Set.indicator_of_notMem h]
  have hind := indepFun_of_update_invariant μ c F hFmeas hFinv
  have hpre : F ⁻¹' {(1 : ℝ)} = A := by
    ext ω
    by_cases h : ω ∈ A
    · simp [hF, h]
    · simp [hF, h]
  have := hind.measure_inter_preimage_eq_mul {(1 : ℝ)} t (measurableSet_singleton _) ht
  rw [hpre] at this
  have hev : (fun ω : Π i, X i => ω j) ⁻¹' t = {ω : Π i, X i | ω j ∈ t} := rfl
  rw [hev] at this
  rw [this]
  congr 1
  rw [← hev, ← Measure.map_apply (measurable_pi_apply j) ht, Measure.infinitePi_map_eval]

/-- An exploration of the coordinates: `idx n ω` is the coordinate read at step
`n`.  It is never a coordinate already read, and it is unchanged when a
coordinate that has not been read is overwritten. -/
structure IsExploration [DecidableEq ι] (idx : ℕ → (Π i, X i) → ι) : Prop where
  /-- Each index map is measurable. -/
  meas : ∀ n, Measurable (idx n)
  /-- No coordinate is read twice. -/
  fresh : ∀ (n : ℕ) (ω : Π i, X i), ∀ k < n, idx k ω ≠ idx n ω
  /-- The `n`-th index reads only the coordinates of the first `n` indices. -/
  pred : ∀ (n : ℕ) (ω : Π i, X i) (j : ι) (c : X j), (∀ k < n, idx k ω ≠ j) →
    idx n (Function.update ω j c) = idx n ω

variable [DecidableEq ι]

/-- The value revealed at step `n`, read through `g`. -/
def revealed (idx : ℕ → (Π i, X i) → ι) (g : ∀ i, X i → α)
    (ω : Π i, X i) (n : ℕ) : α :=
  g (idx n ω) (ω (idx n ω))

/-- The event that the first `n` revealed values lie in the sets `B`. -/
def explored (idx : ℕ → (Π i, X i) → ι) (g : ∀ i, X i → α)
    (B : ℕ → Set α) (n : ℕ) : Set (Π i, X i) :=
  {ω | ∀ k < n, revealed idx g ω k ∈ B k}

variable {idx : ℕ → (Π i, X i) → ι} {g : ∀ i, X i → α}

section Measurability

variable [Countable ι] [MeasurableSingletonClass ι]

omit [DecidableEq ι] in
theorem measurable_revealed (hidx : ∀ n, Measurable (idx n))
    (hg : ∀ i, Measurable (g i)) (n : ℕ) :
    Measurable (fun ω : Π i, X i => revealed idx g ω n) := by
  refine measurable_iff_comap_le.mpr ?_
  intro s hs
  obtain ⟨s, hs, rfl⟩ := hs
  have hcover : (fun ω : Π i, X i => revealed idx g ω n) ⁻¹' s
      = ⋃ j : ι, (idx n ⁻¹' {j} ∩ (fun ω : Π i, X i => g j (ω j)) ⁻¹' s) := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h; exact ⟨idx n ω, rfl, h⟩
    · rintro ⟨j, hj, h⟩
      subst hj
      exact h
  rw [hcover]
  exact MeasurableSet.iUnion fun j =>
    ((hidx n (measurableSet_singleton j)).inter
      (((hg j).comp (measurable_pi_apply j)) hs))

omit [DecidableEq ι] in
theorem measurableSet_explored (hidx : ∀ n, Measurable (idx n))
    (hg : ∀ i, Measurable (g i)) {B : ℕ → Set α} (hB : ∀ k, MeasurableSet (B k)) (n : ℕ) :
    MeasurableSet (explored idx g B n) := by
  have : explored idx g B n
      = ⋂ k ∈ Finset.range n, (fun ω : Π i, X i => revealed idx g ω k) ⁻¹' B k := by
    ext ω; simp [explored, Set.mem_iInter]
  rw [this]
  exact MeasurableSet.biInter (Finset.range n).countable_toSet
    fun k _ => measurable_revealed hidx hg k (hB k)

end Measurability

omit [MeasurableSpace α] in
/-- Overwriting a coordinate that the exploration reads at step `n` changes
neither the first `n` revealed values nor the `n`-th index. -/
theorem update_mem_explored_inter (hidx : IsExploration idx) {B : ℕ → Set α} {n : ℕ}
    {j : ι} (c : X j) {ω : Π i, X i}
    (hω : ω ∈ explored idx g B n ∩ {ω | idx n ω = j}) :
    Function.update ω j c ∈ explored idx g B n ∩ {ω | idx n ω = j} := by
  obtain ⟨hexp, hj⟩ := hω
  have hne : ∀ k < n, idx k ω ≠ j := by
    intro k hk
    rw [← hj]
    exact hidx.fresh n ω k hk
  have hidxk : ∀ k ≤ n, idx k (Function.update ω j c) = idx k ω := by
    intro k hk
    exact hidx.pred k ω j c fun m hm => hne m (lt_of_lt_of_le hm hk)
  refine ⟨?_, ?_⟩
  · intro k hk
    have h1 : idx k (Function.update ω j c) = idx k ω := hidxk k (le_of_lt hk)
    have h2 : Function.update ω j c (idx k ω) = ω (idx k ω) :=
      Function.update_of_ne (hne k hk) _ _
    show revealed idx g (Function.update ω j c) k ∈ B k
    unfold revealed
    rw [h1, h2]
    exact hexp k hk
  · show idx n (Function.update ω j c) = j
    rw [hidxk n le_rfl, hj]

omit [MeasurableSpace ι] [DecidableEq ι] in
/-- The exploration reads a coordinate, so if the family is indexed by nothing
there is nothing to read: the index type is nonempty. -/
theorem nonempty_of_exploration (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (idx : ℕ → (Π i, X i) → ι) : Nonempty ι := by
  have : ∀ i, Nonempty (X i) := fun i => nonempty_of_isProbabilityMeasure (μ i)
  exact ⟨idx 0 fun i => Classical.arbitrary (X i)⟩

variable [Countable ι] [MeasurableSingletonClass ι]

/-- **The exploration lemma, finite dimensional form.**  The first `n` values an
exploration reveals are independent with law `ν`. -/
theorem measure_explored (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    {ν : Measure α} (hidx : IsExploration idx) (hg : ∀ i, Measurable (g i))
    (hlaw : ∀ i, (μ i).map (g i) = ν) {B : ℕ → Set α} (hB : ∀ k, MeasurableSet (B k)) :
    ∀ n, Measure.infinitePi μ (explored idx g B n) = ∏ k ∈ Finset.range n, ν (B k) := by
  classical
  have hAmeas : ∀ (n : ℕ) (j : ι),
      MeasurableSet (explored idx g B n ∩ {ω : Π i, X i | idx n ω = j}) := by
    intro n j
    exact (measurableSet_explored hidx.meas hg hB n).inter
      (hidx.meas n (measurableSet_singleton j))
  have hdisj : ∀ n : ℕ, Pairwise (Function.onFun Disjoint
      fun j : ι => explored idx g B n ∩ {ω : Π i, X i | idx n ω = j}) := by
    intro n j j' hjj'
    refine Set.disjoint_left.mpr fun ω hω hω' => hjj' ?_
    exact hω.2.symm.trans hω'.2
  have hcover : ∀ n : ℕ, explored idx g B n
      = ⋃ j : ι, (explored idx g B n ∩ {ω : Π i, X i | idx n ω = j}) := by
    intro n
    ext ω
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    exact ⟨fun h => ⟨idx n ω, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩
  have hsplit : ∀ n : ℕ, explored idx g B (n + 1)
      = ⋃ j : ι, ((explored idx g B n ∩ {ω : Π i, X i | idx n ω = j})
          ∩ {ω : Π i, X i | ω j ∈ g j ⁻¹' B n}) := by
    intro n
    ext ω
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage]
    constructor
    · intro h
      refine ⟨idx n ω, ⟨fun k hk => h k (Nat.lt_succ_of_lt hk), rfl⟩, ?_⟩
      exact h n (Nat.lt_succ_self n)
    · rintro ⟨j, ⟨hexp, hj⟩, hval⟩
      intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | rfl
      · exact hexp k hk'
      · show revealed idx g ω k ∈ B k
        unfold revealed
        rw [hj]
        exact hval
  intro n
  induction n with
  | zero =>
      have : explored idx g B 0 = Set.univ := by
        ext ω; simp [explored]
      rw [this, Finset.range_zero, Finset.prod_empty, measure_univ]
  | succ n ih =>
      have hlawB : ∀ j : ι, μ j (g j ⁻¹' B n) = ν (B n) := by
        intro j
        rw [← hlaw j, Measure.map_apply (hg j) (hB n)]
      have hfactor : ∀ j : ι,
          Measure.infinitePi μ ((explored idx g B n ∩ {ω : Π i, X i | idx n ω = j})
              ∩ {ω : Π i, X i | ω j ∈ g j ⁻¹' B n})
            = Measure.infinitePi μ (explored idx g B n ∩ {ω : Π i, X i | idx n ω = j})
              * ν (B n) := by
        intro j
        have hne : Nonempty (X j) := nonempty_of_isProbabilityMeasure (μ j)
        have hinv : ∀ ω : Π i, X i,
            Function.update ω j (Classical.arbitrary (X j))
                ∈ explored idx g B n ∩ {ω : Π i, X i | idx n ω = j}
              ↔ ω ∈ explored idx g B n ∩ {ω : Π i, X i | idx n ω = j} := by
          intro ω
          refine ⟨fun h => ?_, fun h => update_mem_explored_inter hidx _ h⟩
          have := update_mem_explored_inter (g := g) hidx (ω j) h
          rwa [Function.update_idem, Function.update_eq_self] at this
        rw [measure_inter_eval_of_update_invariant μ (Classical.arbitrary (X j))
          (hAmeas n j) hinv ((hg j) (hB n)), hlawB j]
      rw [hsplit n]
      rw [measure_iUnion (μ := Measure.infinitePi μ)
        (f := fun j : ι => explored idx g B n ∩ {ω : Π i, X i | idx n ω = j}
          ∩ {ω : Π i, X i | ω j ∈ g j ⁻¹' B n})
        (fun j j' hjj' =>
          ((hdisj n) hjj').mono Set.inter_subset_left Set.inter_subset_left)
        (fun j => (hAmeas n j).inter ((measurable_pi_apply j) ((hg j) (hB n))))]
      calc ∑' j : ι, Measure.infinitePi μ
            ((explored idx g B n ∩ {ω : Π i, X i | idx n ω = j})
              ∩ {ω : Π i, X i | ω j ∈ g j ⁻¹' B n})
          = ∑' j : ι, Measure.infinitePi μ
              (explored idx g B n ∩ {ω : Π i, X i | idx n ω = j}) * ν (B n) := by
            exact tsum_congr hfactor
        _ = (∑' j : ι, Measure.infinitePi μ
              (explored idx g B n ∩ {ω : Π i, X i | idx n ω = j})) * ν (B n) :=
            ENNReal.tsum_mul_right
        _ = Measure.infinitePi μ (explored idx g B n) * ν (B n) := by
            rw [← measure_iUnion (hdisj n) (hAmeas n), ← hcover n]
        _ = ∏ k ∈ Finset.range (n + 1), ν (B k) := by
            rw [Finset.prod_range_succ, ih]

/-- **The exploration lemma.**  An exploration of an independent family that
never reads a coordinate twice, and whose next coordinate is a function of the
values it has read, reveals a sequence of independent draws from the common
law `ν` of the values. -/
theorem map_revealed (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    {ν : Measure α} (hidx : IsExploration idx) (hg : ∀ i, Measurable (g i))
    (hlaw : ∀ i, (μ i).map (g i) = ν) :
    (Measure.infinitePi μ).map (revealed idx g) = Measure.infinitePi fun _ : ℕ => ν := by
  classical
  have hne : Nonempty ι := nonempty_of_exploration μ idx
  have hνprob : IsProbabilityMeasure ν := by
    obtain ⟨i⟩ := hne
    rw [← hlaw i]
    exact Measure.isProbabilityMeasure_map (hg i).aemeasurable
  have hmeas : Measurable (revealed idx g) :=
    measurable_pi_lambda _ fun n => measurable_revealed hidx.meas hg n
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  obtain ⟨N, hN⟩ := s.exists_nat_subset_range
  set B : ℕ → Set α := fun k => if k ∈ s then t k else Set.univ with hBdef
  have hB : ∀ k, MeasurableSet (B k) := by
    intro k
    by_cases hk : k ∈ s <;> simp [hBdef, hk, ht k]
  have hpre : revealed idx g ⁻¹' Set.pi (↑s) t = explored idx g B N := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, explored, Set.mem_setOf_eq]
    constructor
    · intro h k hk
      by_cases hks : k ∈ s
      · simpa [hBdef, hks] using h k hks
      · simp [hBdef, hks]
    · intro h k hk
      have := h k (Finset.mem_range.mp (hN hk))
      simpa [hBdef, hk] using this
  rw [Measure.map_apply hmeas (MeasurableSet.pi s.countable_toSet fun i _ => ht i), hpre,
    measure_explored μ hidx hg hlaw hB N]
  refine (Finset.prod_subset (fun k hk => Finset.mem_range.mpr (Finset.mem_range.mp (hN hk)))
    ?_).symm.trans ?_
  · intro k _ hks
    simp [hBdef, hks]
  · exact Finset.prod_congr rfl fun k hk => by simp [hBdef, hk]

/-- Each single revealed value has law `ν`. -/
theorem map_revealed_apply (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    {ν : Measure α} (hidx : IsExploration idx) (hg : ∀ i, Measurable (g i))
    (hlaw : ∀ i, (μ i).map (g i) = ν) (n : ℕ) :
    (Measure.infinitePi μ).map (fun ω => revealed idx g ω n) = ν := by
  obtain ⟨i₀⟩ : Nonempty ι := nonempty_of_exploration μ idx
  haveI : IsProbabilityMeasure ν := by
    rw [← hlaw i₀]; exact Measure.isProbabilityMeasure_map (hg i₀).aemeasurable
  have hmeas : Measurable (revealed idx g) :=
    measurable_pi_lambda _ fun k => measurable_revealed hidx.meas hg k
  have : (fun ω : Π i, X i => revealed idx g ω n)
      = (fun f : ℕ → α => f n) ∘ revealed idx g := rfl
  rw [this, ← Measure.map_map (measurable_pi_apply n) hmeas,
    map_revealed μ hidx hg hlaw, Measure.infinitePi_map_eval]

/-- **The exploration lemma for one common law.**  When every coordinate has the
same law `ν`, an exploration reveals independent draws from `ν`. -/
theorem map_revealed_of_const {ν : Measure α} [IsProbabilityMeasure ν]
    {idx : ℕ → (ι → α) → ι} (hidx : IsExploration (X := fun _ : ι => α) idx) :
    (Measure.infinitePi fun _ : ι => ν).map (fun ω n => ω (idx n ω))
      = Measure.infinitePi fun _ : ℕ => ν :=
  map_revealed (X := fun _ : ι => α) (g := fun _ => id) (fun _ => ν) hidx
    (fun _ => measurable_id) (fun _ => Measure.map_id)

end LatticeProb

end
