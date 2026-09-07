/-
Revealing an independent family along a well-founded dependency order.

`IsExploration` reads the coordinates in the order of `ℕ`, and its
predictability hypothesis makes the `n`-th index a function of the coordinates
produced at the steps `0, …, n - 1`.  A process indexed by pairs, such as a
particle system in which the pair `(p, t)` reads the instruction that particle
`p` uses in round `t`, does not come with such an order: the read at `(p, t)`
depends on the reads of every particle that has visited the site of `p` before
round `t`, a set of pairs that any enumeration of `ℕ` is free to place later,
and each time level is infinite, so ordering the enumeration by time does not
help either.

What such a process does carry is a DEPENDENCY relation: a finite set `dep a`
of reads that the read `a` looks at, with no infinite regress.  This file
proves the exploration lemma in that form.  The index set is an arbitrary type
`κ`, the dependency is well founded with finite fibres, and the conclusion is
again that the revealed values are independent draws from the common law: the
law of the whole family `fun a => g (idx a ω) (ω (idx a ω))` is the product
measure over `κ`.

The proof does not build an enumeration of `κ`.  It works with the
finite-dimensional distributions directly: a finite set of reads has a maximal
element for the dependency, no other read of the set depends on it, and that is
exactly what is needed to factor its coordinate out of the event.
-/
import LatticeProb.Prob.Exploration

noncomputable section

namespace LatticeProb

open MeasureTheory ProbabilityTheory

variable {ι : Type*} [MeasurableSpace ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
  {α : Type*} [MeasurableSpace α] {κ : Type*}

/-- **A finite set has a maximal element for a well-founded relation.**  Well
foundedness is a statement about descending chains, so it gives minimal
elements directly; the maximal element of a finite set is obtained by passing
to the set of elements above a fixed one, which is strictly smaller because a
well-founded relation has no cycles. -/
theorem exists_maximal_of_wellFounded {r : κ → κ → Prop} (hwf : WellFounded r)
    (s : Finset κ) (hs : s.Nonempty) : ∃ a ∈ s, ∀ b ∈ s, ¬ r a b := by
  classical
  have key : ∀ n : ℕ, ∀ s : Finset κ, s.card ≤ n → s.Nonempty →
      ∃ a ∈ s, ∀ b ∈ s, ¬ r a b := by
    intro n
    induction n with
    | zero =>
        intro s hcard hs
        exact absurd (Finset.card_pos.mpr hs) (by omega)
    | succ n ih =>
        intro s hcard hs
        obtain ⟨a₀, ha₀⟩ := hs
        by_cases hmax : ∃ b ∈ s, r a₀ b
        · obtain ⟨b₀, hb₀s, hb₀⟩ := hmax
          set s' := s.filter (fun b => Relation.TransGen r a₀ b) with hs'def
          have hb₀' : b₀ ∈ s' := by
            rw [hs'def, Finset.mem_filter]
            exact ⟨hb₀s, Relation.TransGen.single hb₀⟩
          have hsub : s' ⊆ s.erase a₀ := by
            intro x hx
            rw [hs'def, Finset.mem_filter] at hx
            refine Finset.mem_erase.mpr ⟨?_, hx.1⟩
            rintro rfl
            exact (hwf.transGen.asymmetric x x hx.2) hx.2
          have hcard' : s'.card ≤ n := by
            have h1 := Finset.card_le_card hsub
            have h2 := Finset.card_erase_of_mem ha₀
            have h3 : 1 ≤ s.card := Finset.card_pos.mpr ⟨a₀, ha₀⟩
            omega
          obtain ⟨a, has', hamax⟩ := ih s' hcard' ⟨b₀, hb₀'⟩
          rw [hs'def, Finset.mem_filter] at has'
          refine ⟨a, has'.1, ?_⟩
          intro b hbs hrab
          have hbs' : b ∈ s' := by
            rw [hs'def, Finset.mem_filter]
            exact ⟨hbs, has'.2.tail hrab⟩
          exact hamax b hbs' hrab
        · exact ⟨a₀, ha₀, fun b hbs hrab => hmax ⟨b, hbs, hrab⟩⟩
  exact key s.card s le_rfl hs

/-- An exploration along a well-founded dependency: `idx a ω` is the coordinate
read by `a`, and `dep a` is the finite set of reads whose coordinates `idx a`
is allowed to look at.  There is no ambient order on `κ`; the dependency itself
is what orders the reads. -/
structure IsDagExploration [DecidableEq ι] (idx : κ → (Π i, X i) → ι)
    (dep : κ → Finset κ) : Prop where
  /-- Each index map is measurable. -/
  meas : ∀ a, Measurable (idx a)
  /-- The dependency has no infinite regress. -/
  wf : WellFounded fun b a => b ∈ dep a
  /-- Distinct reads read distinct coordinates. -/
  fresh : ∀ (a b : κ) (ω : Π i, X i), a ≠ b → idx a ω ≠ idx b ω
  /-- The read `a` looks only at the coordinates of the reads it depends on. -/
  pred : ∀ (a : κ) (ω : Π i, X i) (j : ι) (c : X j), (∀ b ∈ dep a, idx b ω ≠ j) →
    idx a (Function.update ω j c) = idx a ω

variable [DecidableEq ι]

/-- The value revealed by the read `a`, read through `g`. -/
def revealedDag (idx : κ → (Π i, X i) → ι) (g : ∀ i, X i → α)
    (ω : Π i, X i) (a : κ) : α :=
  g (idx a ω) (ω (idx a ω))

/-- The event that the reads in `s` reveal values in the sets `B`. -/
def exploredDag (idx : κ → (Π i, X i) → ι) (g : ∀ i, X i → α)
    (B : κ → Set α) (s : Finset κ) : Set (Π i, X i) :=
  {ω | ∀ a ∈ s, revealedDag idx g ω a ∈ B a}

variable {idx : κ → (Π i, X i) → ι} {dep : κ → Finset κ} {g : ∀ i, X i → α}

section Measurability

variable [Countable ι] [MeasurableSingletonClass ι]

omit [DecidableEq ι] in
theorem measurable_revealedDag (hidx : ∀ a, Measurable (idx a))
    (hg : ∀ i, Measurable (g i)) (a : κ) :
    Measurable (fun ω : Π i, X i => revealedDag idx g ω a) := by
  refine measurable_iff_comap_le.mpr ?_
  intro s hs
  obtain ⟨s, hs, rfl⟩ := hs
  have hcover : (fun ω : Π i, X i => revealedDag idx g ω a) ⁻¹' s
      = ⋃ j : ι, (idx a ⁻¹' {j} ∩ (fun ω : Π i, X i => g j (ω j)) ⁻¹' s) := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h; exact ⟨idx a ω, rfl, h⟩
    · rintro ⟨j, hj, h⟩
      subst hj
      exact h
  rw [hcover]
  exact MeasurableSet.iUnion fun j =>
    ((hidx a (measurableSet_singleton j)).inter
      (((hg j).comp (measurable_pi_apply j)) hs))

omit [DecidableEq ι] in
theorem measurableSet_exploredDag (hidx : ∀ a, Measurable (idx a))
    (hg : ∀ i, Measurable (g i)) {B : κ → Set α} (hB : ∀ a, MeasurableSet (B a))
    (s : Finset κ) : MeasurableSet (exploredDag idx g B s) := by
  have : exploredDag idx g B s
      = ⋂ a ∈ s, (fun ω : Π i, X i => revealedDag idx g ω a) ⁻¹' B a := by
    ext ω; simp [exploredDag, Set.mem_iInter]
  rw [this]
  exact MeasurableSet.biInter s.countable_toSet
    fun a _ => measurable_revealedDag hidx hg a (hB a)

end Measurability

omit [MeasurableSpace α] in
/-- A read depends on no coordinate of its own. -/
theorem notMem_dep_self (hidx : IsDagExploration idx dep) (a : κ) : a ∉ dep a :=
  fun h => hidx.wf.asymmetric a a h h

omit [MeasurableSpace α] in
/-- **The peeling step.**  Let `a` be a read that no read of `s` depends on, and
that is not itself in `s`.  Overwriting the coordinate that `a` reads changes
neither the values the reads of `s` reveal nor the coordinate that `a` reads. -/
theorem update_mem_exploredDag_inter (hidx : IsDagExploration idx dep) {B : κ → Set α}
    {s : Finset κ} {a : κ} (hamax : ∀ b ∈ s, a ∉ dep b) (has : a ∉ s)
    {j : ι} (c : X j) {ω : Π i, X i}
    (hω : ω ∈ exploredDag idx g B s ∩ {ω | idx a ω = j}) :
    Function.update ω j c ∈ exploredDag idx g B s ∩ {ω | idx a ω = j} := by
  obtain ⟨hexp, hj⟩ := hω
  have hne : ∀ b : κ, b ≠ a → idx b ω ≠ j := by
    intro b hb
    rw [← hj]
    exact hidx.fresh b a ω hb
  have hidxa : idx a (Function.update ω j c) = idx a ω := by
    refine hidx.pred a ω j c fun b hb => hne b ?_
    rintro rfl
    exact notMem_dep_self hidx _ hb
  have hidxb : ∀ b ∈ s, idx b (Function.update ω j c) = idx b ω := by
    intro b hbs
    refine hidx.pred b ω j c fun b' hb' => hne b' ?_
    rintro rfl
    exact hamax b hbs hb'
  refine ⟨?_, ?_⟩
  · intro b hbs
    have hba : b ≠ a := by rintro rfl; exact has hbs
    have h2 : Function.update ω j c (idx b ω) = ω (idx b ω) :=
      Function.update_of_ne (hne b hba) _ _
    show revealedDag idx g (Function.update ω j c) b ∈ B b
    unfold revealedDag
    rw [hidxb b hbs, h2]
    exact hexp b hbs
  · show idx a (Function.update ω j c) = j
    rw [hidxa, hj]

variable [Countable ι] [MeasurableSingletonClass ι]

/-- **The exploration lemma along a dependency, finite dimensional form.**  Any
finite set of reads reveals independent values with law `ν`. -/
theorem measure_exploredDag (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    {ν : Measure α} (hidx : IsDagExploration idx dep) (hg : ∀ i, Measurable (g i))
    (hlaw : ∀ i, (μ i).map (g i) = ν) {B : κ → Set α} (hB : ∀ a, MeasurableSet (B a))
    (s : Finset κ) :
    Measure.infinitePi μ (exploredDag idx g B s) = ∏ a ∈ s, ν (B a) := by
  classical
  have hlawB : ∀ (j : ι) (a : κ), μ j (g j ⁻¹' B a) = ν (B a) := by
    intro j a
    rw [← hlaw j, Measure.map_apply (hg j) (hB a)]
  have key : ∀ n : ℕ, ∀ s : Finset κ, s.card ≤ n →
      Measure.infinitePi μ (exploredDag idx g B s) = ∏ a ∈ s, ν (B a) := by
    intro n
    induction n with
    | zero =>
        intro s hcard
        have hs : s = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
        subst hs
        have : exploredDag idx g B ∅ = Set.univ := by ext ω; simp [exploredDag]
        rw [this, Finset.prod_empty, measure_univ]
    | succ n ih =>
        intro s hcard
        rcases s.eq_empty_or_nonempty with rfl | hs
        · have : exploredDag idx g B ∅ = Set.univ := by ext ω; simp [exploredDag]
          rw [this, Finset.prod_empty, measure_univ]
        obtain ⟨a, has, hamax⟩ :=
          exists_maximal_of_wellFounded (r := fun x y => x ∈ dep y) hidx.wf s hs
        set s₀ := s.erase a with hs₀def
        have hs₀card : s₀.card ≤ n := by
          have h2 : s₀.card = s.card - 1 := by
            rw [hs₀def]; exact Finset.card_erase_of_mem has
          have h3 : 1 ≤ s.card := Finset.card_pos.mpr hs
          omega
        have has₀ : a ∉ s₀ := Finset.notMem_erase a s
        have hamax₀ : ∀ b ∈ s₀, a ∉ dep b := fun b hb => hamax b (Finset.mem_of_mem_erase hb)
        have hAmeas : ∀ j : ι,
            MeasurableSet (exploredDag idx g B s₀ ∩ {ω : Π i, X i | idx a ω = j}) := by
          intro j
          exact (measurableSet_exploredDag hidx.meas hg hB s₀).inter
            (hidx.meas a (measurableSet_singleton j))
        have hdisj : Pairwise (Function.onFun Disjoint
            fun j : ι => exploredDag idx g B s₀ ∩ {ω : Π i, X i | idx a ω = j}) := by
          intro j j' hjj'
          refine Set.disjoint_left.mpr fun ω hω hω' => hjj' ?_
          exact hω.2.symm.trans hω'.2
        have hcover : exploredDag idx g B s₀
            = ⋃ j : ι, (exploredDag idx g B s₀ ∩ {ω : Π i, X i | idx a ω = j}) := by
          ext ω
          simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
          exact ⟨fun h => ⟨idx a ω, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩
        have hsplit : exploredDag idx g B s
            = ⋃ j : ι, ((exploredDag idx g B s₀ ∩ {ω : Π i, X i | idx a ω = j})
                ∩ {ω : Π i, X i | ω j ∈ g j ⁻¹' B a}) := by
          ext ω
          simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage]
          constructor
          · intro h
            refine ⟨idx a ω, ⟨fun b hb => h b (Finset.mem_of_mem_erase hb), rfl⟩, ?_⟩
            exact h a has
          · rintro ⟨j, ⟨hexp, hj⟩, hval⟩
            intro b hb
            by_cases hba : b = a
            · subst hba
              show revealedDag idx g ω b ∈ B b
              unfold revealedDag
              rw [hj]
              exact hval
            · exact hexp b (Finset.mem_erase.mpr ⟨hba, hb⟩)
        have hfactor : ∀ j : ι,
            Measure.infinitePi μ ((exploredDag idx g B s₀ ∩ {ω : Π i, X i | idx a ω = j})
                ∩ {ω : Π i, X i | ω j ∈ g j ⁻¹' B a})
              = Measure.infinitePi μ
                  (exploredDag idx g B s₀ ∩ {ω : Π i, X i | idx a ω = j}) * ν (B a) := by
          intro j
          have hne : Nonempty (X j) := nonempty_of_isProbabilityMeasure (μ j)
          have hinv : ∀ ω : Π i, X i,
              Function.update ω j (Classical.arbitrary (X j))
                  ∈ exploredDag idx g B s₀ ∩ {ω : Π i, X i | idx a ω = j}
                ↔ ω ∈ exploredDag idx g B s₀ ∩ {ω : Π i, X i | idx a ω = j} := by
            intro ω
            refine ⟨fun h => ?_, fun h => update_mem_exploredDag_inter hidx hamax₀ has₀ _ h⟩
            have := update_mem_exploredDag_inter (g := g) hidx hamax₀ has₀ (ω j) h
            rwa [Function.update_idem, Function.update_eq_self] at this
          rw [measure_inter_eval_of_update_invariant μ (Classical.arbitrary (X j))
            (hAmeas j) hinv ((hg j) (hB a)), hlawB j a]
        rw [hsplit]
        rw [measure_iUnion (μ := Measure.infinitePi μ)
          (f := fun j : ι => exploredDag idx g B s₀ ∩ {ω : Π i, X i | idx a ω = j}
            ∩ {ω : Π i, X i | ω j ∈ g j ⁻¹' B a})
          (fun j j' hjj' => (hdisj hjj').mono Set.inter_subset_left Set.inter_subset_left)
          (fun j => (hAmeas j).inter ((measurable_pi_apply j) ((hg j) (hB a))))]
        calc ∑' j : ι, Measure.infinitePi μ
              ((exploredDag idx g B s₀ ∩ {ω : Π i, X i | idx a ω = j})
                ∩ {ω : Π i, X i | ω j ∈ g j ⁻¹' B a})
            = ∑' j : ι, Measure.infinitePi μ
                (exploredDag idx g B s₀ ∩ {ω : Π i, X i | idx a ω = j}) * ν (B a) :=
              tsum_congr hfactor
          _ = (∑' j : ι, Measure.infinitePi μ
                (exploredDag idx g B s₀ ∩ {ω : Π i, X i | idx a ω = j})) * ν (B a) :=
              ENNReal.tsum_mul_right
          _ = Measure.infinitePi μ (exploredDag idx g B s₀) * ν (B a) := by
              rw [← measure_iUnion hdisj hAmeas, ← hcover]
          _ = ∏ b ∈ s, ν (B b) := by
              rw [ih s₀ hs₀card, hs₀def, Finset.prod_erase_mul _ _ has]
  exact key s.card s le_rfl

omit [MeasurableSpace ι] [DecidableEq ι] [Countable ι] [MeasurableSingletonClass ι] in
/-- A read reads a coordinate, so if there is a read there is an index. -/
theorem nonempty_of_dagExploration (μ : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)] (idx : κ → (Π i, X i) → ι) (a : κ) : Nonempty ι := by
  have : ∀ i, Nonempty (X i) := fun i => nonempty_of_isProbabilityMeasure (μ i)
  exact ⟨idx a fun i => Classical.arbitrary (X i)⟩

/-- **The exploration lemma along a well-founded dependency.**  An independent
family read at coordinates `idx a ω`, where distinct reads read distinct
coordinates and each read looks only at the coordinates of the finitely many
reads it depends on, reveals a family of independent draws from the common law
`ν` of the values.  No ordering of the reads is used, and none is built. -/
theorem map_revealed_dag (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    {ν : Measure α} (hidx : IsDagExploration idx dep) (hg : ∀ i, Measurable (g i))
    (hlaw : ∀ i, (μ i).map (g i) = ν) :
    (Measure.infinitePi μ).map (revealedDag idx g)
      = Measure.infinitePi fun _ : κ => ν := by
  classical
  have hνprob : ∀ _ : κ, IsProbabilityMeasure ν := by
    intro a
    obtain ⟨i⟩ := nonempty_of_dagExploration μ idx a
    rw [← hlaw i]
    exact Measure.isProbabilityMeasure_map (hg i).aemeasurable
  have hmeas : Measurable (revealedDag idx g) :=
    measurable_pi_lambda _ fun a => measurable_revealedDag hidx.meas hg a
  refine Measure.eq_infinitePi (μ := fun _ : κ => ν) (hμ := hνprob) fun s t ht => ?_
  have hpre : revealedDag idx g ⁻¹' Set.pi (↑s) t = exploredDag idx g t s := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, exploredDag, Set.mem_setOf_eq]
  rw [Measure.map_apply hmeas (MeasurableSet.pi s.countable_toSet fun i _ => ht i), hpre,
    measure_exploredDag μ hidx hg hlaw ht s]

end LatticeProb

end
