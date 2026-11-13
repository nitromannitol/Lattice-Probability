/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.MeasurableInfinitePatchMinimizer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.MeasurableBlockMinimizer
import LatticeProb.Bonanno.ReflectedGMS.Forms.FiniteMinimizerPointwiseConvergence
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Logic.Equiv.List

/-!
# A measurable full-energy anchored minimizer on a possibly infinite patch

`Corrector/MeasurableBlockMinimizer.lean` produces a measurable field of anchored
minimizers on a **finite** block whose labels and boundary vary with the environment, and
`Forms/FiniteMinimizerPointwiseConvergence.lean` shows that the minimizers of a monotone
anchored exhaustion converge pointwise to the unique **full-energy** anchored minimizer of
the whole graph. The two cannot be composed directly: the exhaustion produced by
`Forms/AnchoredFiniteExhaustion.lean`
(`exists_monotone_finset_exhaustion_boundaryAnchored`) chooses, for every vertex, an
arbitrary anchor walk through `Classical.choice`, so for a random graph its levels are not
functions of the environment at all, let alone measurable ones.

This module supplies the missing coherent producer and then assembles the limit.

* A finite anchor path is recorded as a plain `List V`: `IsAnchorChain G A x l` says that
  `l` starts at `x`, follows edges of `G`, and ends in the boundary set `A`. Since `V` is
  countable so is `List V`, and `firstAnchorChain` picks the **first** anchor chain of `x`
  in one fixed enumeration of all finite vertex lists. This replaces the arbitrary choice
  by a canonical one whose fibres `{ω | firstAnchorChain (G ω) (A ω) x = l}` are countable
  boolean combinations of the events `{ω | 0 < (G ω).c a b}` and `{ω | a ∈ A ω}`, hence
  measurable (`measurableSet_firstAnchorChain_eq`).
* `patchLevel G A n`, the union of the chosen anchor chains of the finitely many vertices
  of index at most `n`, is therefore a measurably varying finite label set
  (`measurableSet_patchLevel_eq`), and it is monotone, exhausting and anchored at every
  environment (`boundaryAnchored_patchLevel`), the last obtained from the suffix of a chosen
  chain, which is again an anchor chain inside the same level.
* `exists_measurable_anchored_energy_minimizer` feeds this exhaustion to the varying-block
  minimizers and passes to the pointwise limit: the resulting field is measurable, and at
  **every** environment it has finite energy, carries the prescribed boundary values on the
  whole of `A ω` and minimizes the *full* Dirichlet energy among all finite-energy
  functions with those boundary values.

The patch is arbitrary: the graph may be disconnected and infinite, `A ω` may be infinite,
no level is assumed connected, no finite spatial cell count is assumed, and the full
finite-energy space is used throughout — no finite-support closure. The only pointwise
hypothesis is `BoundaryAnchored (G ω) (A ω)` together with finite energy of the reference
field, and the only measurability hypotheses are those of the adjacency data `(G ω).c`, the
boundary membership `x ∈ A ω` and the reference values `u ω x`.
-/

set_option autoImplicit false

namespace ReflectedGMS

namespace MeasurableInfinitePatchMinimizer

open MeasureTheory Filter Topology
open AnchoredFiniteExhaustion FiniteDirichletEnergyLimit

/-! ### Finite anchor paths recorded as vertex lists -/

section Chains

variable {V : Type*} (G : ReflectedWalk.ConductanceGraph V)

/-- **A finite anchor path of `x`, recorded as a list.** The list is nonempty, starts at
`x`, consecutive entries are adjacent in `G`, and the last entry lies in the boundary set
`A`. -/
def IsAnchorChain (A : Set V) (x : V) (l : List V) : Prop :=
  ∃ hne : l ≠ [], l.IsChain G.toSimpleGraph.Adj ∧ l.head hne = x ∧ l.getLast hne ∈ A

/-- An anchored graph has an anchor chain at every vertex: the support of an anchor walk. -/
theorem exists_isAnchorChain {A : Set V} (hA : BoundaryAnchored G A) (x : V) :
    ∃ l : List V, IsAnchorChain G A x l := by
  obtain ⟨a, haA, hreach⟩ := hA x
  obtain ⟨p⟩ := hreach
  refine ⟨p.support, p.support_ne_nil, p.isChain_adj_support, p.head_support, ?_⟩
  rw [p.getLast_support]
  exact haA

/-- **An anchor chain inside a vertex set gives an anchor walk inside that set.** The walk
is the one reconstructed from the list by `SimpleGraph.Walk.ofSupport`, so its support is
exactly the list. -/
theorem exists_walk_of_isAnchorChain {A S : Set V} {x : V} {l : List V}
    (h : IsAnchorChain G A x l) (hsub : ∀ y ∈ l, y ∈ S) :
    ∃ a ∈ A, ∃ p : G.toSimpleGraph.Walk x a, ∀ y ∈ p.support, y ∈ S := by
  obtain ⟨hne, hchain, hhead, hlast⟩ := h
  subst hhead
  refine ⟨l.getLast hne, hlast,
    SimpleGraph.Walk.ofSupport (G := G.toSimpleGraph) l hne hchain, ?_⟩
  intro y hy
  rw [SimpleGraph.Walk.support_ofSupport] at hy
  exact hsub y hy

/-- **Every vertex of an anchor chain has an anchor chain inside it**: the suffix of the
chain starting at that vertex is again an anchor chain, with the same last entry. -/
theorem exists_isAnchorChain_subset_of_mem {A : Set V} {x u : V} {l : List V}
    (h : IsAnchorChain G A x l) (hu : u ∈ l) :
    ∃ l' : List V, IsAnchorChain G A u l' ∧ ∀ y ∈ l', y ∈ l := by
  obtain ⟨hne, hchain, -, hlast⟩ := h
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hu
  refine ⟨u :: t, ⟨List.cons_ne_nil u t,
    hchain.suffix (List.suffix_append s (u :: t)), rfl, ?_⟩, ?_⟩
  · rw [← List.getLast_append_of_right_ne_nil s (u :: t) (List.cons_ne_nil u t)]
    exact hlast
  · intro y hy
    exact List.mem_append.2 (Or.inr hy)

end Chains

/-! ### The canonical first anchor chain -/

section Selection

variable {V : Type*} [Countable V]

/-- A fixed enumeration of the countably many finite vertex lists. -/
noncomputable def chainEnum : ℕ → List V := (exists_surjective_nat (List V)).choose

theorem chainEnum_surjective : Function.Surjective (chainEnum : ℕ → List V) :=
  (exists_surjective_nat (List V)).choose_spec

open Classical in
/-- **The canonical anchor chain of `x`**: the first anchor chain of `x` in the fixed
enumeration `chainEnum` of all finite vertex lists. No measurable selection theorem and no
continuity in the data is used; the choice is a first-hitting index in a countable list. -/
noncomputable def firstAnchorChain (G : ReflectedWalk.ConductanceGraph V) (A : Set V)
    (x : V) : List V :=
  if h : ∃ n : ℕ, IsAnchorChain G A x (chainEnum n) then chainEnum (Nat.find h) else []

open Classical in
theorem firstAnchorChain_eq_chainEnum_find {G : ReflectedWalk.ConductanceGraph V}
    {A : Set V} {x : V} (h : ∃ n : ℕ, IsAnchorChain G A x (chainEnum n)) :
    firstAnchorChain G A x = chainEnum (Nat.find h) :=
  dif_pos h

/-- The enumerated form of the existence of an anchor chain. -/
theorem exists_index_isAnchorChain {G : ReflectedWalk.ConductanceGraph V} {A : Set V}
    {x : V} (hex : ∃ l : List V, IsAnchorChain G A x l) :
    ∃ n : ℕ, IsAnchorChain G A x (chainEnum n) := by
  obtain ⟨l, hl⟩ := hex
  obtain ⟨n, rfl⟩ := chainEnum_surjective l
  exact ⟨n, hl⟩

/-- **The canonical chain really is an anchor chain.** -/
theorem isAnchorChain_firstAnchorChain {G : ReflectedWalk.ConductanceGraph V} {A : Set V}
    {x : V} (hex : ∃ l : List V, IsAnchorChain G A x l) :
    IsAnchorChain G A x (firstAnchorChain G A x) := by
  classical
  have h : ∃ n : ℕ, IsAnchorChain G A x (chainEnum n) := exists_index_isAnchorChain hex
  rw [firstAnchorChain_eq_chainEnum_find h]
  exact Nat.find_spec h

/-- The starting vertex belongs to its own canonical chain. -/
theorem mem_firstAnchorChain {G : ReflectedWalk.ConductanceGraph V} {A : Set V} {x : V}
    (hex : ∃ l : List V, IsAnchorChain G A x l) : x ∈ firstAnchorChain G A x := by
  obtain ⟨hne, -, hhead, -⟩ := isAnchorChain_firstAnchorChain hex
  have hmem : (firstAnchorChain G A x).head hne ∈ firstAnchorChain G A x := List.head_mem hne
  rwa [hhead] at hmem

end Selection

/-! ### Measurability of the canonical chain in the environment -/

section MeasurableSelection

variable {V : Type*} {Ω : Type*} [MeasurableSpace Ω]

/-- A set defined by a condition not depending on the parameter is measurable. -/
theorem measurableSet_const_prop (p : Prop) : MeasurableSet {_ω : Ω | p} := by
  by_cases h : p
  · simp only [h, Set.setOf_true]
    exact MeasurableSet.univ
  · simp only [h, Set.setOf_false]
    exact MeasurableSet.empty

/-- **Fibres of a countably valued measurable map survive an arbitrary map.** -/
theorem measurableSet_fiber_comp {β γ : Type*} [Countable β] {F : Ω → β}
    (hF : ∀ b : β, MeasurableSet {ω | F ω = b}) (g : β → γ) (t : γ) :
    MeasurableSet {ω | g (F ω) = t} := by
  have hset : {ω | g (F ω) = t} = ⋃ b : {b : β // g b = t}, {ω | F ω = (b : β)} := by
    ext ω
    constructor
    · intro hω
      exact Set.mem_iUnion.2 ⟨⟨F ω, hω⟩, rfl⟩
    · intro hω
      obtain ⟨b, hb⟩ := Set.mem_iUnion.1 hω
      have hb' : F ω = (b : β) := hb
      rw [Set.mem_setOf_eq, hb']
      exact b.2
  rw [hset]
  exact MeasurableSet.iUnion fun b => hF (b : β)

/-- **Fibres of two countably valued measurable maps survive an arbitrary binary map.** -/
theorem measurableSet_fiber_comp₂ {β₁ β₂ γ : Type*} [Countable β₁] [Countable β₂]
    {F₁ : Ω → β₁} {F₂ : Ω → β₂}
    (h₁ : ∀ b : β₁, MeasurableSet {ω | F₁ ω = b})
    (h₂ : ∀ b : β₂, MeasurableSet {ω | F₂ ω = b}) (g : β₁ → β₂ → γ) (t : γ) :
    MeasurableSet {ω | g (F₁ ω) (F₂ ω) = t} := by
  have hset : {ω | g (F₁ ω) (F₂ ω) = t}
      = ⋃ b : {b : β₁ × β₂ // g b.1 b.2 = t},
          {ω | F₁ ω = (b : β₁ × β₂).1} ∩ {ω | F₂ ω = (b : β₁ × β₂).2} := by
    ext ω
    constructor
    · intro hω
      exact Set.mem_iUnion.2 ⟨⟨(F₁ ω, F₂ ω), hω⟩, ⟨rfl, rfl⟩⟩
    · intro hω
      obtain ⟨b, hb⟩ := Set.mem_iUnion.1 hω
      have hb1 : F₁ ω = (b : β₁ × β₂).1 := hb.1
      have hb2 : F₂ ω = (b : β₁ × β₂).2 := hb.2
      rw [Set.mem_setOf_eq, hb1, hb2]
      exact b.2
  rw [hset]
  exact MeasurableSet.iUnion fun b => (h₁ _).inter (h₂ _)

/-- **A fixed list is a chain of the environment graph on a measurable event.** -/
theorem measurableSet_isChain {G : Ω → ReflectedWalk.ConductanceGraph V}
    (hG : ∀ x y : V, Measurable fun ω => (G ω).c x y) (l : List V) :
    MeasurableSet {ω | l.IsChain (G ω).toSimpleGraph.Adj} := by
  induction l with
  | nil =>
      have hset : {ω : Ω | ([] : List V).IsChain (G ω).toSimpleGraph.Adj} = Set.univ := by
        ext ω
        simp [List.isChain_nil]
      rw [hset]
      exact MeasurableSet.univ
  | cons a t ih =>
      cases t with
      | nil =>
          have hset : {ω : Ω | [a].IsChain (G ω).toSimpleGraph.Adj} = Set.univ := by
            ext ω
            simp [List.isChain_singleton]
          rw [hset]
          exact MeasurableSet.univ
      | cons b t' =>
          have hset : {ω : Ω | (a :: b :: t').IsChain (G ω).toSimpleGraph.Adj}
              = {ω : Ω | (0 : ℝ) < (G ω).c a b}
                ∩ {ω : Ω | (b :: t').IsChain (G ω).toSimpleGraph.Adj} := by
            ext ω
            simp only [Set.mem_setOf_eq, Set.mem_inter_iff, List.isChain_cons_cons,
              ReflectedWalk.ConductanceGraph.toSimpleGraph_adj]
          rw [hset]
          exact (measurableSet_lt measurable_const (hG a b)).inter ih

/-- **A fixed list is an anchor chain of the environment on a measurable event.** -/
theorem measurableSet_isAnchorChain {G : Ω → ReflectedWalk.ConductanceGraph V}
    (hG : ∀ x y : V, Measurable fun ω => (G ω).c x y) {A : Ω → Set V}
    (hA : ∀ x : V, MeasurableSet {ω | x ∈ A ω}) (x : V) (l : List V) :
    MeasurableSet {ω | IsAnchorChain (G ω) (A ω) x l} := by
  by_cases hne : l = []
  · have hset : {ω : Ω | IsAnchorChain (G ω) (A ω) x l} = (∅ : Set Ω) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨h, -⟩
      exact h hne
    rw [hset]
    exact MeasurableSet.empty
  · by_cases hhead : l.head hne = x
    · have hset : {ω : Ω | IsAnchorChain (G ω) (A ω) x l}
          = {ω : Ω | l.IsChain (G ω).toSimpleGraph.Adj} ∩ {ω : Ω | l.getLast hne ∈ A ω} := by
        ext ω
        constructor
        · rintro ⟨hne', hchain, -, hlast⟩
          exact ⟨hchain, hlast⟩
        · rintro ⟨hchain, hlast⟩
          exact ⟨hne, hchain, hhead, hlast⟩
      rw [hset]
      exact (measurableSet_isChain hG l).inter (hA _)
    · have hset : {ω : Ω | IsAnchorChain (G ω) (A ω) x l} = (∅ : Set Ω) := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨hne', -, hh, -⟩
        exact hhead hh
      rw [hset]
      exact MeasurableSet.empty

variable [Countable V]

/-- **The canonical anchor chain is a measurable function of the environment.** Its fibres
are the first-hitting events of the countably many measurable events on which a fixed
enumerated list is an anchor chain. -/
theorem measurableSet_firstAnchorChain_eq {G : Ω → ReflectedWalk.ConductanceGraph V}
    (hG : ∀ x y : V, Measurable fun ω => (G ω).c x y) {A : Ω → Set V}
    (hA : ∀ x : V, MeasurableSet {ω | x ∈ A ω}) {x : V}
    (hex : ∀ ω : Ω, ∃ l : List V, IsAnchorChain (G ω) (A ω) x l) (c : List V) :
    MeasurableSet {ω | firstAnchorChain (G ω) (A ω) x = c} := by
  classical
  have hSmeas : ∀ n : ℕ,
      MeasurableSet {ω : Ω | IsAnchorChain (G ω) (A ω) x (chainEnum n)} := fun n =>
    measurableSet_isAnchorChain hG hA x (chainEnum n)
  have hexn : ∀ ω : Ω, ∃ n : ℕ, IsAnchorChain (G ω) (A ω) x (chainEnum n) := fun ω =>
    exists_index_isAnchorChain (hex ω)
  have hset : {ω | firstAnchorChain (G ω) (A ω) x = c}
      = ⋃ n : ℕ, (({ω : Ω | IsAnchorChain (G ω) (A ω) x (chainEnum n)}
            ∩ ⋂ m ∈ Set.Iio n, {ω : Ω | IsAnchorChain (G ω) (A ω) x (chainEnum m)}ᶜ)
          ∩ {_ω : Ω | chainEnum n = c}) := by
    ext ω
    constructor
    · intro hω
      refine Set.mem_iUnion.2 ⟨Nat.find (hexn ω), ⟨Nat.find_spec (hexn ω), ?_⟩, ?_⟩
      · refine Set.mem_iInter₂.2 fun m hm => Set.mem_compl ?_
        exact Nat.find_min (hexn ω) (Set.mem_Iio.1 hm)
      · show chainEnum (Nat.find (hexn ω)) = c
        rw [← firstAnchorChain_eq_chainEnum_find (hexn ω)]
        exact hω
    · intro hω
      obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hω
      obtain ⟨⟨hSn, hmin⟩, hcn⟩ := hn
      have hSn' : IsAnchorChain (G ω) (A ω) x (chainEnum n) := hSn
      have hminm : ∀ m : ℕ, m < n → ¬ IsAnchorChain (G ω) (A ω) x (chainEnum m) := by
        intro m hm
        have hc := Set.mem_iInter₂.1 hmin m (Set.mem_Iio.2 hm)
        exact (Set.mem_compl_iff _ _).1 hc
      have hfind : Nat.find (hexn ω) = n := by
        rcases lt_or_eq_of_le (Nat.find_min' (hexn ω) hSn') with hlt | heq
        · exact absurd (Nat.find_spec (hexn ω)) (hminm _ hlt)
        · exact heq
      show firstAnchorChain (G ω) (A ω) x = c
      rw [firstAnchorChain_eq_chainEnum_find (hexn ω), hfind]
      exact hcn
  rw [hset]
  refine MeasurableSet.iUnion fun n => MeasurableSet.inter ?_ (measurableSet_const_prop _)
  exact (hSmeas n).inter
    (MeasurableSet.biInter (Set.to_countable (Set.Iio n)) fun m _ => (hSmeas m).compl)

end MeasurableSelection

/-! ### The measurable anchored exhaustion -/

section Exhaustion

variable {V : Type*} [Countable V] [DecidableEq V]

/-- A fixed injective indexing of the countable vertex type. -/
noncomputable def vertexIndex : V → ℕ := (Countable.exists_injective_nat V).choose

theorem vertexIndex_injective : Function.Injective (vertexIndex : V → ℕ) :=
  (Countable.exists_injective_nat V).choose_spec

open Classical in
/-- The vertex of index `n`, if there is one. -/
noncomputable def seedFinset (n : ℕ) : Finset V :=
  if h : ∃ v : V, vertexIndex v = n then {h.choose} else ∅

/-- The finitely many vertices of index at most `n`. -/
noncomputable def seedUpTo (n : ℕ) : Finset V := (Finset.range (n + 1)).biUnion seedFinset

theorem mem_seedFinset_self (x : V) : x ∈ (seedFinset (vertexIndex x) : Finset V) := by
  classical
  have hex : ∃ v : V, vertexIndex v = vertexIndex x := ⟨x, rfl⟩
  have hchoose : hex.choose = x := vertexIndex_injective hex.choose_spec
  simp only [seedFinset]
  rw [dif_pos hex, Finset.mem_singleton]
  exact hchoose.symm

theorem mem_seedUpTo_self (x : V) : x ∈ (seedUpTo (vertexIndex x) : Finset V) :=
  Finset.mem_biUnion.2 ⟨vertexIndex x, Finset.self_mem_range_succ _, mem_seedFinset_self x⟩

theorem seedUpTo_mono : Monotone (seedUpTo : ℕ → Finset V) := by
  intro m n hmn
  refine Finset.biUnion_subset_biUnion_of_subset_left seedFinset ?_
  intro k hk
  rw [Finset.mem_range] at hk ⊢
  omega

/-- **The `n`-th level of the canonical anchored exhaustion**: the union of the canonical
anchor chains of the finitely many vertices of index at most `n`. -/
noncomputable def patchLevel (G : ReflectedWalk.ConductanceGraph V) (A : Set V) (n : ℕ) :
    Finset V :=
  (seedUpTo n).biUnion fun x => (firstAnchorChain G A x).toFinset

variable (G : ReflectedWalk.ConductanceGraph V) {A : Set V}

theorem patchLevel_mono : Monotone (patchLevel G A) := by
  intro m n hmn
  exact Finset.biUnion_subset_biUnion_of_subset_left _ (seedUpTo_mono hmn)

/-- **The levels exhaust the vertex type.** -/
theorem exists_mem_patchLevel (hex : ∀ x : V, ∃ l : List V, IsAnchorChain G A x l) (x : V) :
    ∃ n : ℕ, x ∈ patchLevel G A n := by
  refine ⟨vertexIndex x, Finset.mem_biUnion.2 ⟨x, mem_seedUpTo_self x, ?_⟩⟩
  exact List.mem_toFinset.2 (mem_firstAnchorChain (hex x))

/-- **Every level is anchored.** A vertex of a level lies on the canonical chain of some
seed vertex, and the suffix of that chain from it is an anchor chain inside the same
level. -/
theorem boundaryAnchored_patchLevel
    (hex : ∀ x : V, ∃ l : List V, IsAnchorChain G A x l) (n : ℕ) :
    BoundaryAnchored (restrictGraph G ((patchLevel G A n : Finset V) : Set V))
      (inducedAnchorSet A ((patchLevel G A n : Finset V) : Set V)) := by
  refine boundaryAnchored_restrictGraph_of_walks_within G ?_
  intro u hu
  obtain ⟨x, hx, hux⟩ := Finset.mem_biUnion.1 (Finset.mem_coe.1 hu)
  have hulist : u ∈ firstAnchorChain G A x := List.mem_toFinset.1 hux
  obtain ⟨l', hl', hsub⟩ :=
    exists_isAnchorChain_subset_of_mem G (isAnchorChain_firstAnchorChain (hex x)) hulist
  refine exists_walk_of_isAnchorChain G hl' ?_
  intro y hy
  refine Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨x, hx, ?_⟩)
  exact List.mem_toFinset.2 (hsub y hy)

end Exhaustion

section MeasurableExhaustion

variable {V : Type*} [Countable V] [DecidableEq V] {Ω : Type*} [MeasurableSpace Ω]

/-- A finite union of measurably varying finite sets is measurably varying. -/
theorem measurableSet_biUnion_eq {H : Ω → V → Finset V}
    (hH : ∀ (x : V) (t : Finset V), MeasurableSet {ω | H ω x = t}) (K : Finset V) :
    ∀ t : Finset V, MeasurableSet {ω | K.biUnion (H ω) = t} := by
  classical
  refine Finset.induction_on K ?_ ?_
  · intro t
    have hset : {ω : Ω | (∅ : Finset V).biUnion (H ω) = t} = {_ω : Ω | (∅ : Finset V) = t} := by
      ext ω
      simp only [Set.mem_setOf_eq, Finset.biUnion_empty]
    rw [hset]
    exact measurableSet_const_prop _
  · intro a K' _ ih t
    have hset : {ω : Ω | (insert a K').biUnion (H ω) = t}
        = {ω : Ω | (fun s₁ s₂ : Finset V => s₁ ∪ s₂) (H ω a) (K'.biUnion (H ω)) = t} := by
      ext ω
      simp only [Set.mem_setOf_eq, Finset.biUnion_insert]
    rw [hset]
    exact measurableSet_fiber_comp₂ (hH a) ih (fun s₁ s₂ => s₁ ∪ s₂) t

/-- **The canonical exhaustion is measurable in the environment.** -/
theorem measurableSet_patchLevel_eq {G : Ω → ReflectedWalk.ConductanceGraph V}
    (hG : ∀ x y : V, Measurable fun ω => (G ω).c x y) {A : Ω → Set V}
    (hA : ∀ x : V, MeasurableSet {ω | x ∈ A ω})
    (hex : ∀ (ω : Ω) (x : V), ∃ l : List V, IsAnchorChain (G ω) (A ω) x l)
    (n : ℕ) (t : Finset V) :
    MeasurableSet {ω | patchLevel (G ω) (A ω) n = t} := by
  refine measurableSet_biUnion_eq
    (H := fun ω x => (firstAnchorChain (G ω) (A ω) x).toFinset) ?_ (seedUpTo n) t
  intro x s
  exact measurableSet_fiber_comp
    (measurableSet_firstAnchorChain_eq hG hA (fun ω => hex ω x)) List.toFinset s

end MeasurableExhaustion

/-! ### The measurable full-energy anchored minimizer -/

section Minimizer

variable {V : Type*} [Countable V] [DecidableEq V] {Ω : Type*} [MeasurableSpace Ω]

/-- **A measurable full-energy anchored minimizer on a possibly infinite patch.**

For conductance data, a boundary set and reference values depending measurably on the
environment, with each environment graph anchored at its boundary set and each reference
field of finite energy, there is a *measurable* field of functions which, at **every**
environment, has finite energy, agrees with the reference field on the whole boundary set,
and minimizes the **full** Dirichlet energy among all finite-energy functions with those
boundary values.

The patch may be infinite and disconnected, the boundary set may be infinite, and no
finiteness of the number of spatial cells is assumed. The construction is the canonical
measurable anchored exhaustion `patchLevel` together with the varying-block minimizers of
`MeasurableBlockMinimizer.exists_measurable_varying_block_minimizer_anchorSet` and the
pointwise limit of
`FiniteMinimizerPointwiseConvergence.exists_tendsto_pointwise_anchored_minimizer`. -/
theorem exists_measurable_anchored_energy_minimizer
    {G : Ω → ReflectedWalk.ConductanceGraph V}
    (hG : ∀ x y : V, Measurable fun ω => (G ω).c x y)
    {A : Ω → Set V} (hA : ∀ x : V, MeasurableSet {ω | x ∈ A ω})
    (hanchor : ∀ ω : Ω, BoundaryAnchored (G ω) (A ω))
    {u : Ω → V → ℝ} (hu : ∀ x : V, Measurable fun ω => u ω x)
    (huE : ∀ ω : Ω, (G ω).HasFiniteEnergy (u ω)) :
    ∃ f : Ω → V → ℝ, Measurable f ∧ (∀ x : V, Measurable fun ω => f ω x) ∧
      ∀ ω : Ω,
        (G ω).HasFiniteEnergy (f ω) ∧
        (∀ a ∈ A ω, f ω a = u ω a) ∧
        (∀ w : V → ℝ, (G ω).HasFiniteEnergy w → (∀ a ∈ A ω, w a = u ω a) →
          (G ω).Energy (f ω) ≤ (G ω).Energy w) := by
  classical
  have hex : ∀ (ω : Ω) (x : V), ∃ l : List V, IsAnchorChain (G ω) (A ω) x l :=
    fun ω x => exists_isAnchorChain (G ω) (hanchor ω) x
  have hLfib : ∀ (n : ℕ) (t : Finset V),
      MeasurableSet {ω | patchLevel (G ω) (A ω) n = t} :=
    fun n t => measurableSet_patchLevel_eq hG hA hex n t
  have hLanch : ∀ (ω : Ω) (n : ℕ),
      BoundaryAnchored
        (restrictGraph (G ω) ((patchLevel (G ω) (A ω) n : Finset V) : Set V))
        (inducedAnchorSet (A ω) ((patchLevel (G ω) (A ω) n : Finset V) : Set V)) :=
    fun ω n => boundaryAnchored_patchLevel (G ω) (fun x => hex ω x) n
  have hLmono : ∀ ω : Ω, Monotone fun n => patchLevel (G ω) (A ω) n :=
    fun ω => patchLevel_mono (G ω)
  have hLcover : ∀ (ω : Ω) (x : V), ∃ n : ℕ, x ∈ patchLevel (G ω) (A ω) n :=
    fun ω x => exists_mem_patchLevel (G ω) (fun y => hex ω y) x
  have hstep : ∀ n : ℕ, ∃ F : Ω → V → ℝ, (∀ x : V, Measurable fun ω => F ω x) ∧
      ∀ ω : Ω,
        (∀ a ∈ A ω, a ∈ patchLevel (G ω) (A ω) n → F ω a = u ω a) ∧
        (∀ w : V → ℝ, (∀ a ∈ A ω, a ∈ patchLevel (G ω) (A ω) n → w a = u ω a) →
          restrictedEnergy (G ω) ((patchLevel (G ω) (A ω) n : Finset V) : Set V) (F ω)
            ≤ restrictedEnergy (G ω)
                ((patchLevel (G ω) (A ω) n : Finset V) : Set V) w) := by
    intro n
    obtain ⟨F, -, hFeval, hF⟩ :=
      MeasurableBlockMinimizer.exists_measurable_varying_block_minimizer_anchorSet
        (G := G) hG (S := fun ω => patchLevel (G ω) (A ω) n) (fun s => hLfib n s)
        (A := A) hA (fun ω => hLanch ω n) hu
    exact ⟨F, hFeval, fun ω => ⟨(hF ω).1, (hF ω).2.2.1⟩⟩
  choose F hFmeas hF using hstep
  have hlim : ∀ ω : Ω, ∃ g : V → ℝ,
      (∀ x : V, Tendsto (fun n => F n ω x) atTop (𝓝 (g x))) ∧
      (G ω).HasFiniteEnergy g ∧ (∀ a ∈ A ω, g a = u ω a) ∧
      ∀ w : V → ℝ, (G ω).HasFiniteEnergy w → (∀ a ∈ A ω, w a = u ω a) →
        (G ω).Energy g ≤ (G ω).Energy w := by
    intro ω
    exact FiniteMinimizerPointwiseConvergence.exists_tendsto_pointwise_anchored_minimizer
      (G ω) (A := A ω) (u := u ω) (L := fun n => patchLevel (G ω) (A ω) n)
      (F := fun n => F n ω) (hanchor ω) (huE ω) (hLmono ω) (hLcover ω)
      (fun n => (hF n ω).1) (fun n => (hF n ω).2)
  choose g hgconv hgE hgtrace hgmin using hlim
  have hgmeas : ∀ x : V, Measurable fun ω => g ω x := by
    intro x
    refine measurable_of_tendsto_metrizable (f := fun n ω => F n ω x)
      (fun n => hFmeas n x) ?_
    exact tendsto_pi_nhds.2 fun ω => hgconv ω x
  exact ⟨g, Measurable.of_eval hgmeas, hgmeas,
    fun ω => ⟨hgE ω, hgtrace ω, hgmin ω⟩⟩

end Minimizer

end MeasurableInfinitePatchMinimizer

end ReflectedGMS
