/-
The zero-one law for the existence of an infinite open cluster, for site and bond
percolation on a countable graph with independent states.

Let `G` be a simple graph on a countable vertex set `V`.

* Site percolation.  A configuration is `ω : V → Bool`, a vertex `v` being open when
  `ω v = true`.  The open cluster `siteCluster G ω x` of `x` is empty when `x` is closed, and
  otherwise is the set of vertices joined to `x` by a path of `G` through open vertices; it is
  the component of `x` in the subgraph induced by the open vertices
  (`mem_siteCluster_iff_reachable`).
* Bond percolation.  A configuration is `ω : Sym2 V → Bool`, an edge `s(x, y)` of `G` being
  open when `ω s(x, y) = true`.  The open cluster `bondCluster G ω x` of `x` is the set of
  vertices joined to `x` by a path of open edges.

Results.

* The events `siteExistsInfinite G` and `bondExistsInfinite G` that some open cluster is
  infinite are measurable.
* Changing a configuration at finitely many coordinates does not change these events; for site
  percolation this uses that every vertex has finitely many neighbours.
* Hence, by the Kolmogorov zero-one law in its finite-alteration form
  (`OAI.CriticalZ3.zero_one_of_finite_alteration`), under every law with independent
  coordinates, for instance every product `Measure.infinitePi ν` of probability measures on
  `Bool`, each event has probability `0` or `1`, and it has probability `1` as soon as the
  open cluster of one vertex is infinite with positive probability.
* On `ℤ^d` with the nearest-neighbour graph `lattice d`, the site event is
  `HasInfiniteComponent {v | ω v = true}` (`hasInfiniteComponent_iff_mem_siteExistsInfinite`).

The arguments are those given for `ℤ^3` in OpenAI's math repository
(https://github.com/openai/math, commit 4eaee875, file lean/OAI/Probability/CriticalZ3/Basic.lean,
Apache License 2.0; copied in `LatticeProb.OpenAI.Probability.CriticalZ3.Basic`), written here
for a general graph and a general law with independent coordinates.
-/
import Mathlib
import LatticeProb.Site
import LatticeProb.OpenAI.Probability.CriticalZ3.Basic

namespace LatticeProb

namespace GraphPercolation

open MeasureTheory ProbabilityTheory

variable {V : Type*} (G : SimpleGraph V)

/-! ### Site percolation -/

/-- Two vertices are joined by an open step of site percolation: they are adjacent in `G`
and both are open. -/
def SiteOpenAdj (ω : V → Bool) (x y : V) : Prop :=
  G.Adj x y ∧ ω x = true ∧ ω y = true

/-- The open cluster of `x` in site percolation: empty when `x` is closed, and otherwise the
vertices joined to `x` by a path of `G` through open vertices. -/
def siteCluster (ω : V → Bool) (x : V) : Set V :=
  {y | ω x = true ∧ Relation.ReflTransGen (SiteOpenAdj G ω) x y}

/-- The event that some open cluster of site percolation is infinite. -/
def siteExistsInfinite : Set (V → Bool) :=
  {ω | ∃ x, (siteCluster G ω x).Infinite}

theorem measurableSet_siteOpenAdj (x y : V) :
    MeasurableSet {ω : V → Bool | SiteOpenAdj G ω x y} :=
  (MeasurableSet.const _).inter
    ((measurableSet_eq_fun (measurable_pi_apply x) measurable_const).inter
      (measurableSet_eq_fun (measurable_pi_apply y) measurable_const))

theorem measurableSet_mem_siteCluster [Countable V] (x y : V) :
    MeasurableSet {ω : V → Bool | y ∈ siteCluster G ω x} :=
  (measurableSet_eq_fun (measurable_pi_apply x) measurable_const).inter
    (OAI.CriticalZ3.measurableSet_rtg (fun ω => SiteOpenAdj G ω) (measurableSet_siteOpenAdj G) x y)

theorem measurableSet_siteCluster_infinite [Countable V] (x : V) :
    MeasurableSet {ω : V → Bool | (siteCluster G ω x).Infinite} :=
  OAI.CriticalZ3.measurableSet_infinite_fiber (fun ω y => y ∈ siteCluster G ω x)
    (measurableSet_mem_siteCluster G x)

theorem measurableSet_siteExistsInfinite [Countable V] :
    MeasurableSet (siteExistsInfinite G) := by
  have h : siteExistsInfinite G = ⋃ x, {ω : V → Bool | (siteCluster G ω x).Infinite} :=
    Set.ext fun ω => by simp only [siteExistsInfinite, Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [h]
  exact MeasurableSet.iUnion fun x => measurableSet_siteCluster_infinite G x

theorem siteRtg_from_closed {ω : V → Bool} {x y : V} (hx : ω x ≠ true)
    (h : Relation.ReflTransGen (SiteOpenAdj G ω) x y) : y = x := by
  induction h with
  | refl => rfl
  | @tail a b _ hab ih => exact (hx (ih ▸ hab.2.1)).elim

theorem siteCluster_infinite_iff (ω : V → Bool) (x : V) :
    (siteCluster G ω x).Infinite ↔
      {y | Relation.ReflTransGen (SiteOpenAdj G ω) x y}.Infinite := by
  by_cases hx : ω x = true
  · simp only [siteCluster, hx, true_and]
  · have he : {y | Relation.ReflTransGen (SiteOpenAdj G ω) x y} = {x} := by
      ext y
      exact ⟨siteRtg_from_closed G hx,
        fun hy => by rw [Set.mem_singleton_iff.mp hy]; exact .refl⟩
    simp [siteCluster, hx, he]

/-- The open cluster of an open vertex `x` is its component in the subgraph of `G` induced by
the open vertices. -/
theorem mem_siteCluster_iff_reachable {ω : V → Bool} {x y : V} (hx : ω x = true) :
    y ∈ siteCluster G ω x ↔
      ∃ hy : ω y = true, (G.induce {v | ω v = true}).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  constructor
  · rintro ⟨-, h⟩
    induction h with
    | refl => exact ⟨hx, SimpleGraph.Reachable.rfl⟩
    | @tail a b _ hab ih =>
      obtain ⟨ha, hr⟩ := ih
      exact ⟨hab.2.2, hr.trans (SimpleGraph.Adj.reachable
        (G := G.induce {v | ω v = true}) (u := ⟨a, ha⟩) (v := ⟨b, hab.2.2⟩) hab.1)⟩
  · rintro ⟨hy, hr⟩
    refine ⟨hx, ?_⟩
    exact ((SimpleGraph.reachable_iff_reflTransGen _ _).mp hr).lift Subtype.val
      (fun a b h => ⟨h, a.2, b.2⟩)

/-- On a locally finite graph, the event that some open cluster of site percolation is
infinite is not changed by altering the configuration at finitely many vertices. -/
theorem siteExistsInfinite_of_finite_alteration (hG : ∀ x, (G.neighborSet x).Finite)
    {ω ω' : V → Bool} (J : Finset V) (hagree : ∀ v ∉ J, ω' v = ω v)
    (hω : ω ∈ siteExistsInfinite G) : ω' ∈ siteExistsInfinite G := by
  classical
  let F : Set V := (J : Set V) ∪ ⋃ x ∈ (J : Set V), G.neighborSet x
  have hF : F.Finite := J.finite_toSet.union (J.finite_toSet.biUnion fun x _ => hG x)
  have hh : ∀ a b, SiteOpenAdj G ω a b → SiteOpenAdj G ω' a b ∨ b ∈ F := by
    intro a b hab
    by_cases ha : a ∈ J
    · exact Or.inr (Or.inr (Set.mem_iUnion₂.mpr ⟨a, ha, hab.1⟩))
    by_cases hb : b ∈ J
    · exact Or.inr (Or.inl hb)
    · exact Or.inl ⟨hab.1, (hagree a ha).trans hab.2.1, (hagree b hb).trans hab.2.2⟩
  obtain ⟨x, hx⟩ := hω
  obtain ⟨y, hy⟩ := OAI.CriticalZ3.infinite_component_of_perturbation hF hh
    ⟨x, (siteCluster_infinite_iff G ω x).mp hx⟩
  exact ⟨y, (siteCluster_infinite_iff G ω' y).mpr hy⟩

theorem siteExistsInfinite_finite_alteration (hG : ∀ x, (G.neighborSet x).Finite)
    {ω ω' : V → Bool} (J : Finset V) (hagree : ∀ v ∉ J, ω' v = ω v) :
    ω' ∈ siteExistsInfinite G ↔ ω ∈ siteExistsInfinite G :=
  ⟨siteExistsInfinite_of_finite_alteration G hG J fun v hv => (hagree v hv).symm,
    siteExistsInfinite_of_finite_alteration G hG J hagree⟩

/-- **Zero-one law for site percolation.** On a countable locally finite graph, under any law
with independent coordinates, the event that some open cluster is infinite has probability
`0` or `1`. -/
theorem siteExistsInfinite_zero_one [Countable V] (hG : ∀ x, (G.neighborSet x).Finite)
    (μ : Measure (V → Bool)) (hi : iIndepFun (fun v (ω : V → Bool) => ω v) μ) :
    μ (siteExistsInfinite G) = 0 ∨ μ (siteExistsInfinite G) = 1 :=
  OAI.CriticalZ3.zero_one_of_finite_alteration μ hi _ (measurableSet_siteExistsInfinite G)
    fun J _ _ h => siteExistsInfinite_finite_alteration G hG J h

/-- If the open cluster of one vertex is infinite with positive probability, then almost
surely some open cluster is infinite. -/
theorem siteExistsInfinite_eq_one [Countable V] (hG : ∀ x, (G.neighborSet x).Finite)
    (μ : Measure (V → Bool)) (hi : iIndepFun (fun v (ω : V → Bool) => ω v) μ) {x : V}
    (hx : 0 < μ {ω | (siteCluster G ω x).Infinite}) : μ (siteExistsInfinite G) = 1 :=
  (siteExistsInfinite_zero_one G hG μ hi).resolve_left
    (ne_of_gt (hx.trans_le (measure_mono fun _ h => ⟨x, h⟩)))

/-- The zero-one law for site percolation under a product of probability measures on
`Bool`, for instance Bernoulli site percolation. -/
theorem siteExistsInfinite_infinitePi_zero_one [Countable V]
    (hG : ∀ x, (G.neighborSet x).Finite) (ν : V → Measure Bool)
    [∀ v, IsProbabilityMeasure (ν v)] :
    Measure.infinitePi ν (siteExistsInfinite G) = 0 ∨
      Measure.infinitePi ν (siteExistsInfinite G) = 1 :=
  siteExistsInfinite_zero_one G hG _
    (iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id))

/-! ### Bond percolation -/

/-- Two vertices are joined by an open edge of bond percolation. -/
def BondOpenAdj (ω : Sym2 V → Bool) (x y : V) : Prop :=
  G.Adj x y ∧ ω s(x, y) = true

/-- The open cluster of `x` in bond percolation. -/
def bondCluster (ω : Sym2 V → Bool) (x : V) : Set V :=
  {y | Relation.ReflTransGen (BondOpenAdj G ω) x y}

/-- The event that some open cluster of bond percolation is infinite. -/
def bondExistsInfinite : Set (Sym2 V → Bool) :=
  {ω | ∃ x, (bondCluster G ω x).Infinite}

theorem measurableSet_bondOpenAdj (x y : V) :
    MeasurableSet {ω : Sym2 V → Bool | BondOpenAdj G ω x y} :=
  (MeasurableSet.const _).inter
    (measurableSet_eq_fun (measurable_pi_apply s(x, y)) measurable_const)

theorem measurableSet_mem_bondCluster [Countable V] (x y : V) :
    MeasurableSet {ω : Sym2 V → Bool | y ∈ bondCluster G ω x} :=
  OAI.CriticalZ3.measurableSet_rtg (fun ω => BondOpenAdj G ω) (measurableSet_bondOpenAdj G) x y

theorem measurableSet_bondCluster_infinite [Countable V] (x : V) :
    MeasurableSet {ω : Sym2 V → Bool | (bondCluster G ω x).Infinite} :=
  OAI.CriticalZ3.measurableSet_infinite_fiber (fun ω y => y ∈ bondCluster G ω x)
    (measurableSet_mem_bondCluster G x)

theorem measurableSet_bondExistsInfinite [Countable V] :
    MeasurableSet (bondExistsInfinite G) := by
  have h : bondExistsInfinite G = ⋃ x, {ω : Sym2 V → Bool | (bondCluster G ω x).Infinite} :=
    Set.ext fun ω => by simp only [bondExistsInfinite, Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [h]
  exact MeasurableSet.iUnion fun x => measurableSet_bondCluster_infinite G x

/-- The event that some open cluster of bond percolation is infinite is not changed by
altering the configuration at finitely many edges. -/
theorem bondExistsInfinite_of_finite_alteration {ω ω' : Sym2 V → Bool} (J : Finset (Sym2 V))
    (hagree : ∀ e ∉ J, ω' e = ω e) (hω : ω ∈ bondExistsInfinite G) :
    ω' ∈ bondExistsInfinite G := by
  classical
  let F : Set V := (fun e : Sym2 V => (Quot.out e : V × V).1) '' (J : Set (Sym2 V)) ∪
    (fun e : Sym2 V => (Quot.out e : V × V).2) '' (J : Set (Sym2 V))
  have hF : F.Finite := (J.finite_toSet.image _).union (J.finite_toSet.image _)
  have key : ∀ a b : V, s(a, b) ∈ J → b ∈ F := by
    intro a b hab
    have hq : s((Quot.out (s(a, b) : Sym2 V) : V × V).1, (Quot.out (s(a, b) : Sym2 V)).2) =
        s(a, b) := Quot.out_eq _
    rcases Sym2.eq_iff.mp hq with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact Or.inr ⟨s(a, b), hab, h2⟩
    · exact Or.inl ⟨s(a, b), hab, h1⟩
  apply OAI.CriticalZ3.infinite_component_of_perturbation hF (r := BondOpenAdj G ω)
    (s := BondOpenAdj G ω') _ hω
  intro a b hab
  by_cases hj : s(a, b) ∈ J
  · exact Or.inr (key a b hj)
  · exact Or.inl ⟨hab.1, (hagree _ hj).trans hab.2⟩

theorem bondExistsInfinite_finite_alteration {ω ω' : Sym2 V → Bool} (J : Finset (Sym2 V))
    (hagree : ∀ e ∉ J, ω' e = ω e) :
    ω' ∈ bondExistsInfinite G ↔ ω ∈ bondExistsInfinite G :=
  ⟨bondExistsInfinite_of_finite_alteration G J fun e he => (hagree e he).symm,
    bondExistsInfinite_of_finite_alteration G J hagree⟩

/-- **Zero-one law for bond percolation.** On a countable graph, under any law with
independent coordinates, the event that some open cluster is infinite has probability `0`
or `1`. -/
theorem bondExistsInfinite_zero_one [Countable V] (μ : Measure (Sym2 V → Bool))
    (hi : iIndepFun (fun e (ω : Sym2 V → Bool) => ω e) μ) :
    μ (bondExistsInfinite G) = 0 ∨ μ (bondExistsInfinite G) = 1 :=
  OAI.CriticalZ3.zero_one_of_finite_alteration μ hi _ (measurableSet_bondExistsInfinite G)
    fun J _ _ h => bondExistsInfinite_finite_alteration G J h

/-- If the open cluster of one vertex is infinite with positive probability, then almost
surely some open cluster is infinite. -/
theorem bondExistsInfinite_eq_one [Countable V] (μ : Measure (Sym2 V → Bool))
    (hi : iIndepFun (fun e (ω : Sym2 V → Bool) => ω e) μ) {x : V}
    (hx : 0 < μ {ω | (bondCluster G ω x).Infinite}) : μ (bondExistsInfinite G) = 1 :=
  (bondExistsInfinite_zero_one G μ hi).resolve_left
    (ne_of_gt (hx.trans_le (measure_mono fun _ h => ⟨x, h⟩)))

/-- The zero-one law for bond percolation under a product of probability measures on
`Bool`, for instance Bernoulli bond percolation. -/
theorem bondExistsInfinite_infinitePi_zero_one [Countable V] (ν : Sym2 V → Measure Bool)
    [∀ e, IsProbabilityMeasure (ν e)] :
    Measure.infinitePi ν (bondExistsInfinite G) = 0 ∨
      Measure.infinitePi ν (bondExistsInfinite G) = 1 :=
  bondExistsInfinite_zero_one G _
    (iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id))

/-! ### Site percolation on `ℤ^d` -/

/-- Every site of `ℤ^d` has finitely many nearest neighbours. -/
theorem lattice_neighborSet_finite {d : ℕ} (x : Site d) : ((lattice d).neighborSet x).Finite := by
  refine (nbrFinset x).finite_toSet.subset ?_
  rintro y ⟨i, hi | hi⟩
  · exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simp [hi]⟩)
  · exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ _, by simp [eq_sub_of_add_eq hi.symm]⟩)

/-- The open cluster of an open site of `ℤ^d` is its component among the open sites. -/
theorem componentIn_eq_siteCluster {d : ℕ} (ω : Site d → Bool) {x : Site d} (hx : ω x = true) :
    componentIn {v | ω v = true} x = siteCluster (lattice d) ω x := by
  ext y
  rw [mem_siteCluster_iff_reachable _ hx]
  exact ⟨fun ⟨_, hy, h⟩ => ⟨hy, h⟩, fun ⟨hy, h⟩ => ⟨hx, hy, h⟩⟩

theorem hasInfiniteComponent_iff_mem_siteExistsInfinite {d : ℕ} (ω : Site d → Bool) :
    HasInfiniteComponent {v | ω v = true} ↔ ω ∈ siteExistsInfinite (lattice d) := by
  constructor
  · rintro ⟨x, hx, hinf⟩
    exact ⟨x, componentIn_eq_siteCluster ω hx ▸ hinf⟩
  · rintro ⟨x, hinf⟩
    have hx : ω x = true := by
      by_contra hx
      exact hinf (Set.finite_empty.subset fun _ hy => absurd hy.1 hx)
    exact ⟨x, hx, (componentIn_eq_siteCluster ω hx).symm ▸ hinf⟩

theorem measurableSet_hasInfiniteComponent (d : ℕ) :
    MeasurableSet {ω : Site d → Bool | HasInfiniteComponent {v | ω v = true}} := by
  have h : {ω : Site d → Bool | HasInfiniteComponent {v | ω v = true}} =
      siteExistsInfinite (lattice d) :=
    Set.ext fun ω => hasInfiniteComponent_iff_mem_siteExistsInfinite ω
  rw [h]
  exact measurableSet_siteExistsInfinite _

/-- **Zero-one law for site percolation on `ℤ^d`.** Under any law with independent
coordinates, the set of open sites has an infinite component with probability `0` or `1`. -/
theorem hasInfiniteComponent_zero_one (d : ℕ) (μ : Measure (Site d → Bool))
    (hi : iIndepFun (fun v (ω : Site d → Bool) => ω v) μ) :
    μ {ω | HasInfiniteComponent {v | ω v = true}} = 0 ∨
      μ {ω | HasInfiniteComponent {v | ω v = true}} = 1 := by
  have h : {ω : Site d → Bool | HasInfiniteComponent {v | ω v = true}} =
      siteExistsInfinite (lattice d) :=
    Set.ext fun ω => hasInfiniteComponent_iff_mem_siteExistsInfinite ω
  rw [h]
  exact siteExistsInfinite_zero_one _ lattice_neighborSet_finite μ hi

end GraphPercolation

end LatticeProb
