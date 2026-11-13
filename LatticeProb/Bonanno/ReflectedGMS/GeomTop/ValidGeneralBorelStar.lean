/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.GeomTop.ValidGeneralBorelStar at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Environment.GeneralGeometry
import LatticeProb.Bonanno.ReflectedGMS.Environment.GenericLines
import LatticeProb.Bonanno.ReflectedGMS.GMS.LineConnectedPoint
import Mathlib.Util.AssertNoSorry

/-!
# The canonical singular set of a general cell configuration

For a cell configuration `C` (`CellConfiguration`, no hypotheses) let

* `accSet C` — points every neighbourhood of which meets infinitely many cells;
* `uncSet C` — points lying in no cell;
* `badSet C` — points `z` whose point graph `H({z})` is not (pre)connected;
* `starSet C := closure (accSet C ∪ uncSet C ∪ badSet C)`.

**Characterization** (`exists_singularSet_iff`): the existential clause of `GeneralGeometry`,
`∃ S : SingularSet C, C.LineConnectedOff S.sing` (Definition 1.1(ii) with (LCS) for the same
witness), holds iff `μH[1] (starSet C) = 0`.

* (⇒) every witness `S` is closed and contains the three sets: `accSet` by local finiteness off `S`,
  `uncSet` by the covering clause, and `badSet` because a short horizontal segment through a point
  `z ∉ S` avoids `S` and meets exactly the cells containing `z` (manuscript,
  `work/general/manuscript-text.txt` lines 70–73).  Hence `starSet C ⊆ S`.
* (⇐) `starSet C` itself is a witness; (LCS) off it holds because along a compact segment avoiding
  it only finitely many cells are involved and every point has a connected cell set, so the finite
  closed cover of the segment chains (the argument of
  `GMS.CellConfig.inducedGraph_connected_of_isCompact`).
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology Metric

namespace ReflectedGMS.GeomTop.ValidBorel

variable {V : Type*} (C : CellConfiguration V)

/-- Points no neighbourhood of which meets only finitely many cells. -/
def accSet : Set Plane := {z | ¬ ∃ U ∈ 𝓝 z, {v | C.Hits U v}.Finite}

/-- Points covered by no cell. -/
def uncSet : Set Plane := (⋃ v, (C.cell v : Set Plane))ᶜ

/-- Points whose point graph `H({z})` is not connected. -/
def badSet : Set Plane := {z | ¬ C.InducedConnected {z}}

/-- **The canonical singular set**: the closure of the accumulation, uncovered and bad points. -/
def starSet : Set Plane := closure (accSet C ∪ uncSet C ∪ badSet C)

variable {C}

theorem isClosed_starSet : IsClosed (starSet C) := isClosed_closure

theorem subset_starSet : accSet C ∪ uncSet C ∪ badSet C ⊆ starSet C := subset_closure

/-- Near a point with a neighbourhood meeting finitely many cells, a small closed ball meets only
the cells containing the point. -/
theorem exists_pos_closedBall_hits_imp_mem {z : Plane} (hz : z ∉ accSet C) :
    ∃ δ > 0, ∀ v, C.Hits (closedBall z δ) v → z ∈ (C.cell v : Set Plane) := by
  have hz' : ∃ U ∈ 𝓝 z, {v | C.Hits U v}.Finite := not_not.1 hz
  obtain ⟨U, hU, hfin⟩ := hz'
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
  have hFfin : {v | C.Hits U v ∧ z ∉ (C.cell v : Set Plane)}.Finite :=
    hfin.subset fun v hv => hv.1
  have hclosed : IsClosed (⋃ v ∈ {v | C.Hits U v ∧ z ∉ (C.cell v : Set Plane)},
      (C.cell v : Set Plane)) :=
    hFfin.isClosed_biUnion fun v _ => (C.cell v).isCompact.isClosed
  have hzn : z ∉ ⋃ v ∈ {v | C.Hits U v ∧ z ∉ (C.cell v : Set Plane)},
      (C.cell v : Set Plane) := by
    simp only [Set.mem_iUnion]
    rintro ⟨v, hv, hzv⟩
    exact hv.2 hzv
  obtain ⟨δ', hδ', hball⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl z hzn
  refine ⟨min ε δ' / 2, half_pos (lt_min hε hδ'), ?_⟩
  rintro v ⟨w, hwv, hw⟩
  by_contra hzv
  have hwz : dist w z ≤ min ε δ' / 2 := Metric.mem_closedBall.mp hw
  have hmin : min ε δ' / 2 < min ε δ' := half_lt_self (lt_min hε hδ')
  have hwε : w ∈ Metric.ball z ε := Metric.mem_ball.mpr
    (lt_of_le_of_lt hwz (lt_of_lt_of_le hmin (min_le_left _ _)))
  have hwδ : w ∈ Metric.ball z δ' := Metric.mem_ball.mpr
    (lt_of_le_of_lt hwz (lt_of_lt_of_le hmin (min_le_right _ _)))
  have hvU : C.Hits U v := ⟨w, hwv, hεU hwε⟩
  exact hball hwδ (Set.mem_biUnion (x := v) ⟨hvU, hzv⟩ hwv)

/-- Local finiteness plus compactness: only finitely many cells meet a compact set of
non-accumulation points. -/
theorem finite_hits_of_isCompact {L : Set Plane} (hc : IsCompact L)
    (hL : ∀ z ∈ L, z ∉ accSet C) : {v | C.Hits L v}.Finite := by
  have h' : ∀ z ∈ L, ∃ U ∈ 𝓝 z, {v | C.Hits U v}.Finite := fun z hz => not_not.1 (hL z hz)
  choose! U hU hfin using h'
  obtain ⟨t, htL, hcov⟩ := hc.elim_nhds_subcover U hU
  refine (t.finite_toSet.biUnion fun x hx => hfin x (htL x hx)).subset ?_
  rintro v ⟨p, hpv, hpL⟩
  obtain ⟨x, hx, hpx⟩ := Set.mem_iUnion₂.1 (hcov hpL)
  exact Set.mem_biUnion hx ⟨p, hpv, hpx⟩

/-- A non-accumulation point every neighbourhood of which meets a cell is covered: the finitely
many cells near it form a closed union. -/
theorem mem_iUnion_cell_of_notMem_accSet {z : Plane} (hz : z ∉ accSet C)
    (h : ∀ W ∈ 𝓝 z, ∃ v, C.Hits W v) : z ∈ ⋃ v, (C.cell v : Set Plane) := by
  have hz' : ∃ U ∈ 𝓝 z, {v | C.Hits U v}.Finite := not_not.1 hz
  obtain ⟨U, hU, hfin⟩ := hz'
  by_contra hzn
  have hclosed : IsClosed (⋃ v ∈ {v | C.Hits U v}, (C.cell v : Set Plane)) :=
    hfin.isClosed_biUnion fun v _ => (C.cell v).isCompact.isClosed
  have hzF : z ∉ ⋃ v ∈ {v | C.Hits U v}, (C.cell v : Set Plane) := by
    intro hzF
    obtain ⟨v, -, hzv⟩ := Set.mem_iUnion₂.1 hzF
    exact hzn (Set.mem_iUnion.2 ⟨v, hzv⟩)
  have hW : U ∩ (⋃ v ∈ {v | C.Hits U v}, (C.cell v : Set Plane))ᶜ ∈ 𝓝 z :=
    Filter.inter_mem hU (hclosed.isOpen_compl.mem_nhds hzF)
  obtain ⟨v, y, hyv, hyU, hyF⟩ := h _ hW
  exact hyF (Set.mem_biUnion (x := v) ⟨y, hyv, hyU⟩ hyv)

/-! ## Every witness contains the canonical singular set -/

/-- A witness with (LCS) contains the accumulation, uncovered and bad points. -/
theorem subset_sing (S : CellConfiguration.SingularSet C)
    (hL : C.LineConnectedOff S.sing) : accSet C ∪ uncSet C ∪ badSet C ⊆ S.sing := by
  intro z hz
  by_contra hzS
  have hacc : z ∉ accSet C := fun h => h (S.locallyFinite z hzS)
  have hunc : z ∉ uncSet C := fun h => h (S.cover hzS)
  have hbad : z ∉ badSet C := by
    intro hb
    apply hb
    obtain ⟨δ, hδ, hnear⟩ := exists_pos_closedBall_hits_imp_mem hacc
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp S.isClosed_sing.isOpen_compl z hzS
    set η := min ε δ / 2 with hη_def
    have hη : 0 < η := half_pos (lt_min hε hδ)
    have hηε : η < ε := lt_of_lt_of_le (half_lt_self (lt_min hε hδ)) (min_le_left _ _)
    have hηδ : η ≤ δ := le_trans (half_lt_self (lt_min hε hδ)).le (min_le_right _ _)
    have hsub : horizontal (z 0 - η) (z 0 + η) (z 1) ⊆ closedBall z η := fun p hp =>
      GMS.CellConfig.mem_closedBall_of_mem_horizontal hp
    have hdisj : Disjoint (horizontal (z 0 - η) (z 0 + η) (z 1)) S.sing := by
      refine Set.disjoint_left.2 fun p hp hpS => ?_
      have hpz : dist p z < ε := lt_of_le_of_lt (Metric.mem_closedBall.1 (hsub hp)) hηε
      exact hball (Metric.mem_ball.2 hpz) hpS
    have hconn := hL.1 (z 0 - η) (z 0 + η) (z 1) hdisj
    have hset : {v | C.Hits (horizontal (z 0 - η) (z 0 + η) (z 1)) v} = {v | C.Hits {z} v} := by
      ext v
      simp only [Set.mem_setOf_eq]
      constructor
      · rintro ⟨p, hpv, hpL⟩
        refine ⟨z, hnear v ⟨p, hpv, closedBall_subset_closedBall hηδ (hsub hpL)⟩, rfl⟩
      · rintro ⟨p, hpv, hp⟩
        rw [Set.mem_singleton_iff] at hp
        subst hp
        exact ⟨p, hpv, by linarith, by linarith, rfl⟩
    unfold CellConfiguration.InducedConnected at hconn ⊢
    rw [hset] at hconn
    exact hconn
  rcases hz with (hz | hz) | hz
  · exact hacc hz
  · exact hunc hz
  · exact hbad hz

/-- **Every witness contains the canonical singular set.** -/
theorem starSet_subset_sing (S : CellConfiguration.SingularSet C)
    (hL : C.LineConnectedOff S.sing) : starSet C ⊆ S.sing :=
  closure_minimal (subset_sing S hL) S.isClosed_sing

/-! ## Compact connected sets of good points -/

/-- **Connectedness along a compact preconnected set of good points**: if no point of `L` is an
accumulation, uncovered or bad point, then `H(L)` is connected. -/
theorem inducedConnected_of_isCompact {L : Set Plane} (hLc : IsCompact L)
    (hLp : IsPreconnected L) (hL : ∀ z ∈ L, z ∉ accSet C ∪ uncSet C ∪ badSet C) :
    C.InducedConnected L := by
  classical
  have hacc : ∀ z ∈ L, z ∉ accSet C := fun z hz h => hL z hz (Or.inl (Or.inl h))
  have hWfin : {v | C.Hits L v}.Finite := finite_hits_of_isCompact hLc hacc
  haveI : Finite {v | C.Hits L v} := hWfin.to_subtype
  have hcover : ∀ p ∈ L, ∃ K : {v | C.Hits L v}, p ∈ (C.cell (K : V) : Set Plane) := by
    intro p hp
    have hp' : p ∈ ⋃ v, (C.cell v : Set Plane) := by
      by_contra h
      exact hL p hp (Or.inl (Or.inr h))
    obtain ⟨v, hpv⟩ := Set.mem_iUnion.1 hp'
    exact ⟨⟨v, p, hpv, hp⟩, hpv⟩
  intro u₀ w₀
  by_contra hnr
  let R : Set {v | C.Hits L v} := {q | (C.graph.induce {v | C.Hits L v}).Reachable u₀ q}
  have hFA : IsClosed (⋃ q ∈ R, (C.cell (q : V) : Set Plane)) :=
    (Set.toFinite R).isClosed_biUnion fun q _ => (C.cell (q : V)).isCompact.isClosed
  have hFB : IsClosed (⋃ q ∈ Rᶜ, (C.cell (q : V) : Set Plane)) :=
    (Set.toFinite Rᶜ).isClosed_biUnion fun q _ => (C.cell (q : V)).isCompact.isClosed
  have hcov : L ⊆ (⋃ q ∈ R, (C.cell (q : V) : Set Plane)) ∪
      ⋃ q ∈ Rᶜ, (C.cell (q : V) : Set Plane) := by
    intro p hp
    obtain ⟨K, hpK⟩ := hcover p hp
    by_cases hK : K ∈ R
    · exact Or.inl (Set.mem_biUnion hK hpK)
    · exact Or.inr (Set.mem_biUnion hK hpK)
  have hA : (L ∩ ⋃ q ∈ R, (C.cell (q : V) : Set Plane)).Nonempty := by
    obtain ⟨p, hpc, hpL⟩ := u₀.2
    exact ⟨p, hpL, Set.mem_biUnion (show u₀ ∈ R from SimpleGraph.Reachable.refl u₀) hpc⟩
  have hB : (L ∩ ⋃ q ∈ Rᶜ, (C.cell (q : V) : Set Plane)).Nonempty := by
    obtain ⟨p, hpc, hpL⟩ := w₀.2
    exact ⟨p, hpL, Set.mem_biUnion (show w₀ ∈ Rᶜ from hnr) hpc⟩
  obtain ⟨p, hpL, hpA, hpB⟩ := isPreconnected_closed_iff.1 hLp _ _ hFA hFB hcov hA hB
  obtain ⟨q, hqR, hpq⟩ := Set.mem_iUnion₂.1 hpA
  obtain ⟨q', hq'R, hpq'⟩ := Set.mem_iUnion₂.1 hpB
  have hle : {v | C.Hits {p} v} ≤ {v | C.Hits L v} := fun v hv =>
    ⟨p, Set.inter_singleton_nonempty.1 hv, hpL⟩
  have hpt : C.InducedConnected {p} := by
    by_contra h
    exact hL p hpL (Or.inr h)
  have hr : (C.graph.induce {v | C.Hits {p} v}).Reachable
      ⟨(q : V), Set.inter_singleton_nonempty.2 hpq⟩
      ⟨(q' : V), Set.inter_singleton_nonempty.2 hpq'⟩ := hpt _ _
  have hr' := hr.map (C.graph.induceHomOfLE hle).toHom
  exact hq'R (hqR.trans hr')

/-! ## The characterization -/

/-- **The existential witness clause of Definition 1.1(ii) + (LCS) is the Hausdorff nullity of the
canonical singular set.** -/
theorem exists_singularSet_iff :
    (∃ S : CellConfiguration.SingularSet C, C.LineConnectedOff S.sing) ↔
      μH[1] (starSet C) = 0 := by
  constructor
  · rintro ⟨S, hL⟩
    exact measure_mono_null (starSet_subset_sing S hL) S.hausdorff_sing
  · intro h0
    have hgood : ∀ z ∉ starSet C, z ∉ accSet C ∪ uncSet C ∪ badSet C := fun z hz h =>
      hz (subset_starSet h)
    refine ⟨{ sing := starSet C
              isClosed_sing := isClosed_starSet
              hausdorff_sing := h0
              cover := fun z hz => by
                by_contra h
                exact hgood z hz (Or.inl (Or.inr h))
              locallyFinite := fun z hz => by
                by_contra h
                exact hgood z hz (Or.inl (Or.inl h)) }, ?_, ?_⟩
    · intro a b y hdisj
      exact inducedConnected_of_isCompact (isCompact_horizontal a b y)
        (isPreconnected_horizontal a b y) fun z hz => hgood z (Set.disjoint_left.1 hdisj hz)
    · intro x a b hdisj
      exact inducedConnected_of_isCompact (isCompact_vertical x a b)
        (isPreconnected_vertical x a b) fun z hz => hgood z (Set.disjoint_left.1 hdisj hz)

end ReflectedGMS.GeomTop.ValidBorel

assert_no_sorry ReflectedGMS.GeomTop.ValidBorel.exists_pos_closedBall_hits_imp_mem
assert_no_sorry ReflectedGMS.GeomTop.ValidBorel.finite_hits_of_isCompact
assert_no_sorry ReflectedGMS.GeomTop.ValidBorel.mem_iUnion_cell_of_notMem_accSet
assert_no_sorry ReflectedGMS.GeomTop.ValidBorel.subset_sing
assert_no_sorry ReflectedGMS.GeomTop.ValidBorel.starSet_subset_sing
assert_no_sorry ReflectedGMS.GeomTop.ValidBorel.inducedConnected_of_isCompact
assert_no_sorry ReflectedGMS.GeomTop.ValidBorel.exists_singularSet_iff

#print axioms ReflectedGMS.GeomTop.ValidBorel.inducedConnected_of_isCompact
#print axioms ReflectedGMS.GeomTop.ValidBorel.exists_singularSet_iff
