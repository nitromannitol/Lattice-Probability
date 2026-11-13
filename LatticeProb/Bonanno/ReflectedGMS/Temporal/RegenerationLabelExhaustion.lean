/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.RegenerationLabelExhaustion at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Temporal.RegenerationKernel
import LatticeProb.Bonanno.ReflectedGMS.Corrector.MeasurableInfinitePatchMinimizer
import LatticeProb.Bonanno.ReflectedGMS.Corrector.VaryingVertexIndexing
import LatticeProb.Bonanno.ReflectedGMS.Spatial.RootedFiniteEnergyDensityMeasurable

/-!
# A label-canonical exhaustion and the measurability of its level chains' jump data

`Temporal/RegenerationKernel` reduces the two-sided regeneration kernel to the measurability of
the area-clock transition function `e ↦ P_e^{H_n}(X_t = H_m)`.  The transition function is the
limit of the one-time marginals of the level chains `Yⁿ` of Gwynne–Sung (3.2)–(3.3) along ANY
exhaustion of the cell graph (Step 1 of the uniqueness proof,
`ReflectedWalk.Theorem16.exists_approximant`).  The exhaustion `TwoSidedRegenerationCoding.exhaustion
e` is a `Classical.choose` and cannot be used; this module builds a **label-canonical** exhaustion
whose levels vary measurably with the environment, and proves that the jump data of its level
chains — the transition probabilities (3.2)–(3.3), including the **full-graph harmonic measure**
of (3.3), and the area holding rates — are measurable functions of the environment.

* `baseLabel e` — the least active label, measurable (`measurable_baseLabel`).
* `labelExhaustion e : (decode e).graph.Exhaustion` — level `N` is the base vertex together with
  the active labels of `MeasurableInfinitePatchMinimizer.patchLevel` on the fixed ℕ-indexing
  `VaryingVertexIndexing.envNatGraph e`, anchored at the base label and at every absent label
  ("gate the datum, not the graph": inactive labels are isolated, so they anchor themselves).
  Membership of a label in a level is measurable (`measurableSet_levelMemSet`), and so is the
  first level of a label (`measurable_levelIndex`).
* `exists_measurable_harmonicMeasure` — the harmonic measure `hm^a_{G_N}(b)` of the actual
  (possibly transient, infinite) cell graph is a measurable function of the environment.  It is
  the full-energy minimizer with boundary data `1_b`, produced measurably on the ℕ-indexing by
  `MeasurableInfinitePatchMinimizer.exists_measurable_anchored_energy_minimizer` and identified
  with `energyMin` by uniqueness (`ConductanceGraph.energyMin_unique`); competitors transfer
  through `VaryingVertexIndexing.natExtend` with no change of energy.
* `measurable_labelTransProb`, `measurable_labelRate` — the label forms of `transProb` and of the
  area rate `π(v)/a(v)`.

Nothing here certifies `p:lem:regeninvariant` or either main theorem.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ReflectedGMS.RegenerationLabelExhaustion

open Code EnvironmentLaws AreaClocks
open ReflectedWalk
open ReflectedGMS.EnvironmentWalkDataProducer
open ReflectedGMS.MeasurableInfinitePatchMinimizer ReflectedGMS.VaryingVertexIndexing
open ReflectedGMS.RootedFiniteEnergyDensityMeasurable

/-! ### 1. The base label -/

theorem exists_active (e : Env) : ∃ n : ℕ, (e.val.1 n).isSome := by
  haveI := nontrivial_vertex e
  obtain ⟨v⟩ := (inferInstance : Nonempty (Vertex e.val))
  exact ⟨v.val, v.property⟩

/-- The least active label of the environment. -/
noncomputable def baseLabel (e : Env) : ℕ := Nat.find (exists_active e)

theorem baseLabel_isSome (e : Env) : (e.val.1 (baseLabel e)).isSome :=
  Nat.find_spec (exists_active e)

/-- The base vertex: the cell of the least active label. -/
noncomputable def baseVertex (e : Env) : Vertex e.val := ⟨baseLabel e, baseLabel_isSome e⟩

theorem measurable_baseLabel : Measurable baseLabel := by
  refine measurable_to_countable' fun n => ?_
  have hset : baseLabel ⁻¹' {n} = {e : Env | (e.val.1 n).isSome} ∩
      ⋂ k : Fin n, {e : Env | (e.val.1 (k : ℕ)).isSome}ᶜ := by
    ext e
    rw [Set.mem_preimage, Set.mem_singleton_iff, baseLabel, Nat.find_eq_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, Set.mem_iInter.2 fun k => h2 k k.isLt⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun k hk => Set.mem_iInter.1 h2 ⟨k, hk⟩⟩
  rw [hset]
  exact (RegenerationKernel.measurableSet_slotPresent n).inter
    (MeasurableSet.iInter fun k => (RegenerationKernel.measurableSet_slotPresent (k : ℕ)).compl)

/-! ### 2. The ℕ-indexed graph: adjacency only between active labels -/

theorem isSome_of_adj {e : Env} {a b : ℕ} (h : (envNatGraph e).toSimpleGraph.Adj a b) :
    (e.val.1 a).isSome ∧ (e.val.1 b).isSome := by
  have hc : 0 < e.val.2 a b := h
  constructor
  · by_contra ha
    have h0 : e.val.2 a b = 0 :=
      (admissible e).absent a b (Or.inl (Option.not_isSome_iff_eq_none.mp ha))
    linarith
  · by_contra hb
    have h0 : e.val.2 a b = 0 :=
      (admissible e).absent a b (Or.inr (Option.not_isSome_iff_eq_none.mp hb))
    linarith

theorem isSome_of_walk {e : Env} :
    ∀ {a b : ℕ} (_p : (envNatGraph e).toSimpleGraph.Walk a b),
      (e.val.1 a).isSome → (e.val.1 b).isSome
  | _, _, .nil, h => h
  | _, _, .cons hadj q, _ => isSome_of_walk q (isSome_of_adj hadj).2

/-- The inclusion of the cell graph into the ℕ-indexed graph is a graph homomorphism. -/
def valHom (e : Env) : (decode e).graph.toSimpleGraph →g (envNatGraph e).toSimpleGraph where
  toFun := Subtype.val
  map_rel' := fun h => h

/-- A walk of the ℕ-indexed graph between active labels whose support lies (as vertices) in `S`
gives reachability in the cell graph induced on `S`. -/
theorem reachable_induce_of_walk (e : Env) (S : Set (Vertex e.val)) :
    ∀ {a b : ℕ} (p : (envNatGraph e).toSimpleGraph.Walk a b) (ha : (e.val.1 a).isSome)
      (hb : (e.val.1 b).isSome)
      (hS : ∀ y ∈ p.support, ∀ hy : (e.val.1 y).isSome, (⟨y, hy⟩ : Vertex e.val) ∈ S),
      ((decode e).graph.toSimpleGraph.induce S).Reachable
        ⟨⟨a, ha⟩, hS a p.start_mem_support ha⟩ ⟨⟨b, hb⟩, hS b p.end_mem_support hb⟩ := by
  intro a b p
  induction p with
  | nil =>
    intro ha hb hS
    exact SimpleGraph.Reachable.refl _
  | cons hadj q ih =>
    intro ha hb hS
    have hc := (isSome_of_adj hadj).2
    have hS' : ∀ y ∈ q.support, ∀ hy : (e.val.1 y).isSome, (⟨y, hy⟩ : Vertex e.val) ∈ S :=
      fun y hy => hS y (by rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ hy)
    refine SimpleGraph.Reachable.trans ?_ (ih hc hb hS')
    exact SimpleGraph.Adj.reachable (by exact hadj)

/-! ### 3. The anchor set and the canonical levels on the ℕ-indexing -/

/-- The anchors of the canonical exhaustion: the base label and every absent label. -/
def anchorSet (e : Env) : Set ℕ := {n | n = baseLabel e ∨ ¬ (e.val.1 n).isSome}

theorem measurableSet_mem_anchorSet (n : ℕ) : MeasurableSet {e : Env | n ∈ anchorSet e} := by
  have hset : {e : Env | n ∈ anchorSet e} =
      baseLabel ⁻¹' {n} ∪ {e : Env | (e.val.1 n).isSome}ᶜ := by
    ext e
    show (n = baseLabel e ∨ ¬ (e.val.1 n).isSome) ↔ (baseLabel e = n ∨ ¬ (e.val.1 n).isSome)
    rw [eq_comm]
  rw [hset]
  exact (measurable_baseLabel (measurableSet_singleton n)).union
    (RegenerationKernel.measurableSet_slotPresent n).compl

theorem boundaryAnchored_anchorSet (e : Env) :
    BoundaryAnchored (envNatGraph e) (anchorSet e) := by
  intro v
  by_cases hv : (e.val.1 v).isSome
  · refine ⟨baseLabel e, Or.inl rfl, ?_⟩
    exact ((decode_connected e).preconnected ⟨v, hv⟩ (baseVertex e)).map (valHom e)
  · exact ⟨v, Or.inr hv, SimpleGraph.Reachable.refl _⟩

theorem exists_isAnchorChain_anchorSet (e : Env) (x : ℕ) :
    ∃ l : List ℕ, IsAnchorChain (envNatGraph e) (anchorSet e) x l :=
  exists_isAnchorChain _ (boundaryAnchored_anchorSet e) x

/-- The canonical level on the ℕ-indexing: `patchLevel` of the anchored ℕ-indexed graph. -/
noncomputable def natLevel (e : Env) (N : ℕ) : Finset ℕ :=
  patchLevel (envNatGraph e) (anchorSet e) N

theorem measurableSet_natLevel_eq (N : ℕ) (t : Finset ℕ) :
    MeasurableSet {e : Env | natLevel e N = t} :=
  measurableSet_patchLevel_eq (G := envNatGraph) measurable_envNatGraph_c
    measurableSet_mem_anchorSet exists_isAnchorChain_anchorSet N t

theorem measurableSet_mem_natLevel (N a : ℕ) : MeasurableSet {e : Env | a ∈ natLevel e N} := by
  have hset : {e : Env | a ∈ natLevel e N} =
      ⋃ t : {t : Finset ℕ // a ∈ t}, {e : Env | natLevel e N = t.1} := by
    ext e
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    exact ⟨fun h => ⟨⟨natLevel e N, h⟩, rfl⟩, fun ⟨t, ht⟩ => ht ▸ t.2⟩
  rw [hset]
  exact MeasurableSet.iUnion fun t => measurableSet_natLevel_eq N t.1

/-- A label of a canonical level is joined to the base label by a walk inside the level. -/
theorem exists_walk_to_base (e : Env) (N : ℕ) {u : ℕ} (hu : (e.val.1 u).isSome)
    (huN : u ∈ natLevel e N) :
    ∃ p : (envNatGraph e).toSimpleGraph.Walk u (baseLabel e),
      ∀ y ∈ p.support, y ∈ natLevel e N := by
  have hu' : u ∈ (seedUpTo N).biUnion
      fun x => (firstAnchorChain (envNatGraph e) (anchorSet e) x).toFinset := huN
  obtain ⟨x, hx, hux⟩ := Finset.mem_biUnion.1 hu'
  have hulist : u ∈ firstAnchorChain (envNatGraph e) (anchorSet e) x := List.mem_toFinset.1 hux
  obtain ⟨l', hl', hsub⟩ := exists_isAnchorChain_subset_of_mem (envNatGraph e)
    (isAnchorChain_firstAnchorChain (exists_isAnchorChain_anchorSet e x)) hulist
  have hsubN : ∀ y ∈ l', y ∈ natLevel e N := fun y hy =>
    (show y ∈ (seedUpTo N).biUnion
        fun x => (firstAnchorChain (envNatGraph e) (anchorSet e) x).toFinset from
      Finset.mem_biUnion.2 ⟨x, hx, List.mem_toFinset.2 (hsub y hy)⟩)
  obtain ⟨a, haA, p, hp⟩ := exists_walk_of_isAnchorChain (envNatGraph e) hl'
    (S := ((natLevel e N : Finset ℕ) : Set ℕ)) (fun y hy => Finset.mem_coe.2 (hsubN y hy))
  have ha : (e.val.1 a).isSome := isSome_of_walk p hu
  rcases haA with rfl | hna
  · exact ⟨p, fun y hy => hp y hy⟩
  · exact absurd ha hna

/-! ### 4. The label-canonical exhaustion -/

/-- Level `N` of the label-canonical exhaustion: the base vertex and the active labels of the
canonical ℕ-level. -/
noncomputable def levelFinset (e : Env) (N : ℕ) : Finset (Vertex e.val) :=
  insert (baseVertex e) ((natLevel e N).subtype fun m => (e.val.1 m).isSome)

theorem mem_levelFinset {e : Env} {N : ℕ} {v : Vertex e.val} :
    v ∈ levelFinset e N ↔ v = baseVertex e ∨ v.val ∈ natLevel e N := by
  rw [levelFinset, Finset.mem_insert, Finset.mem_subtype]

theorem baseVertex_mem_levelFinset (e : Env) (N : ℕ) : baseVertex e ∈ levelFinset e N :=
  mem_levelFinset.2 (Or.inl rfl)

theorem levelFinset_mono (e : Env) : Monotone (levelFinset e) := by
  intro N N' h v hv
  rw [mem_levelFinset] at hv ⊢
  rcases hv with hv | hv
  · exact Or.inl hv
  · exact Or.inr (patchLevel_mono (envNatGraph e) h hv)

theorem exists_mem_levelFinset (e : Env) (v : Vertex e.val) : ∃ N, v ∈ levelFinset e N := by
  obtain ⟨N, hN⟩ :=
    exists_mem_patchLevel (envNatGraph e) (exists_isAnchorChain_anchorSet e) v.val
  exact ⟨N, mem_levelFinset.2 (Or.inr hN)⟩

theorem connected_levelFinset (e : Env) (N : ℕ) :
    ((decode e).graph.toSimpleGraph.induce
      ((levelFinset e N : Finset (Vertex e.val)) : Set (Vertex e.val))).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨baseVertex e, baseVertex_mem_levelFinset e N⟩, fun ⟨u, hu⟩ => ?_⟩
  rcases mem_levelFinset.1 hu with rfl | hu'
  · exact SimpleGraph.Reachable.refl _
  · obtain ⟨p, hp⟩ := exists_walk_to_base e N u.property hu'
    have hS : ∀ y ∈ p.support, ∀ hy : (e.val.1 y).isSome,
        (⟨y, hy⟩ : Vertex e.val) ∈ ((levelFinset e N : Finset (Vertex e.val)) :
          Set (Vertex e.val)) :=
      fun y hy _ => mem_levelFinset.2 (Or.inr (hp y hy))
    exact (reachable_induce_of_walk e _ p u.property (baseLabel_isSome e) hS).symm

/-- **The label-canonical exhaustion of the cell graph.** -/
noncomputable def labelExhaustion (e : Env) : (decode e).graph.Exhaustion where
  Gsub := levelFinset e
  mono := levelFinset_mono e
  connected := connected_levelFinset e
  exists_mem := exists_mem_levelFinset e

/-! ### 5. Measurability of the levels in the labels -/

/-- The environments in which label `a` is active and belongs to level `N`. -/
def levelMemSet (N a : ℕ) : Set Env :=
  {e : Env | ∃ h : (e.val.1 a).isSome, (⟨a, h⟩ : Vertex e.val) ∈ levelFinset e N}

theorem mem_levelMemSet {N a : ℕ} {e : Env} (ha : (e.val.1 a).isSome) :
    e ∈ levelMemSet N a ↔ (⟨a, ha⟩ : Vertex e.val) ∈ levelFinset e N :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨ha, h⟩⟩

/-- **Level membership of a label is measurable in the environment.** -/
theorem measurableSet_levelMemSet (N a : ℕ) : MeasurableSet (levelMemSet N a) := by
  have hset : levelMemSet N a
      = {e : Env | (e.val.1 a).isSome} ∩ (baseLabel ⁻¹' {a} ∪ {e | a ∈ natLevel e N}) := by
    ext e
    constructor
    · rintro ⟨h, hmem⟩
      refine ⟨h, ?_⟩
      rcases mem_levelFinset.1 hmem with hb | hn
      · exact Or.inl (show baseLabel e = a from (congrArg Subtype.val hb).symm)
      · exact Or.inr hn
    · rintro ⟨h, hb | hn⟩
      · refine ⟨h, mem_levelFinset.2 (Or.inl (Subtype.ext ?_))⟩
        exact (show baseLabel e = a from hb).symm
      · exact ⟨h, mem_levelFinset.2 (Or.inr hn)⟩
  rw [hset]
  exact (RegenerationKernel.measurableSet_slotPresent a).inter
    ((measurable_baseLabel (measurableSet_singleton a)).union (measurableSet_mem_natLevel N a))

/-- `n_z = N` exactly when `z` lies in level `N` and in no earlier level. -/
theorem nz_eq_iff {V : Type*} {G : ConductanceGraph V} (E : G.Exhaustion) (z : V) (N : ℕ) :
    E.nz z = N ↔ z ∈ E.Gsub N ∧ ∀ k < N, z ∉ E.Gsub k := by
  constructor
  · rintro rfl
    exact ⟨E.mem_Gsub_nz z, fun k hk hz => absurd (E.nz_le hz) (not_le.2 hk)⟩
  · rintro ⟨hN, hmin⟩
    refine le_antisymm (E.nz_le hN) ?_
    by_contra hlt
    exact hmin _ (not_le.1 hlt) (E.mem_Gsub_nz z)

/-- The first level of a label (`0` at absent labels). -/
noncomputable def levelIndex (e : Env) (a : ℕ) : ℕ :=
  if h : (e.val.1 a).isSome then (labelExhaustion e).nz ⟨a, h⟩ else 0

theorem levelIndex_of_isSome {e : Env} {a : ℕ} (h : (e.val.1 a).isSome) :
    levelIndex e a = (labelExhaustion e).nz ⟨a, h⟩ := dif_pos h

theorem measurable_levelIndex (a : ℕ) : Measurable fun e : Env => levelIndex e a := by
  refine measurable_to_countable' fun N => ?_
  have hset : (fun e : Env => levelIndex e a) ⁻¹' {N} =
      ({e : Env | (e.val.1 a).isSome} ∩ (levelMemSet N a ∩ ⋂ k : Fin N, (levelMemSet k a)ᶜ)) ∪
        ({e : Env | (e.val.1 a).isSome}ᶜ ∩ {_e : Env | N = 0}) := by
    ext e
    rw [Set.mem_preimage, Set.mem_singleton_iff]
    by_cases ha : (e.val.1 a).isSome
    · rw [levelIndex_of_isSome ha, nz_eq_iff]
      constructor
      · rintro ⟨h1, h2⟩
        refine Or.inl ⟨ha, (mem_levelMemSet ha).2 h1, Set.mem_iInter.2 fun k hk => ?_⟩
        exact h2 k k.isLt ((mem_levelMemSet ha).1 hk)
      · rintro (⟨-, h1, h2⟩ | ⟨hna, -⟩)
        · refine ⟨(mem_levelMemSet ha).1 h1, fun k hk hmem => ?_⟩
          exact Set.mem_iInter.1 h2 ⟨k, hk⟩ ((mem_levelMemSet ha).2 hmem)
        · exact absurd ha hna
    · have h0 : levelIndex e a = 0 := dif_neg ha
      rw [h0]
      constructor
      · rintro rfl
        exact Or.inr ⟨ha, rfl⟩
      · rintro (⟨hsa, -⟩ | ⟨-, hN⟩)
        · exact absurd hsa ha
        · exact hN.symm
  rw [hset]
  refine MeasurableSet.union ?_ ?_
  · exact (RegenerationKernel.measurableSet_slotPresent a).inter
      ((measurableSet_levelMemSet N a).inter
        (MeasurableSet.iInter fun k => (measurableSet_levelMemSet (k : ℕ) a).compl))
  · exact (RegenerationKernel.measurableSet_slotPresent a).compl.inter
      (MeasurableSet.const (N = 0))

/-! ### 6. The harmonic measure of the actual graph is measurable -/

/-- The anchors of the level-`N` harmonic problem on the ℕ-indexing: the labels of level `N` and
every absent label. -/
def levelAnchor (N : ℕ) (e : Env) : Set ℕ :=
  {m | (∃ h : (e.val.1 m).isSome, (⟨m, h⟩ : Vertex e.val) ∈ levelFinset e N) ∨
    ¬ (e.val.1 m).isSome}

theorem measurableSet_mem_levelAnchor (N m : ℕ) :
    MeasurableSet {e : Env | m ∈ levelAnchor N e} := by
  have hset : {e : Env | m ∈ levelAnchor N e} =
      levelMemSet N m ∪ {e : Env | (e.val.1 m).isSome}ᶜ := rfl
  rw [hset]
  exact (measurableSet_levelMemSet N m).union (RegenerationKernel.measurableSet_slotPresent m).compl

theorem boundaryAnchored_levelAnchor (N : ℕ) (e : Env) :
    BoundaryAnchored (envNatGraph e) (levelAnchor N e) := by
  intro v
  by_cases hv : (e.val.1 v).isSome
  · refine ⟨baseLabel e, Or.inl ⟨baseLabel_isSome e, baseVertex_mem_levelFinset e N⟩, ?_⟩
    exact ((decode_connected e).preconnected ⟨v, hv⟩ (baseVertex e)).map (valHom e)
  · exact ⟨v, Or.inr hv, SimpleGraph.Reachable.refl _⟩

/-- The indicator of a label on the ℕ-indexing. -/
def labelIndicator (b m : ℕ) : ℝ := if m = b then 1 else 0

theorem labelIndicator_eq_indic {e : Env} {b : ℕ} (hb : (e.val.1 b).isSome) (v : Vertex e.val) :
    labelIndicator b v.val = (decode e).graph.indic ⟨b, hb⟩ v := by
  simp only [ConductanceGraph.indic]
  by_cases hvb : v.val = b
  · have hv' : v = ⟨b, hb⟩ := Subtype.ext hvb
    rw [labelIndicator, if_pos hvb, if_pos hv']
  · have hv' : v ≠ ⟨b, hb⟩ := fun h => hvb (congrArg Subtype.val h)
    rw [labelIndicator, if_neg hvb, if_neg hv']

theorem natExtend_of_not_isSome {e : Env} (g : Vertex e.val → ℝ) {m : ℕ}
    (hm : ¬ (e.val.1 m).isSome) : natExtend g m = 0 := by
  unfold natExtend
  rw [Function.extend_apply' _ _ _ fun ⟨v, hv⟩ => hm (hv ▸ v.property)]

/-- **The full-graph harmonic measure of a canonical level is measurable in the environment.**
For every level `N` and target label `b` there is a field, measurable at every label, which is
`hm^a_{G_N}(b)` at every environment in which `a` and `b` are active. -/
theorem exists_measurable_harmonicMeasure (N b : ℕ) :
    ∃ f : Env → ℕ → ℝ, (∀ a : ℕ, Measurable fun e => f e a) ∧
      ∀ (e : Env) (a : ℕ) (ha : (e.val.1 a).isSome) (hb : (e.val.1 b).isSome),
        (decode e).graph.harmonicMeasure (decode_connected e) (levelFinset e N) ⟨a, ha⟩ ⟨b, hb⟩
          = f e a := by
  have huE : ∀ e : Env, (envNatGraph e).HasFiniteEnergy (labelIndicator b) := fun e =>
    (envNatGraph e).hasFiniteEnergy_of_support_subset {b} fun x hx => by
      have hxb : x ≠ b := fun h => hx (Finset.mem_singleton.2 h)
      rw [labelIndicator, if_neg hxb]
  obtain ⟨f, -, hfmeas, hf⟩ := exists_measurable_anchored_energy_minimizer
    (G := envNatGraph) measurable_envNatGraph_c (A := levelAnchor N)
    (measurableSet_mem_levelAnchor N) (boundaryAnchored_levelAnchor N)
    (u := fun _ => labelIndicator b) (fun _ => measurable_const) huE
  refine ⟨f, hfmeas, fun e a ha hb => ?_⟩
  obtain ⟨hfE, hftrace, hfmin⟩ := hf e
  have hSne : (levelFinset e N).Nonempty := ⟨baseVertex e, baseVertex_mem_levelFinset e N⟩
  have key : (fun v : Vertex e.val => f e v.val) =
      (decode e).graph.energyMin (decode_connected e) (levelFinset e N)
        ((decode e).graph.indic ⟨b, hb⟩) := by
    refine (decode e).graph.energyMin_unique (decode_connected e) hSne _ ?_ ?_ ?_
    · exact (hasFiniteEnergy_envNatGraph_iff e (f e)).2 hfE
    · intro v hv
      have hmem : v.val ∈ levelAnchor N e := Or.inl ⟨v.property, Finset.mem_coe.1 hv⟩
      show f e v.val = _
      rw [hftrace v.val hmem]
      exact labelIndicator_eq_indic hb v
    · intro g hg hgS
      rw [Energy_envNatGraph e (f e), ← natExtend_comp g, Energy_envNatGraph e (natExtend g)]
      refine hfmin (natExtend g) ((hasFiniteEnergy_envNatGraph_iff e _).1 ?_) ?_
      · rw [natExtend_comp]
        exact hg
      · intro m hm
        rcases hm with ⟨hm, hmS⟩ | hm
        · have h1 : natExtend g m = g ⟨m, hm⟩ := natExtend_apply g ⟨m, hm⟩
          rw [h1, hgS (Finset.mem_coe.2 hmS)]
          exact (labelIndicator_eq_indic hb ⟨m, hm⟩).symm
        · have hne : m ≠ b := fun h => hm (h ▸ hb)
          rw [natExtend_of_not_isSome g hm]
          show (0 : ℝ) = labelIndicator b m
          rw [labelIndicator, if_neg hne]
  show (decode e).graph.energyMin (decode_connected e) (levelFinset e N)
      ((decode e).graph.indic ⟨b, hb⟩) ⟨a, ha⟩ = f e a
  rw [← key]

/-! ### 7. The jump data of the level chains in labels -/

theorem pi_eq_slotConductanceMass (e : Env) (v : Vertex e.val) :
    (decode e).graph.pi v = (slotConductanceMass e v.val).toReal := by
  rw [← ofReal_pi_eq_slotConductanceMass]
  exact (ENNReal.toReal_ofReal ((decode e).graph.pi_nonneg v)).symm

/-- The transition probabilities (3.2)–(3.3) of the level-`N` chain of the label-canonical
exhaustion, read in the labels (`0` at absent labels). -/
noncomputable def labelTransProb (N : ℕ) (e : Env) (a b : ℕ) : ℝ :=
  if h : (e.val.1 a).isSome ∧ (e.val.1 b).isSome then
    (decode e).graph.transProb (decode_connected e) (levelFinset e N) ⟨a, h.1⟩ ⟨b, h.2⟩
  else 0

theorem labelTransProb_of_isSome {N : ℕ} {e : Env} {a b : ℕ} (ha : (e.val.1 a).isSome)
    (hb : (e.val.1 b).isSome) :
    labelTransProb N e a b =
      (decode e).graph.transProb (decode_connected e) (levelFinset e N) ⟨a, ha⟩ ⟨b, hb⟩ :=
  dif_pos ⟨ha, hb⟩

open Classical in
/-- **The label transition probabilities of the level chains are measurable.** -/
theorem measurable_labelTransProb (N a b : ℕ) :
    Measurable fun e : Env => labelTransProb N e a b := by
  obtain ⟨f, hfm, hf⟩ := exists_measurable_harmonicMeasure N b
  have heq : (fun e : Env => labelTransProb N e a b) = fun e =>
      if e ∈ {e : Env | (e.val.1 a).isSome} ∩ {e : Env | (e.val.1 b).isSome} then
        (if e ∈ levelMemSet N a then e.val.2 a b / (slotConductanceMass e a).toReal
          else if e ∈ levelMemSet N b then f e a else 0)
      else 0 := by
    funext e
    by_cases h : (e.val.1 a).isSome ∧ (e.val.1 b).isSome
    · have hS : e ∈ {e : Env | (e.val.1 a).isSome} ∩ {e : Env | (e.val.1 b).isSome} := h
      rw [labelTransProb_of_isSome h.1 h.2, if_pos hS]
      by_cases ha' : (⟨a, h.1⟩ : Vertex e.val) ∈ levelFinset e N
      · rw [if_pos ((mem_levelMemSet h.1).2 ha'), ConductanceGraph.transProb_of_mem _ _ ha',
          pi_eq_slotConductanceMass]
        exact rfl
      · rw [if_neg (fun hm => ha' ((mem_levelMemSet h.1).1 hm))]
        by_cases hb' : (⟨b, h.2⟩ : Vertex e.val) ∈ levelFinset e N
        · rw [if_pos ((mem_levelMemSet h.2).2 hb'),
            ConductanceGraph.transProb_of_not_mem_of_mem _ _ ha' hb', hf e a h.1 h.2]
        · rw [if_neg (fun hm => hb' ((mem_levelMemSet h.2).1 hm)),
            ConductanceGraph.transProb_of_not_mem_of_not_mem _ _ ha' hb']
    · have hS : e ∉ {e : Env | (e.val.1 a).isSome} ∩ {e : Env | (e.val.1 b).isSome} := h
      rw [if_neg hS]
      exact dif_neg h
  rw [heq]
  refine Measurable.ite ((RegenerationKernel.measurableSet_slotPresent a).inter
      (RegenerationKernel.measurableSet_slotPresent b))
    (Measurable.ite (measurableSet_levelMemSet N a) ?_
      (Measurable.ite (measurableSet_levelMemSet N b) (hfm a) measurable_const))
    measurable_const
  exact (measurable_conductance_env a b).div (measurable_slotConductanceMass a).ennreal_toReal

/-- The area holding rate `π(v)/a(v)` read in the labels (`1` at absent labels). -/
noncomputable def labelRate (e : Env) (a : ℕ) : ℝ :=
  if h : (e.val.1 a).isSome then areaRate (decode e) ⟨a, h⟩ else 1

theorem labelRate_of_isSome {e : Env} {a : ℕ} (h : (e.val.1 a).isSome) :
    labelRate e a = areaRate (decode e) ⟨a, h⟩ := dif_pos h

theorem measurable_labelRate (a : ℕ) : Measurable fun e : Env => labelRate e a := by
  classical
  have heq : (fun e : Env => labelRate e a) = fun e =>
      if e ∈ {e : Env | (e.val.1 a).isSome} then
        (slotConductanceMass e a).toReal / (volume (slotCell e a : Set Plane)).toReal
      else 1 := by
    funext e
    by_cases h : (e.val.1 a).isSome
    · have hS : e ∈ {e : Env | (e.val.1 a).isSome} := h
      rw [labelRate_of_isSome h, if_pos hS, areaRate, pi_eq_slotConductanceMass,
        StatementIngredients.cellArea, ← slotCell_eq_cell e ⟨a, h⟩]
    · have hS : e ∉ {e : Env | (e.val.1 a).isSome} := h
      rw [labelRate, dif_neg h, if_neg hS]
  rw [heq]
  exact Measurable.ite (RegenerationKernel.measurableSet_slotPresent a)
    ((measurable_slotConductanceMass a).ennreal_toReal.div
      (Spatial.measurable_cellVolume.comp (measurable_slotCell_env a)).ennreal_toReal)
    measurable_const

end ReflectedGMS.RegenerationLabelExhaustion
