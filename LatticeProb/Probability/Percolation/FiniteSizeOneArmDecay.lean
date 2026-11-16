import LatticeProb.Vendor.FormalMathPercolation.Literature.PlanarDuality
import LatticeProb.Vendor.FormalMathPercolation.Literature.FiniteEnergy
import LatticeProb.Prob.BK

/-!
# Finite-size connectivity

Independence, disjoint path certificates, and a finite-coordinate BK bound
under Bernoulli bond percolation.
-/

open MeasureTheory ProbabilityTheory Percolation.Literature
open scoped ProbabilityTheory

noncomputable section

namespace FiniteSizeOneArm

variable {V : Type*} [Countable V]

/-- The open boundary edge contributes a factor `p` to the probability of an
interior connection. -/
theorem interior_connection_inter_boundary_edge (G : SimpleGraph V) (p : unitInterval)
    (S : Finset V) (a b x y : V) (hy : y ∉ S)
    (he : s(x, y) ∈ G.edgeSet) :
    (bondPercolation G p).real
        (openConnIn (↑S : Set V) a b ∩ {ω | s(x, y) ∈ ω}) =
      (p : ℝ) * (bondPercolation G p).real (openConnIn (↑S : Set V) a b) := by
  classical
  have hdis : Disjoint (↑S.sym2 : Set (Sym2 V)) {s(x, y)} := by
    rw [Set.disjoint_singleton_right]
    intro h
    have h' := Finset.mem_sym2_iff.mp h
    exact hy (h' y (by simp))
  have hdet : DeterminedBy {ω : BondConfig V | s(x, y) ∈ ω} {s(x, y)} := by
    rw [determinedBy_iff]
    intro ω ω' h
    have := Set.ext_iff.mp h s(x, y)
    simpa using this
  have hm : MeasurableSet {ω : BondConfig V | s(x, y) ∈ ω} := measurableSet_setOfPred.mpr (measurable_set_mem _)
  rw [bondPercolation_real_inter_of_disjoint G p hdis
    (PlanarDuality.determinedBy_openConnIn S a b) hdet
    (PlanarDuality.determinedBy_openConnIn S a b).measurableSet_of_finset hm,
    bondPercolation_cylinder G p he, mul_comm]


/-- Interior and exterior connections and the open edge between them factor
under Bernoulli bond percolation. -/
theorem interior_connection_inter_edge_inter_exterior_connection
    (G : SimpleGraph V) (p : unitInterval) (S T : Finset V)
    (a b x y c d : V) (hST : Disjoint S T) (hx : x ∈ S) (hy : y ∉ S)
    (he : s(x, y) ∈ G.edgeSet) :
    (bondPercolation G p).real
        ((openConnIn (↑S : Set V) a b ∩ {ω | s(x, y) ∈ ω}) ∩
          openConnIn (↑T : Set V) c d) =
      (p : ℝ) * (bondPercolation G p).real (openConnIn (↑S : Set V) a b) *
        (bondPercolation G p).real (openConnIn (↑T : Set V) c d) := by
  classical
  have hxT : x ∉ T := fun h => (Finset.disjoint_left.mp hST) hx h
  have hdisST : Disjoint (↑S.sym2 : Set (Sym2 V)) ↑T.sym2 := by
    rw [Finset.disjoint_coe, Finset.disjoint_left]
    intro e hS hT
    induction e using Sym2.ind with
    | h u v =>
      rw [Finset.mk_mem_sym2_iff] at hS hT
      exact (Finset.disjoint_left.mp hST) hS.1 hT.1
  have hdisedge : Disjoint ({s(x, y)} : Set (Sym2 V)) ↑T.sym2 := by
    rw [Set.disjoint_singleton_left]
    intro h
    exact hxT ((Finset.mk_mem_sym2_iff.mp h).1)
  have hdetedge : DeterminedBy {ω : BondConfig V | s(x, y) ∈ ω} {s(x, y)} := by
    rw [determinedBy_iff]
    intro ω ω' h
    have := Set.ext_iff.mp h s(x, y)
    simpa using this
  have hmedge : MeasurableSet {ω : BondConfig V | s(x, y) ∈ ω} :=
    measurableSet_setOfPred.mpr (measurable_set_mem _)
  have hdet := (PlanarDuality.determinedBy_openConnIn S a b).mono
    (Set.subset_union_left : (↑S.sym2 : Set (Sym2 V)) ⊆ (↑S.sym2 : Set (Sym2 V)) ∪ {s(x, y)})
  have hdete := hdetedge.mono
    (Set.subset_union_right : ({s(x, y)} : Set (Sym2 V)) ⊆ (↑S.sym2 : Set (Sym2 V)) ∪ {s(x, y)})
  rw [bondPercolation_real_inter_of_disjoint G p (Set.disjoint_union_left.mpr ⟨hdisST, hdisedge⟩)
    (hdet.inter hdete) (PlanarDuality.determinedBy_openConnIn T c d)
    ((PlanarDuality.determinedBy_openConnIn S a b).measurableSet_of_finset.inter hmedge)
    (PlanarDuality.determinedBy_openConnIn T c d).measurableSet_of_finset,
    interior_connection_inter_boundary_edge G p S a b x y hy he]


omit [Countable V] in
/-- An open walk leaving a set contains an open edge leaving it, preceded by
an interior connection and followed by an open connection to the endpoint. -/
theorem exists_first_exit_edge {ω : BondConfig V} (S : Finset V) {a z : V}
    (ha : a ∈ S) (hz : z ∉ S) (h : (openGraph ω).Reachable a z) :
    ∃ x ∈ S, ∃ y ∉ S, s(x, y) ∈ ω ∧
      ω ∈ openConnIn (↑S : Set V) a x ∧ (openGraph ω).Reachable y z := by
  classical
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact (hz ha).elim
  | @cons u v z huv w ih =>
    by_cases hv : v ∈ S
    · obtain ⟨x, hx, y, hy, he, hc, hr⟩ := ih hv hz
      refine ⟨x, hx, y, hy, he, ?_, hr⟩
      exact PlanarDuality.openConnIn_trans
        (openConnIn_of_adj ha hv (openGraph_adj ω u v |>.mp huv).1 huv.ne) hc
    · exact ⟨u, ha, v, hv, (openGraph_adj ω u v |>.mp huv).1,
        openConnIn_refl ha, ⟨w⟩⟩


omit [Countable V] in
/-- A walk leaving a set splits at its first exit into a walk within the set,
an exit edge, and a remaining walk. -/
theorem walk_first_exit_split {G : SimpleGraph V} (S : Set V) {a z : V}
    (w : G.Walk a z) (ha : a ∈ S) (hz : z ∉ S) :
    ∃ (x : V) (_ : x ∈ S) (y : V) (_ : y ∉ S) (hxy : G.Adj x y)
      (p : G.Walk a x) (q : G.Walk y z),
      (∀ v ∈ p.support, v ∈ S) ∧ w = p.append (SimpleGraph.Walk.cons hxy q) := by
  induction w with
  | nil => exact (hz ha).elim
  | @cons u v z huv w ih =>
    by_cases hv : v ∈ S
    · obtain ⟨x, hx, y, hy, hxy, p, q, hp, hw⟩ := ih hv hz
      refine ⟨x, hx, y, hy, hxy, p.cons huv, q, ?_, ?_⟩
      · intro t ht
        simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at ht
        rcases ht with rfl | ht
        · exact ha
        · exact hp t ht
      · simpa only [SimpleGraph.Walk.cons_append] using congrArg (SimpleGraph.Walk.cons huv) hw
    · refine ⟨u, ha, v, hv, huv, SimpleGraph.Walk.nil, w, ?_, ?_⟩
      · simpa using ha
      · rfl


omit [Countable V] in
/-- An open connection leaving a set admits an interior prefix, an exit edge,
and a continuation with pairwise disjoint edge sets. -/
theorem exists_first_exit_edge_disjoint_walks {ω : BondConfig V} (S : Set V) {a z : V}
    (ha : a ∈ S) (hz : z ∉ S) (h : (openGraph ω).Reachable a z) :
    ∃ (x : V) (_ : x ∈ S) (y : V) (_ : y ∉ S)
      (_hxy : (openGraph ω).Adj x y) (p : (openGraph ω).Walk a x)
      (q : (openGraph ω).Walk y z),
      (∀ v ∈ p.support, v ∈ S) ∧
      p.edges.Disjoint (s(x, y) :: q.edges) ∧ s(x, y) ∉ q.edges := by
  classical
  obtain ⟨w⟩ := h
  let t := w.toPath
  obtain ⟨x, hx, y, hy, hxy, p, q, hp, hsplit⟩ :=
    walk_first_exit_split S t.val ha hz
  have ht : t.val.IsTrail := t.property.isTrail
  rw [hsplit, SimpleGraph.Walk.isTrail_append] at ht
  refine ⟨x, hx, y, hy, hxy, p, q, hp, ?_, ?_⟩
  · simpa only [SimpleGraph.Walk.edges_cons] using ht.2.2
  · exact (SimpleGraph.Walk.isTrail_cons hxy q).mp ht.2.1 |>.2


omit [Countable V] in
/-- An open connection leaving a set has disjoint finite certificates for its
interior connection and exit edge, and for the continuation. -/
theorem exists_first_exit_disjoint_certificates {ω : BondConfig V} (S : Set V) {a z : V}
    (ha : a ∈ S) (hz : z ∉ S) (h : (openGraph ω).Reachable a z) :
    ∃ (x : V) (_ : x ∈ S) (y : V) (_ : y ∉ S) (K L : Finset (Sym2 V)),
      Disjoint K L ∧ (↑K : Set (Sym2 V)) ⊆ ω ∧ (↑L : Set (Sym2 V)) ⊆ ω ∧
      s(x, y) ∈ K ∧ (↑K : BondConfig V) ∈ openConnIn S a x ∧
      (openGraph (↑L : BondConfig V)).Reachable y z := by
  classical
  obtain ⟨x, hx, y, hy, hxy, p, q, hp, hdis, hed⟩ :=
    exists_first_exit_edge_disjoint_walks S ha hz h
  let K := insert s(x, y) p.edges.toFinset
  let L := q.edges.toFinset
  refine ⟨x, hx, y, hy, K, L, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro e heK heL
    simp only [K, Finset.mem_insert, List.mem_toFinset] at heK
    simp only [L, List.mem_toFinset] at heL
    rcases heK with rfl | heK
    · exact hed heL
    · exact (List.disjoint_left.mp hdis) heK (List.mem_cons_of_mem _ heL)
  · intro e he
    simp only [Finset.mem_coe, K, Finset.mem_insert, List.mem_toFinset] at he
    rcases he with rfl | he
    · exact (openGraph_adj ω x y).mp hxy |>.1
    · exact edgeSet_openGraph_subset ω (p.edges_subset_edgeSet he)
  · intro e he
    exact edgeSet_openGraph_subset ω (q.edges_subset_edgeSet (by simpa [L] using he))
  · simp [K]
  · apply mem_openConnIn_of_walk p hp
    intro e he
    simp [K, he]
  · have hq : ∀ e ∈ q.edges, e ∈ (openGraph (↑L : BondConfig V)).edgeSet := by
      intro e he
      rw [openGraph, SimpleGraph.edgeSet_fromEdgeSet]
      exact ⟨by simpa [L] using he, SimpleGraph.not_isDiag_of_mem_edgeSet _
        (q.edges_subset_edgeSet he)⟩
    exact ⟨q.transfer _ hq⟩

/-- Encode a proposition as a Boolean value. -/
def propBool (q : Prop) : Bool := by
  classical
  exact decide q

/-- Restrict a bond configuration to finitely many Boolean coordinates. -/
def finiteBoolConfig (F : Finset (Sym2 V)) (ω : BondConfig V) : F → Bool :=
  fun e => propBool (e.val ∈ ω)

omit [Countable V] in
/-- The law of finitely many bond coordinates is the product of their laws. -/
theorem finiteBoolConfig_law (G : SimpleGraph V) (p : unitInterval)
    (F : Finset (Sym2 V)) :
    (bondPercolation G p).map (finiteBoolConfig F) =
      Measure.pi (fun e : F =>
        (bernoulliMeasure (e.val ∈ G.edgeSet) False p).map propBool) := by
  classical
  have hm : Measurable propBool := by fun_prop
  rw [bondPercolation, setBernoulli_eq_map, Measure.map_map]
  · have heq : (finiteBoolConfig F ∘ fun χ : Sym2 V → Prop => {i | χ i}) =
        (fun χ : Sym2 V → Prop => fun e : F => propBool (χ e)) := by rfl
    rw [heq]
    rw [show (fun χ : Sym2 V → Prop => fun e : F => propBool (χ e)) =
        (fun χ : F → Prop => fun e : F => propBool (χ e)) ∘ F.restrict by rfl]
    rw [← Measure.map_map (by fun_prop) (by fun_prop), Measure.infinitePi_map_restrict]
    exact Measure.pi_map_pi (fun _ => hm.aemeasurable)
  · unfold finiteBoolConfig
    fun_prop
  · fun_prop

omit [Countable V] in
/-- The BK inequality for increasing events depending on finitely many bonds. -/
theorem finite_bool_bk (G : SimpleGraph V) (p : unitInterval)
    (F : Finset (Sym2 V)) {A B : Set (F → Bool)}
    (hA : IsUpperSet A) (hB : IsUpperSet B) :
    (bondPercolation G p) (finiteBoolConfig F ⁻¹' LatticeProb.disjointOccSet A B) ≤
      (bondPercolation G p) (finiteBoolConfig F ⁻¹' A) *
      (bondPercolation G p) (finiteBoolConfig F ⁻¹' B) := by
  classical
  have hm : Measurable (finiteBoolConfig F) := by unfold finiteBoolConfig; fun_prop
  have hmap := finiteBoolConfig_law G p F
  have h := LatticeProb.measure_pi_disjointOccSet_le
    (fun e : F => (bernoulliMeasure (e.val ∈ G.edgeSet) False p).map
      propBool) hA hB
  rw [← hmap, Measure.map_apply hm (MeasurableSet.of_discrete),
    Measure.map_apply hm (MeasurableSet.of_discrete),
    Measure.map_apply hm (MeasurableSet.of_discrete)] at h
  exact h

omit [Countable V] in
/-- Disjoint open-coordinate witnesses for increasing events satisfy the BK bound. -/
theorem finite_bool_witness_bk [DecidableEq V] (G : SimpleGraph V) (p : unitInterval)
    (F : Finset (Sym2 V)) {A B : Set (F → Bool)}
    (hA : IsUpperSet A) (hB : IsUpperSet B) :
    (bondPercolation G p) (finiteBoolConfig F ⁻¹' LatticeProb.wit A B) ≤
      (bondPercolation G p) (finiteBoolConfig F ⁻¹' A) *
      (bondPercolation G p) (finiteBoolConfig F ⁻¹' B) := by
  classical
  rw [← LatticeProb.disjointOcc_eq_wit hA hB, ← LatticeProb.disjointOccSet_eq]
  exact finite_bool_bk G p F hA hB

omit [Countable V] in
/-- Disjoint open edge certificates induce disjoint Boolean witnesses. -/
theorem finite_bool_witness_of_edge_certificates [DecidableEq V]
    (F K L : Finset (Sym2 V)) (ω : BondConfig V) {A B : Set (F → Bool)}
    (hKL : Disjoint K L)
    (hKω : (↑K : Set (Sym2 V)) ⊆ ω) (hLω : (↑L : Set (Sym2 V)) ⊆ ω)
    (hKA : finiteBoolConfig F (↑K : BondConfig V) ∈ A)
    (hLB : finiteBoolConfig F (↑L : BondConfig V) ∈ B) :
    finiteBoolConfig F ω ∈ LatticeProb.wit A B := by
  classical
  let K' : Finset F := F.attach.filter (fun i => i.val ∈ K)
  let L' : Finset F := F.attach.filter (fun i => i.val ∈ L)
  have hmemK (i : F) : i ∈ K' ↔ i.val ∈ K := by simp [K']
  have hmemL (i : F) : i ∈ L' ↔ i.val ∈ L := by simp [L']
  refine ⟨K', L', ?_, ?_, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro i hi hj
    exact (Finset.disjoint_left.mp hKL) ((hmemK i).mp hi) ((hmemL i).mp hj)
  · intro i hi
    change propBool (i.val ∈ ω) = true
    simp [propBool, hKω ((hmemK i).mp hi)]
  · intro i hi
    change propBool (i.val ∈ ω) = true
    simp [propBool, hLω ((hmemL i).mp hi)]
  · have heq : LatticeProb.indic K' = finiteBoolConfig F (↑K : BondConfig V) := by
      funext i
      simp [LatticeProb.indic, finiteBoolConfig, propBool, hmemK]
    rw [heq]
    exact hKA
  · have heq : LatticeProb.indic L' = finiteBoolConfig F (↑L : BondConfig V) := by
      funext i
      simp [LatticeProb.indic, finiteBoolConfig, propBool, hmemL]
    rw [heq]
    exact hLB

omit [Countable V] in
/-- A connection inside a finite volume has disjoint first-exit certificates
supported on the volume's internal edges. -/
theorem exists_first_exit_finite_volume_certificates
    {ω : BondConfig V} (S : Set V) (T : Finset V) {a z : V}
    (ha : a ∈ S) (hz : z ∉ S) (h : ω ∈ openConnIn (↑T : Set V) a z) :
    ∃ (x : V) (_ : x ∈ S) (y : V) (_ : y ∉ S) (K L : Finset (Sym2 V)),
      Disjoint K L ∧ (↑K : Set (Sym2 V)) ⊆ ω ∧ (↑L : Set (Sym2 V)) ⊆ ω ∧
      K ⊆ T.sym2 ∧ L ⊆ T.sym2 ∧ s(x, y) ∈ K ∧
      (↑K : BondConfig V) ∈ openConnIn S a x ∧
      (openGraph (↑L : BondConfig V)).Reachable y z := by
  classical
  let ω' : BondConfig V := ω ∩ (↑T.sym2 : Set (Sym2 V))
  have hconn : ω' ∈ openConnIn (↑T : Set V) a z := by
    apply ((determinedBy_iff _ _).mp (PlanarDuality.determinedBy_openConnIn T a z) ω ω' ?_).mp h
    simp [ω', Set.inter_assoc]
  obtain ⟨_, _, ⟨q⟩⟩ := hconn
  have hreach : (openGraph ω').Reachable a z :=
    ⟨(q.map (SimpleGraph.Embedding.induce (↑T : Set V)).toHom).copy rfl rfl⟩
  obtain ⟨x, hx, y, hy, K, L, hd, hk, hl, he, hc, hr⟩ :=
    exists_first_exit_disjoint_certificates S ha hz hreach
  refine ⟨x, hx, y, hy, K, L, hd, ?_, ?_, ?_, ?_, he, hc, hr⟩
  · exact hk.trans Set.inter_subset_left
  · exact hl.trans Set.inter_subset_left
  · intro e he'
    exact (hk he').2
  · intro e he'
    exact (hl he').2


/-- The set of open edges represented by finite Boolean coordinates. -/
def finiteBoolEdges (F : Finset (Sym2 V)) (η : F → Bool) : BondConfig V :=
  {e | ∃ i : F, i.val = e ∧ η i = true}

omit [Countable V] in
/-- Encoding and decoding a finite edge set preserves it when the coordinates contain it. -/
theorem finiteBoolEdges_finiteBoolConfig [DecidableEq V] (F K : Finset (Sym2 V))
    (hKF : K ⊆ F) : finiteBoolEdges F (finiteBoolConfig F (↑K : BondConfig V)) = ↑K := by
  classical
  ext e
  constructor
  · rintro ⟨i, rfl, hi⟩
    simpa [finiteBoolConfig, propBool] using hi
  · intro he
    refine ⟨⟨e, hKF he⟩, rfl, ?_⟩
    simp [finiteBoolConfig, propBool, he]

/-- An interior connection together with a specified exit edge. -/
def exitFiniteEvent (F : Finset (Sym2 V)) (S : Set V) (a x y : V) : Set (F → Bool) :=
  {η | finiteBoolEdges F η ∈ openConnIn S a x ∧ s(x, y) ∈ finiteBoolEdges F η}

/-- A connection starting at the outer endpoint of an exit edge. -/
def continuationFiniteEvent (F : Finset (Sym2 V)) (y z : V) : Set (F → Bool) :=
  {η | (openGraph (finiteBoolEdges F η)).Reachable y z}

omit [Countable V] in
/-- Adding open Boolean coordinates enlarges the encoded edge set. -/
theorem finiteBoolEdges_mono (F : Finset (Sym2 V)) : Monotone (finiteBoolEdges F) := by
  intro η η' h e he
  obtain ⟨i, rfl, hi⟩ := he
  refine ⟨i, rfl, ?_⟩
  have h' := h i
  rw [hi] at h'
  cases hv : η' i with
  | false => exact False.elim ((by decide : ¬ (true ≤ false)) (hv ▸ h'))
  | true => rfl

omit [Countable V] in
/-- The finite-coordinate exit event is increasing. -/
theorem exitFiniteEvent_upper (F : Finset (Sym2 V)) (S : Set V) (a x y : V) :
    IsUpperSet (exitFiniteEvent F S a x y) := by
  intro η η' h hη
  exact ⟨isUpperSet_openConnIn S a x (finiteBoolEdges_mono F h) hη.1,
    finiteBoolEdges_mono F h hη.2⟩

omit [Countable V] in
/-- The finite-coordinate continuation event is increasing. -/
theorem continuationFiniteEvent_upper (F : Finset (Sym2 V)) (y z : V) :
    IsUpperSet (continuationFiniteEvent F y z) := by
  intro η η' h hη
  exact hη.mono (openGraph_mono (finiteBoolEdges_mono F h))

omit [Countable V] in
/-- A connection leaving a set yields a disjoint occurrence at an exit edge. -/
theorem first_exit_finite_disjoint_occurrence [DecidableEq V]
    {ω : BondConfig V} (S : Set V) (T : Finset V) {a z : V}
    (ha : a ∈ S) (hz : z ∉ S) (h : ω ∈ openConnIn (↑T : Set V) a z) :
    ∃ x ∈ T, x ∈ S ∧ ∃ y ∈ T, y ∉ S ∧ finiteBoolConfig T.sym2 ω ∈
      LatticeProb.wit (exitFiniteEvent T.sym2 S a x y) (continuationFiniteEvent T.sym2 y z) := by
  obtain ⟨x, hx, y, hy, K, L, hd, hk, hl, hkt, hlt, he, hc, hr⟩ :=
    exists_first_exit_finite_volume_certificates S T ha hz h
  have hxy := Finset.mk_mem_sym2_iff.mp (hkt he)
  refine ⟨x, hxy.1, hx, y, hxy.2, hy,
    finite_bool_witness_of_edge_certificates T.sym2 K L ω hd hk hl ?_ ?_⟩
  · change finiteBoolEdges T.sym2 (finiteBoolConfig T.sym2 (↑K : BondConfig V)) ∈
      openConnIn S a x ∧ s(x, y) ∈ finiteBoolEdges T.sym2 (finiteBoolConfig T.sym2 (↑K : BondConfig V))
    rw [finiteBoolEdges_finiteBoolConfig _ _ hkt]
    exact ⟨hc, he⟩
  · change (openGraph (finiteBoolEdges T.sym2 (finiteBoolConfig T.sym2 (↑L : BondConfig V)))).Reachable y z
    rw [finiteBoolEdges_finiteBoolConfig _ _ hlt]
    exact hr

/-- Ordered pairs of vertices in the volume crossing the boundary of a set. -/
def finiteBoundaryPairs [DecidableEq V] (S : Set V) (T : Finset V) : Finset (V × V) := by
  classical
  exact (T.product T).filter (fun xy => xy.1 ∈ S ∧ xy.2 ∉ S)

omit [Countable V] in
/-- The finite-volume first-exit bound obtained from the BK inequality. -/
theorem finite_volume_first_exit_bk [DecidableEq V]
    (G : SimpleGraph V) (p : unitInterval) (S : Set V) (T : Finset V) (a z : V)
    (ha : a ∈ S) (hz : z ∉ S) :
    (bondPercolation G p) (openConnIn (↑T : Set V) a z) ≤
      ∑ xy ∈ finiteBoundaryPairs S T,
        (bondPercolation G p) (finiteBoolConfig T.sym2 ⁻¹' exitFiniteEvent T.sym2 S a xy.1 xy.2) *
        (bondPercolation G p) (finiteBoolConfig T.sym2 ⁻¹' continuationFiniteEvent T.sym2 xy.2 z) := by
  classical
  let A : V × V → Set (BondConfig V) := fun xy =>
    finiteBoolConfig T.sym2 ⁻¹' LatticeProb.wit
      (exitFiniteEvent T.sym2 S a xy.1 xy.2) (continuationFiniteEvent T.sym2 xy.2 z)
  have hsub : openConnIn (↑T : Set V) a z ⊆ ⋃ xy ∈ finiteBoundaryPairs S T, A xy := by
    intro ω hω
    obtain ⟨x, hxT, hx, y, hyT, hy, hw⟩ :=
      first_exit_finite_disjoint_occurrence S T ha hz hω
    apply Set.mem_iUnion.mpr
    refine ⟨(x, y), Set.mem_iUnion.mpr ⟨?_, hw⟩⟩
    simp [finiteBoundaryPairs, hxT, hyT, hx, hy]
  calc
    (bondPercolation G p) (openConnIn (↑T : Set V) a z) ≤
        (bondPercolation G p) (⋃ xy ∈ finiteBoundaryPairs S T, A xy) := measure_mono hsub
    _ ≤ ∑ xy ∈ finiteBoundaryPairs S T, (bondPercolation G p) (A xy) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ xy ∈ finiteBoundaryPairs S T,
        (bondPercolation G p) (finiteBoolConfig T.sym2 ⁻¹' exitFiniteEvent T.sym2 S a xy.1 xy.2) *
        (bondPercolation G p) (finiteBoolConfig T.sym2 ⁻¹' continuationFiniteEvent T.sym2 xy.2 z) := by
      apply Finset.sum_le_sum
      intro xy _
      exact finite_bool_witness_bk G p T.sym2 (exitFiniteEvent_upper _ _ _ _ _)
        (continuationFiniteEvent_upper _ _ _)


omit [Countable V] in
/-- Decoding restricted coordinates keeps exactly the selected edges. -/
theorem finiteBoolEdges_config (F : Finset (Sym2 V)) (ω : BondConfig V) :
    finiteBoolEdges F (finiteBoolConfig F ω) = ω ∩ (↑F : Set (Sym2 V)) := by
  classical
  ext e
  constructor
  · rintro ⟨i, rfl, hi⟩
    exact ⟨by simpa [finiteBoolConfig, propBool] using hi, i.property⟩
  · rintro ⟨heω, heF⟩
    exact ⟨⟨e, heF⟩, rfl, by simpa [finiteBoolConfig, propBool] using heω⟩

omit [Countable V] in
/-- Restricting to a volume containing the interior set preserves the exit event. -/
theorem exitFiniteEvent_preimage (S T : Finset V) (a x y : V)
    (hST : S ⊆ T) (hxT : x ∈ T) (hyT : y ∈ T) :
    finiteBoolConfig T.sym2 ⁻¹' exitFiniteEvent T.sym2 (↑S : Set V) a x y =
      openConnIn (↑S : Set V) a x ∩ {ω | s(x, y) ∈ ω} := by
  classical
  ext ω
  have hdet := (determinedBy_iff _ _).mp (PlanarDuality.determinedBy_openConnIn S a x)
  have hint : ω ∩ (↑T.sym2 : Set (Sym2 V)) ∩ (↑S.sym2 : Set (Sym2 V)) =
      ω ∩ (↑S.sym2 : Set (Sym2 V)) := by
    ext e
    simp only [Set.mem_inter_iff, Finset.mem_coe]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, Finset.sym2_mono hST h.2⟩, h.2⟩⟩
  have hconn := hdet (ω ∩ (↑T.sym2 : Set (Sym2 V))) ω hint
  simp only [Set.mem_preimage, exitFiniteEvent, Set.mem_ofPred_eq, Set.mem_inter_iff]
  rw [finiteBoolEdges_config, hconn]
  simp [hxT, hyT]

/-- The exit event factors into its interior connection probability and `p`. -/
theorem exitFiniteEvent_probability (G : SimpleGraph V) (p : unitInterval)
    (S T : Finset V) (a x y : V) (hST : S ⊆ T) (hxT : x ∈ T) (hyT : y ∈ T)
    (hy : y ∉ S) (he : s(x, y) ∈ G.edgeSet) :
    (bondPercolation G p).real
        (finiteBoolConfig T.sym2 ⁻¹' exitFiniteEvent T.sym2 (↑S : Set V) a x y) =
      (p : ℝ) * (bondPercolation G p).real (openConnIn (↑S : Set V) a x) := by
  rw [exitFiniteEvent_preimage S T a x y hST hxT hyT]
  exact interior_connection_inter_boundary_edge G p S a x x y hy he

omit [Countable V] in
/-- A restricted continuation is also an unrestricted connection. -/
theorem continuationFiniteEvent_subset (F : Finset (Sym2 V)) (y z : V) :
    finiteBoolConfig F ⁻¹' continuationFiniteEvent F y z ⊆ openConn y z := by
  intro ω hω
  change (openGraph (finiteBoolEdges F (finiteBoolConfig F ω))).Reachable y z at hω
  change (openGraph ω).Reachable y z
  rw [finiteBoolEdges_config] at hω
  exact hω.mono (openGraph_mono Set.inter_subset_left)

/-- The exit-event factorization as an extended nonnegative real equality. -/
theorem exitFiniteEvent_measure (G : SimpleGraph V) (p : unitInterval)
    (S T : Finset V) (a x y : V) (hST : S ⊆ T) (hxT : x ∈ T) (hyT : y ∈ T)
    (hy : y ∉ S) (he : s(x, y) ∈ G.edgeSet) :
    (bondPercolation G p)
        (finiteBoolConfig T.sym2 ⁻¹' exitFiniteEvent T.sym2 (↑S : Set V) a x y) =
      ENNReal.ofReal (p : ℝ) * (bondPercolation G p) (openConnIn (↑S : Set V) a x) := by
  have h := exitFiniteEvent_probability G p S T a x y hST hxT hyT hy he
  rw [measureReal_def, measureReal_def] at h
  have h' := congrArg ENNReal.ofReal h
  rw [ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_mul p.property.1,
    ENNReal.ofReal_toReal (measure_ne_top _ _)] at h'
  exact h'


/-- A nonedge cannot occur in an exit event under the bond law. -/
theorem exitFiniteEvent_measure_zero (G : SimpleGraph V) (p : unitInterval)
    (F : Finset (Sym2 V)) (S : Set V) (a x y : V)
    (he : s(x, y) ∉ G.edgeSet) :
    (bondPercolation G p) (finiteBoolConfig F ⁻¹' exitFiniteEvent F S a x y) = 0 := by
  classical
  have hae : ∀ᵐ ω ∂bondPercolation G p, ω ⊆ G.edgeSet := by
    simpa [bondPercolation] using
      (ProbabilityTheory.setBernoulli_ae_subset (u := G.edgeSet) (p := p))
  have hnull : (bondPercolation G p) {ω | ¬ ω ⊆ G.edgeSet} = 0 := by
    simpa only [ae_iff, Set.compl_ofPred] using hae
  apply measure_mono_null _ hnull
  intro ω hω
  have hmem : s(x, y) ∈ finiteBoolEdges F (finiteBoolConfig F ω) := hω.2
  rw [finiteBoolEdges_config] at hmem
  exact fun hs => he (hs hmem.1)

/-- Oriented graph edges leaving the set inside the finite volume. -/
def finiteBoundaryEdges [DecidableEq V] (G : SimpleGraph V) (S : Set V)
    (T : Finset V) : Finset (V × V) := by
  classical
  exact (finiteBoundaryPairs S T).filter (fun xy => s(xy.1, xy.2) ∈ G.edgeSet)

/-- A finite-volume connection is bounded by a sum over oriented boundary edges. -/
theorem finite_volume_first_exit_edge_sum [DecidableEq V]
    (G : SimpleGraph V) (p : unitInterval) (S T : Finset V) (a z : V)
    (hST : S ⊆ T) (ha : a ∈ S) (hz : z ∉ S) :
    (bondPercolation G p) (openConnIn (↑T : Set V) a z) ≤
      ∑ xy ∈ finiteBoundaryEdges G (↑S : Set V) T,
        ENNReal.ofReal (p : ℝ) *
          (bondPercolation G p) (openConnIn (↑S : Set V) a xy.1) *
          (bondPercolation G p) (openConn xy.2 z) := by
  classical
  let term : V × V → ENNReal := fun xy =>
    (bondPercolation G p) (finiteBoolConfig T.sym2 ⁻¹' exitFiniteEvent T.sym2 (↑S : Set V) a xy.1 xy.2) *
      (bondPercolation G p) (finiteBoolConfig T.sym2 ⁻¹' continuationFiniteEvent T.sym2 xy.2 z)
  have hfilter : ∑ xy ∈ finiteBoundaryPairs (↑S : Set V) T, term xy =
      ∑ xy ∈ finiteBoundaryEdges G (↑S : Set V) T, term xy := by
    rw [finiteBoundaryEdges, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro xy _
    by_cases he : s(xy.1, xy.2) ∈ G.edgeSet
    · simp [he]
    · simp [he, term, exitFiniteEvent_measure_zero G p T.sym2 (↑S : Set V) a xy.1 xy.2 he]
  calc
    (bondPercolation G p) (openConnIn (↑T : Set V) a z) ≤
        ∑ xy ∈ finiteBoundaryPairs (↑S : Set V) T, term xy :=
      finite_volume_first_exit_bk G p (↑S : Set V) T a z ha hz
    _ = ∑ xy ∈ finiteBoundaryEdges G (↑S : Set V) T, term xy := hfilter
    _ ≤ ∑ xy ∈ finiteBoundaryEdges G (↑S : Set V) T,
        ENNReal.ofReal (p : ℝ) *
          (bondPercolation G p) (openConnIn (↑S : Set V) a xy.1) *
          (bondPercolation G p) (openConn xy.2 z) := by
      apply Finset.sum_le_sum
      intro xy hxy
      simp only [finiteBoundaryEdges, Finset.mem_filter, finiteBoundaryPairs,
        Finset.mem_coe] at hxy
      have hT := Finset.mem_product.mp hxy.1.1
      have hy : xy.2 ∉ S := hxy.1.2.2
      change _ * _ ≤ _ * _
      rw [exitFiniteEvent_measure G p S T a xy.1 xy.2 hST hT.1 hT.2 hy hxy.2]
      gcongr
      exact continuationFiniteEvent_subset T.sym2 xy.2 z


/-- Connection to at least one vertex of a target set. -/
def openConnTo (U : Set V) (a : V) : Set (BondConfig V) :=
  {ω | ∃ z ∈ U, (openGraph ω).Reachable a z}

/-- Connection to a target set by a path inside a specified set. -/
def openConnInTo (T U : Set V) (a : V) : Set (BondConfig V) :=
  {ω | ∃ z ∈ U, ω ∈ openConnIn T a z}

/-- A finite-coordinate connection to a target set. -/
def continuationFiniteEventTo (F : Finset (Sym2 V)) (U : Set V) (y : V) :
    Set (F → Bool) :=
  {η | ∃ z ∈ U, (openGraph (finiteBoolEdges F η)).Reachable y z}

omit [Countable V] in
/-- Finite-coordinate connection to a target set is increasing. -/
theorem continuationFiniteEventTo_upper (F : Finset (Sym2 V)) (U : Set V) (y : V) :
    IsUpperSet (continuationFiniteEventTo F U y) := by
  intro η η' h hη
  obtain ⟨z, hz, hconn⟩ := hη
  exact ⟨z, hz, hconn.mono (openGraph_mono (finiteBoolEdges_mono F h))⟩

omit [Countable V] in
/-- A finite-coordinate connection to a target is an unrestricted connection. -/
theorem continuationFiniteEventTo_subset (F : Finset (Sym2 V)) (U : Set V) (y : V) :
    finiteBoolConfig F ⁻¹' continuationFiniteEventTo F U y ⊆ openConnTo U y := by
  intro ω hω
  obtain ⟨z, hz, hconn⟩ := hω
  exact ⟨z, hz, continuationFiniteEvent_subset F y z hconn⟩

omit [Countable V] in
/-- A finite-volume connection to a disjoint target gives disjoint exit witnesses. -/
theorem first_exit_finite_disjoint_occurrence_to [DecidableEq V]
    {ω : BondConfig V} (S U : Set V) (T : Finset V) {a : V}
    (ha : a ∈ S) (hUS : Disjoint U S) (h : ω ∈ openConnInTo (↑T : Set V) U a) :
    ∃ x ∈ T, x ∈ S ∧ ∃ y ∈ T, y ∉ S ∧ finiteBoolConfig T.sym2 ω ∈
      LatticeProb.wit (exitFiniteEvent T.sym2 S a x y) (continuationFiniteEventTo T.sym2 U y) := by
  classical
  obtain ⟨z, hz, hconn⟩ := h
  have hzS : z ∉ S := fun hzS => (Set.disjoint_left.mp hUS) hz hzS
  obtain ⟨x, hxT, hxS, y, hyT, hyS, K, L, hd, hk, hl, hKA, hLB⟩ :=
    first_exit_finite_disjoint_occurrence S T ha hzS hconn
  exact ⟨x, hxT, hxS, y, hyT, hyS, K, L, hd, hk, hl, hKA, z, hz, hLB⟩

omit [Countable V] in
/-- The BK first-exit bound for a connection to a disjoint target set. -/
theorem finite_volume_first_exit_to_bk [DecidableEq V]
    (G : SimpleGraph V) (p : unitInterval) (S U : Set V) (T : Finset V) (a : V)
    (ha : a ∈ S) (hUS : Disjoint U S) :
    (bondPercolation G p) (openConnInTo (↑T : Set V) U a) ≤
      ∑ xy ∈ finiteBoundaryPairs S T,
        (bondPercolation G p) (finiteBoolConfig T.sym2 ⁻¹' exitFiniteEvent T.sym2 S a xy.1 xy.2) *
        (bondPercolation G p) (finiteBoolConfig T.sym2 ⁻¹' continuationFiniteEventTo T.sym2 U xy.2) := by
  classical
  let A : V × V → Set (BondConfig V) := fun xy =>
    finiteBoolConfig T.sym2 ⁻¹' LatticeProb.wit
      (exitFiniteEvent T.sym2 S a xy.1 xy.2) (continuationFiniteEventTo T.sym2 U xy.2)
  have hsub : openConnInTo (↑T : Set V) U a ⊆ ⋃ xy ∈ finiteBoundaryPairs S T, A xy := by
    intro ω hω
    obtain ⟨x, hxT, hx, y, hyT, hy, hw⟩ :=
      first_exit_finite_disjoint_occurrence_to S U T ha hUS hω
    apply Set.mem_iUnion.mpr
    refine ⟨(x, y), Set.mem_iUnion.mpr ⟨?_, hw⟩⟩
    simp [finiteBoundaryPairs, hxT, hyT, hx, hy]
  calc
    (bondPercolation G p) (openConnInTo (↑T : Set V) U a) ≤
        (bondPercolation G p) (⋃ xy ∈ finiteBoundaryPairs S T, A xy) := measure_mono hsub
    _ ≤ ∑ xy ∈ finiteBoundaryPairs S T, (bondPercolation G p) (A xy) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ xy ∈ finiteBoundaryPairs S T,
        (bondPercolation G p) (finiteBoolConfig T.sym2 ⁻¹' exitFiniteEvent T.sym2 S a xy.1 xy.2) *
        (bondPercolation G p) (finiteBoolConfig T.sym2 ⁻¹' continuationFiniteEventTo T.sym2 U xy.2) := by
      apply Finset.sum_le_sum
      intro xy _
      exact finite_bool_witness_bk G p T.sym2 (exitFiniteEvent_upper _ _ _ _ _)
        (continuationFiniteEventTo_upper _ _ _)

/-- A finite-volume target connection is bounded by a boundary-edge sum. -/
theorem finite_volume_first_exit_to_edge_sum [DecidableEq V]
    (G : SimpleGraph V) (p : unitInterval) (S T : Finset V) (U : Set V) (a : V)
    (hST : S ⊆ T) (ha : a ∈ S) (hUS : Disjoint U (↑S : Set V)) :
    (bondPercolation G p) (openConnInTo (↑T : Set V) U a) ≤
      ∑ xy ∈ finiteBoundaryEdges G (↑S : Set V) T,
        ENNReal.ofReal (p : ℝ) *
          (bondPercolation G p) (openConnIn (↑S : Set V) a xy.1) *
          (bondPercolation G p) (openConnTo U xy.2) := by
  classical
  let term : V × V → ENNReal := fun xy =>
    (bondPercolation G p) (finiteBoolConfig T.sym2 ⁻¹' exitFiniteEvent T.sym2 (↑S : Set V) a xy.1 xy.2) *
      (bondPercolation G p) (finiteBoolConfig T.sym2 ⁻¹' continuationFiniteEventTo T.sym2 U xy.2)
  have hfilter : ∑ xy ∈ finiteBoundaryPairs (↑S : Set V) T, term xy =
      ∑ xy ∈ finiteBoundaryEdges G (↑S : Set V) T, term xy := by
    rw [finiteBoundaryEdges, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro xy _
    by_cases he : s(xy.1, xy.2) ∈ G.edgeSet
    · simp [he]
    · simp [he, term, exitFiniteEvent_measure_zero G p T.sym2 (↑S : Set V) a xy.1 xy.2 he]
  calc
    (bondPercolation G p) (openConnInTo (↑T : Set V) U a) ≤
        ∑ xy ∈ finiteBoundaryPairs (↑S : Set V) T, term xy :=
      finite_volume_first_exit_to_bk G p (↑S : Set V) U T a ha hUS
    _ = ∑ xy ∈ finiteBoundaryEdges G (↑S : Set V) T, term xy := hfilter
    _ ≤ ∑ xy ∈ finiteBoundaryEdges G (↑S : Set V) T,
        ENNReal.ofReal (p : ℝ) *
          (bondPercolation G p) (openConnIn (↑S : Set V) a xy.1) *
          (bondPercolation G p) (openConnTo U xy.2) := by
      apply Finset.sum_le_sum
      intro xy hxy
      simp only [finiteBoundaryEdges, Finset.mem_filter, finiteBoundaryPairs,
        Finset.mem_coe] at hxy
      have hT := Finset.mem_product.mp hxy.1.1
      have hy : xy.2 ∉ S := hxy.1.2.2
      change _ * _ ≤ _ * _
      rw [exitFiniteEvent_measure G p S T a xy.1 xy.2 hST hT.1 hT.2 hy hxy.2]
      gcongr
      exact continuationFiniteEventTo_subset T.sym2 U xy.2


end FiniteSizeOneArm
