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


end FiniteSizeOneArm
