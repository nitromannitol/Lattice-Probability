/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.CellularFacts.Basic at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.LFMultigraph
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Adj
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsConnectedSet
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.VerticesMeeting
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.PlaneDiam
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsPlaneData
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.CellularEmbedding

/-!
# §5: basic facts on cellular embeddings, Lemmas 5.1 and 5.2

* `isPlaneData_cell`: the cells of a cellular embedding are §3 plane data.
* `infinite_of_cellularEmbedding`: the vertex type of a cellular embedding is infinite (finitely many compact cells
  cannot cover `ℂ`).
* `isCompact_cellUnion`, `isConnected_cellUnion`: `U_A^ℋ` is compact for finite `A` and connected for connected `A`.
* `norm_le_planeDiam`: if `o ∈ A` then `U_A^ℋ ⊆ B̄_{D_ℋ(A)}(0)` (because `0 ∈ H_o`).
* `nbhd_subset_closedBall` (**the neighbourhood bound**) and `exists_walk_between_spheres` (**the sphere-crossing lemma**, corrected form: the
  hypotheses `a > 0`, `a < b` are unnecessary; the proof uses compactness of `U_A^ℋ`).
-/

set_option autoImplicit false

noncomputable section

open Metric Set

namespace MatedCRTHarmonic.CellularFacts

variable {V E : Type*} {G : LFMultigraph V E} {o : V}

/-- The cells of a cellular embedding are §3 plane data (the planar argument "plane-data compatibility"). -/
theorem isPlaneData_cell (H : CellularEmbedding G o) : G.IsPlaneData H.cell where
  isConnected := H.isConnected_cell
  isBounded x := (H.isCompact_cell x).isBounded
  locallyFinite := H.locallyFinite_cell
  inter_of_adj := H.inter_of_adj

/-- The vertex type of a cellular embedding is infinite: finitely many compact cells have compact union, which is not
`ℂ = ⋃ cells` (the planar argument (a1)(ii)). -/
theorem infinite_of_cellularEmbedding (H : CellularEmbedding G o) : Infinite V := by
  by_contra hfin
  rw [not_infinite_iff_finite] at hfin
  have hc : IsCompact (⋃ x, H.cell x) := isCompact_iUnion H.isCompact_cell
  rw [H.iUnion_cell] at hc
  exact noncompact_univ ℂ hc

/-- `U_A^ℋ = ⋃_{x ∈ A} H_x` is compact for finite `A`. -/
theorem isCompact_cellUnion (H : CellularEmbedding G o) (A : Finset V) :
    IsCompact (⋃ x ∈ (A : Set V), H.cell x) :=
  A.finite_toSet.isCompact_biUnion fun x _ => H.isCompact_cell x

/-- `U_A^ℋ` is connected when the induced subgraph on `A` is connected (the planar argument N1, (a1)(iv)): adjacent
cells intersect, so the cells of `A` form a chain of pairwise-intersecting connected sets. -/
theorem isConnected_cellUnion (H : CellularEmbedding G o) {A : Set V} (hA : G.IsConnectedSet A) :
    IsConnected (⋃ x ∈ A, H.cell x) := by
  have hne : A.Nonempty := by
    obtain ⟨⟨x, hx⟩⟩ := hA.nonempty
    exact ⟨x, hx⟩
  refine IsConnected.biUnion_of_reflTransGen hne (fun i _ => H.isConnected_cell i) ?_
  intro i hi j hj
  have hr : (G.adj.induce A).Reachable ⟨i, hi⟩ ⟨j, hj⟩ := hA.preconnected _ _
  rw [SimpleGraph.reachable_iff_reflTransGen] at hr
  refine Relation.ReflTransGen.lift
    (p := fun i j => (H.cell i ∩ H.cell j).Nonempty ∧ i ∈ A) Subtype.val ?_ _ _ hr
  intro a b hab
  exact ⟨H.inter_of_adj _ _ hab, a.2⟩

/-- If `o ∈ A`, every point of `U_A^ℋ` has norm at most `D_ℋ(A)` (`0 ∈ H_o ⊆ U_A^ℋ`; the planar argument P53.2). -/
theorem norm_le_planeDiam (H : CellularEmbedding G o) {A : Finset V} (hoA : o ∈ A) {x : V} (hx : x ∈ A)
    {y : ℂ} (hy : y ∈ H.cell x) : ‖y‖ ≤ planeDiam H.cell A := by
  have h0 : (0 : ℂ) ∈ ⋃ x ∈ (A : Set V), H.cell x :=
    mem_biUnion (Finset.mem_coe.2 hoA) H.zero_mem_root
  have hy' : y ∈ ⋃ x ∈ (A : Set V), H.cell x := mem_biUnion (Finset.mem_coe.2 hx) hy
  have h := dist_le_diam_of_mem (isCompact_cellUnion H A).isBounded hy' h0
  rwa [dist_zero_right] at h

/-- **the sphere-crossing lemma** (the planar argument L52, corrected proof (a3)): let `A` be finite and connected,
`D = D_ℋ(A) = diam U_A^ℋ`, and `dist(z, U_A^ℋ) ≤ a ≤ b ≤ D/2`. Then `A` contains a graph path joining
`𝒱_ℋ(∂B_a(z))` to `𝒱_ℋ(∂B_b(z))`. The proof does not need `a > 0` or `a < b`. -/
theorem exists_walk_between_spheres (H : CellularEmbedding G o) {A : Finset V}
    (hA : G.IsConnectedSet A) {z : ℂ} {a b : ℝ}
    (ha : infDist z (⋃ x ∈ (A : Set V), H.cell x) ≤ a) (hab : a ≤ b)
    (hb : b ≤ planeDiam H.cell A / 2) :
    ∃ x ∈ verticesMeeting H.cell (sphere z a), ∃ y ∈ verticesMeeting H.cell (sphere z b),
      ∃ q : G.adj.Walk x y, ∀ w ∈ q.support, w ∈ A := by
  set U := ⋃ x ∈ (A : Set V), H.cell x with hU
  have hUc : IsCompact U := isCompact_cellUnion H A
  have hUconn : IsConnected U := isConnected_cellUnion H hA
  have hUne : U.Nonempty := hUconn.nonempty
  have hf : ContinuousOn (fun y : ℂ => dist y z) U := (continuous_id.dist continuous_const).continuousOn
  obtain ⟨y₀, hy₀U, hy₀⟩ := hUc.exists_infDist_eq_dist hUne z
  obtain ⟨y₁, hy₁U, hy₁max⟩ := hUc.exists_isMaxOn hUne hf
  have hmax : ∀ y ∈ U, dist y z ≤ dist y₁ z := fun y hy => hy₁max hy
  have hdiam : planeDiam H.cell A ≤ 2 * dist y₁ z := by
    show diam U ≤ 2 * dist y₁ z
    refine diam_le_of_forall_dist_le (by positivity) fun y hy y' hy' => ?_
    calc dist y y' ≤ dist y z + dist y' z := dist_triangle_right _ _ _
      _ ≤ dist y₁ z + dist y₁ z := add_le_add (hmax y hy) (hmax y' hy')
      _ = 2 * dist y₁ z := by ring
  have hf0 : dist y₀ z ≤ a := by rw [dist_comm, ← hy₀]; exact ha
  have hf1 : b ≤ dist y₁ z := by linarith
  have hivt := hUconn.isPreconnected.intermediate_value hy₀U hy₁U hf
  obtain ⟨ya, hyaU, hya⟩ := hivt ⟨hf0, hab.trans hf1⟩
  obtain ⟨yb, hybU, hyb⟩ := hivt ⟨hf0.trans hab, hf1⟩
  rw [hU, mem_iUnion₂] at hyaU hybU
  obtain ⟨wa, hwaA, hya'⟩ := hyaU
  obtain ⟨wb, hwbA, hyb'⟩ := hybU
  obtain ⟨q⟩ : (G.adj.induce (A : Set V)).Reachable ⟨wa, hwaA⟩ ⟨wb, hwbA⟩ := hA.preconnected _ _
  refine ⟨wa, ⟨ya, hya', ?_⟩, wb, ⟨yb, hyb', ?_⟩,
    q.map (SimpleGraph.Embedding.induce (A : Set V)).toHom, ?_⟩
  · rw [mem_sphere]; exact hya
  · rw [mem_sphere]; exact hyb
  · intro w hw
    have hw' : w ∈ (q.map (SimpleGraph.Embedding.induce (A : Set V)).toHom).support := hw
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hw'
    obtain ⟨w', _, rfl⟩ := hw'
    exact w'.2

end MatedCRTHarmonic.CellularFacts
