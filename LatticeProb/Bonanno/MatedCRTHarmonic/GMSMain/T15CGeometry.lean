/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSMain.T15CGeometry at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.RCorollaryB
import LatticeProb.Bonanno.MatedCRTHarmonic.GoodScales.Geometry
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS3.Cells

/-!
# [18] Theorem 3.9, boundary estimate: the geometric step

Source: Gwynne–Miller–Sheffield, *Harmonic functions on mated-CRT maps* [18], proof of Theorem 3.9, `[18]`: "if `x ∈ VG^ε(D)` and
`r ≥ 2 dist(η(x), ∂D)`, then since `C \ D` is connected, in order for a random walk started from `x` to disconnect
`VG^ε(B_{r/2}(0))` from `∞`, it must first hit `VG^ε(∂D)`" (read: `B_{r/2}(η(x))`, and "disconnect
`V(∂B_{r/2}(η(x)))` from `V(∂B_{2r}(η(x)))`", the event of (3.35)).

Everything here is deterministic and stated for a cellular embedding `H` of a graph `G` (frozen
`CellularEmbedding`) with the cell-topology property (LC) `H.PointConnected` (Core interface; TF2's Theorem B proves
it for the mated-CRT cells, `RouteM.pointConnected_of_peanosphere_holds`).

* `t15c_exists_walk_of_isConnected`: under (LC), two vertices whose cells meet a connected set `C` are joined by a
  graph walk all of whose vertices have cells meeting `C` (TF2's Corollary B′,
  `RouteM.connected_induce_verticesMeeting`).
* `t15c_exists_mem_not_subset_of_disconnects` (**the key geometric step**): if `ℂ \ D` is preconnected, contains a
  point within distance `a` of `z` and a point at distance `≥ b ≥ a` from `z`, then every vertex set `U` which
  graph-disconnects `V(∂B_a(z))` from `V(∂B_b(z))` contains a vertex whose cell is not contained in `D`. Reason: the
  cells meeting `ℂ \ D` contain a graph walk from `V(∂B_a(z))` to `V(∂B_b(z))` (Corollary B′), which `U` must meet.
* `t15c_exists_frontier_of_not_subset` (**chain step**): along a vertex path whose consecutive vertices are equal or
  adjacent and whose first cell meets the open set `D`, the first cell not contained in `D` is preceded (weakly) by a
  cell meeting `∂D` (cells are connected and adjacent cells intersect).
* `t15c_cell_subset_ball_of_forall_not_meet` (**confinement**): along such a path starting in a cell containing `z`,
  as long as no cell meets `∂B_b(z)`, every cell lies in `B_b(z)`.

Comparison with [18]: [18] asserts the key step for the "trace" of the walk with no cell-topology input. In the
graph-disconnection sense of (3.35) (Lemma 3.10 needs graph disconnection) the step needs the cells meeting the
connected set `ℂ \ D` to form a connected subgraph, i.e. (LC) or an equivalent property. Cells meeting a set but not adjacent along it would break it. For the mated-CRT map (LC)
is TF2's Theorem B.
-/

set_option autoImplicit false

noncomputable section

open Set Metric

namespace MatedCRTHarmonic.GMSMain

open LFMultigraph GoodScales

variable {V E : Type*} {G : LFMultigraph V E} {o : V}

/-! ### Corollary B′ in walk form -/

/-- Under (LC), two vertices whose cells meet a connected set `C` are joined by a graph walk of `G.adj` all of whose
vertices have cells meeting `C`. -/
theorem t15c_exists_walk_of_isConnected {H : CellularEmbedding G o} (hLC : H.PointConnected) {C : Set ℂ}
    (hC : IsConnected C) {u v : V} (hu : u ∈ verticesMeeting H.cell C) (hv : v ∈ verticesMeeting H.cell C) :
    ∃ w : G.adj.Walk u v, ∀ y ∈ w.support, y ∈ verticesMeeting H.cell C := by
  have hconn := RouteM.connected_induce_verticesMeeting hLC hC
  obtain ⟨w⟩ := hconn.preconnected ⟨u, hu⟩ ⟨v, hv⟩
  refine ⟨w.map (SimpleGraph.Embedding.induce (verticesMeeting H.cell C)).toHom, fun y hy => ?_⟩
  have hy' : y ∈ w.support.map (SimpleGraph.Embedding.induce (G := G.adj)
      (verticesMeeting H.cell C)).toHom := by
    rwa [← SimpleGraph.Walk.support_map]
  obtain ⟨y', -, rfl⟩ := List.mem_map.mp hy'
  exact y'.2

/-- A cell containing a given point (cells cover `ℂ`). -/
theorem t15c_exists_mem_cell (H : CellularEmbedding G o) (q : ℂ) : ∃ x, q ∈ H.cell x :=
  RouteM.exists_mem_cell_of_cover H q

/-! ### The key geometric step -/

/-- **The key geometric step of [18] (3.31)**. Let `ℂ \ D` be preconnected, with a point `w₀`
within distance `a` of `z` and a point `w₁` at distance `≥ b` from `z`, where `a ≤ b`. Under (LC), every vertex set
`U` which graph-disconnects `V(∂B_a(z))` from `V(∂B_b(z))` contains a vertex whose cell is not contained in `D`. -/
theorem t15c_exists_mem_not_subset_of_disconnects {H : CellularEmbedding G o} (hLC : H.PointConnected)
    {D : Set ℂ} (hD : IsPreconnected Dᶜ) {z : ℂ} {a b : ℝ} (hab : a ≤ b) {w₀ w₁ : ℂ} (hw₀ : w₀ ∉ D)
    (hw₀a : dist w₀ z ≤ a) (hw₁ : w₁ ∉ D) (hw₁b : b ≤ dist w₁ z) {U : Set V}
    (hU : G.Disconnects U (verticesMeeting H.cell (sphere z a)) (verticesMeeting H.cell (sphere z b))) :
    ∃ y ∈ U, ¬ H.cell y ⊆ D := by
  have hC : IsConnected Dᶜ := ⟨⟨w₀, hw₀⟩, hD⟩
  -- `ℂ \ D` meets both circles
  obtain ⟨qa, hqaD, hqa⟩ := inter_sphere_nonempty_of_isPreconnected hD (show w₁ ∈ Dᶜ from hw₁)
    (show w₀ ∈ Dᶜ from hw₀) (hab.trans hw₁b) hw₀a
  obtain ⟨qb, hqbD, hqb⟩ := inter_sphere_nonempty_of_isPreconnected hD (show w₁ ∈ Dᶜ from hw₁)
    (show w₀ ∈ Dᶜ from hw₀) hw₁b (hw₀a.trans hab)
  obtain ⟨u, hu⟩ := t15c_exists_mem_cell H qa
  obtain ⟨v, hv⟩ := t15c_exists_mem_cell H qb
  obtain ⟨w, hw⟩ := t15c_exists_walk_of_isConnected hLC hC (u := u) (v := v) ⟨qa, hu, hqaD⟩ ⟨qb, hv, hqbD⟩
  obtain ⟨y, hyw, hyU⟩ := hU u ⟨qa, hu, hqa⟩ v ⟨qb, hv, hqb⟩ w
  refine ⟨y, hyU, fun hsub => ?_⟩
  obtain ⟨q, hq, hqD⟩ := hw y hyw
  exact hqD (hsub hq)

/-! ### Paths of cells -/

/-- The cells at the two ends of an admissible step intersect. -/
theorem t15c_inter_nonempty_of_stepOK (H : CellularEmbedding G o) {x y : V} (h : StepOK G x y) :
    (H.cell x ∩ H.cell y).Nonempty := by
  rcases h with rfl | h
  · rw [Set.inter_self]
    exact GMS3.cell_nonempty H _
  · exact H.inter_of_adj x y h

/-- **Chain step.** Let `D` be open. Along a vertex path `X` with admissible steps whose first cell meets `D`: if no
cell up to time `m` meets `∂D`, then every cell up to time `m` lies in `D`. -/
theorem t15c_cell_subset_of_forall_not_meet_frontier (H : CellularEmbedding G o) {D : Set ℂ} (hDo : IsOpen D)
    {X : ℕ → V} (hX : ∀ n, StepOK G (X n) (X (n + 1))) (h0 : (H.cell (X 0) ∩ D).Nonempty) :
    ∀ m, (∀ k ≤ m, ¬ (H.cell (X k) ∩ frontier D).Nonempty) → ∀ k ≤ m, H.cell (X k) ⊆ D := by
  intro m
  induction m with
  | zero =>
    intro hfr k hk
    rw [Nat.le_zero.mp hk]
    exact GMS3.cell_subset_of_inter_frontier_eq_empty H hDo h0
      (Set.not_nonempty_iff_eq_empty.mp (hfr 0 le_rfl))
  | succ m ih =>
    intro hfr k hk
    have hprev := ih (fun k hk => hfr k (by omega))
    rcases Nat.lt_or_ge k (m + 1) with hlt | hge
    · exact hprev k (by omega)
    · have hk' : k = m + 1 := by omega
      subst hk'
      obtain ⟨c, hc1, hc2⟩ := t15c_inter_nonempty_of_stepOK H (hX m)
      exact GMS3.cell_subset_of_inter_frontier_eq_empty H hDo ⟨c, hc2, hprev m le_rfl hc1⟩
        (Set.not_nonempty_iff_eq_empty.mp (hfr (m + 1) le_rfl))

/-- **Chain step, exit form.** Let `D` be open. Along a vertex path `X` with admissible steps whose first cell meets
`D`, if the cell at time `m` is not contained in `D`, some cell at a time `≤ m` meets `∂D`. -/
theorem t15c_exists_frontier_of_not_subset (H : CellularEmbedding G o) {D : Set ℂ} (hDo : IsOpen D)
    {X : ℕ → V} (hX : ∀ n, StepOK G (X n) (X (n + 1))) (h0 : (H.cell (X 0) ∩ D).Nonempty) {m : ℕ}
    (hm : ¬ H.cell (X m) ⊆ D) : ∃ k ≤ m, (H.cell (X k) ∩ frontier D).Nonempty := by
  by_contra hcon
  push Not at hcon
  exact hm (t15c_cell_subset_of_forall_not_meet_frontier H hDo hX h0 m
    (fun k hk => Set.not_nonempty_iff_eq_empty.mpr (hcon k hk)) m le_rfl)

/-- A preconnected set meeting `B_b(z)` and avoiding `∂B_b(z)` lies in `B_b(z)`. -/
theorem t15c_subset_ball_of_isPreconnected {S : Set ℂ} (hS : IsPreconnected S) {z : ℂ} {b : ℝ}
    (hmeet : (S ∩ ball z b).Nonempty) (hav : ¬ (S ∩ sphere z b).Nonempty) : S ⊆ ball z b := by
  have hcover : S ⊆ ball z b ∪ (closedBall z b)ᶜ := by
    intro q hq
    by_cases hqb : q ∈ ball z b
    · exact Or.inl hqb
    · refine Or.inr fun hqc => hav ⟨q, hq, ?_⟩
      rw [mem_sphere]
      rw [mem_ball, not_lt] at hqb
      exact le_antisymm (mem_closedBall.mp hqc) hqb
  rcases hS.subset_or_subset isOpen_ball isClosed_closedBall.isOpen_compl
    (Disjoint.mono_left ball_subset_closedBall disjoint_compl_right) hcover with h | h
  · exact h
  · obtain ⟨q, hq, hqb⟩ := hmeet
    exact absurd (ball_subset_closedBall hqb) (h hq)

/-- **Confinement.** Along a vertex path `X` with admissible steps whose first cell contains `z`, with `b > 0`: if no
cell up to time `m` meets `∂B_b(z)`, then every cell up to time `m` lies in `B_b(z)`. -/
theorem t15c_cell_subset_ball_of_forall_not_meet (H : CellularEmbedding G o) {X : ℕ → V}
    (hX : ∀ n, StepOK G (X n) (X (n + 1))) {z : ℂ} (hz : z ∈ H.cell (X 0)) {b : ℝ} (hb : 0 < b) :
    ∀ m, (∀ k ≤ m, ¬ (H.cell (X k) ∩ sphere z b).Nonempty) → ∀ k ≤ m, H.cell (X k) ⊆ ball z b := by
  intro m
  induction m with
  | zero =>
    intro hav k hk
    rw [Nat.le_zero.mp hk]
    exact t15c_subset_ball_of_isPreconnected (H.isConnected_cell _).isPreconnected
      ⟨z, hz, mem_ball_self hb⟩ (hav 0 le_rfl)
  | succ m ih =>
    intro hav k hk
    have hprev := ih (fun k hk => hav k (by omega))
    rcases Nat.lt_or_ge k (m + 1) with hlt | hge
    · exact hprev k (by omega)
    · have hk' : k = m + 1 := by omega
      subst hk'
      obtain ⟨c, hc1, hc2⟩ := t15c_inter_nonempty_of_stepOK H (hX m)
      exact t15c_subset_ball_of_isPreconnected (H.isConnected_cell _).isPreconnected
        ⟨c, hc2, hprev m le_rfl hc1⟩ (hav (m + 1) le_rfl)

/-- **Crossing.** Along a vertex path `X` with admissible steps whose first cell contains `z`, with `0 < b ≤ b'`: if
the cell at time `m` meets `∂B_{b'}(z)`, some cell at a time `≤ m` meets `∂B_b(z)`. -/
theorem t15c_exists_sphere_of_meet (H : CellularEmbedding G o) {X : ℕ → V}
    (hX : ∀ n, StepOK G (X n) (X (n + 1))) {z : ℂ} (hz : z ∈ H.cell (X 0)) {b b' : ℝ} (hb : 0 < b)
    (hbb' : b ≤ b') {m : ℕ} (hm : (H.cell (X m) ∩ sphere z b').Nonempty) :
    ∃ k ≤ m, (H.cell (X k) ∩ sphere z b).Nonempty := by
  by_contra hcon
  push Not at hcon
  have hsub := t15c_cell_subset_ball_of_forall_not_meet H hX hz hb m
    (fun k hk => Set.not_nonempty_iff_eq_empty.mpr (hcon k hk)) m le_rfl
  obtain ⟨q, hq, hq'⟩ := hm
  have h1 := mem_ball.mp (hsub hq)
  rw [mem_sphere] at hq'
  linarith

end MatedCRTHarmonic.GMSMain
