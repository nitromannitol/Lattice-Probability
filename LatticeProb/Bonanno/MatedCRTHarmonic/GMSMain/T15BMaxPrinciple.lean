/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSMain.T15BMaxPrinciple at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS3.Cells
import LatticeProb.Bonanno.MatedCRTHarmonic.GoodScales.Geometry

/-!
# [18] Theorem 3.9: maximum principle and cell chains

Source: Gwynne–Miller–Sheffield, *Harmonic functions on mated-CRT maps* [18], §3.5, proof of Theorem 3.9. The deterministic graph facts
behind the oscillation-decay proof of the interior estimate (3.30). Discrete harmonicity is the
formalized `GMS3.lap G u v = 0` (simple random walk over edge ends, multiplicities counted).

* `mem_of_walk`: membership in an adjacency-closed set propagates along walks.
* `eq_of_lap_eq_zero_of_le`, `eq_of_lap_eq_zero_of_ge`: at a harmonic vertex, a one-sided bound at all dart heads
  forces equality.
* `nonneg_of_lap_eq_zero` (**minimum principle**): on a finite set `K` each of whose vertices is connected to the
  outside, a harmonic function nonnegative at the outer neighbours of `K` is nonnegative on `K`.
* `exists_walk_le_of_lap_eq_zero` (**maximum-principle path**): from every vertex `v₀` there is a walk leaving `K`
  along which `u ≥ u(v₀)`.
* `exists_mem_support_sphere` (crossing lemma for graph walks): if the cell of the start of a walk comes within `ρ`
  of `z` and the cell of its end reaches distance `ρ`, some cell of the walk meets `∂B_ρ(z)`.
* `cell_subset_ball_of_not_meet`: a cell meeting `B_r(z)` but not `∂B_r(z)` lies in `B_r(z)`.
* `infinite_vertex`, `exists_reachable_notMem`: a cellular embedding has infinitely many vertices, so in a
  connected graph every vertex of a finite set is connected to a vertex outside it.
-/

set_option autoImplicit false

noncomputable section

open Set Metric

namespace MatedCRTHarmonic.GMSMain.T15B

open LFMultigraph Harmonic

variable {V E : Type*} (G : LFMultigraph V E)

/-! ### Walks and adjacency-closed sets -/

/-- Membership in a set closed under adjacency propagates along walks. -/
theorem mem_of_walk {S : Set V} (hS : ∀ v w, G.adj.Adj v w → v ∈ S → w ∈ S) :
    ∀ {a b : V} (_p : G.adj.Walk a b), a ∈ S → b ∈ S := by
  intro a b p
  induction p with
  | nil => exact id
  | cons hadj _ ih => exact fun h => ih (hS _ _ hadj h)

/-- The head of a dart at `v` is `v` itself (a loop) or a neighbour of `v`. -/
theorem dtgt_eq_or_adj {v : V} {d : G.Dart} (hd : d ∈ G.outDarts v) :
    G.dtgt d = v ∨ G.adj.Adj v (G.dtgt d) := by
  have h := GoodScales.stepOK_dsrc_dtgt G d
  rw [(Harmonic.mem_outDarts G).mp hd] at h
  exact h

/-- At a harmonic vertex where `u ≤ u v` at every dart head, `u = u v` at every dart head. -/
theorem eq_of_lap_eq_zero_of_le {u : V → ℝ} {v : V} (hlap : GMS3.lap G u v = 0)
    (hle : ∀ d ∈ G.outDarts v, u (G.dtgt d) ≤ u v) : ∀ d ∈ G.outDarts v, u (G.dtgt d) = u v := by
  unfold GMS3.lap at hlap
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun d hd => sub_nonneg.mpr (hle d hd))).mp hlap
  intro d hd
  linarith [h0 d hd]

/-- At a harmonic vertex where `u v ≤ u` at every dart head, `u = u v` at every dart head. -/
theorem eq_of_lap_eq_zero_of_ge {u : V → ℝ} {v : V} (hlap : GMS3.lap G u v = 0)
    (hge : ∀ d ∈ G.outDarts v, u v ≤ u (G.dtgt d)) : ∀ d ∈ G.outDarts v, u (G.dtgt d) = u v := by
  unfold GMS3.lap at hlap
  have h0 := (Finset.sum_eq_zero_iff_of_nonpos (fun d hd => sub_nonpos.mpr (hge d hd))).mp hlap
  intro d hd
  linarith [h0 d hd]

/-- The Laplacian of `-u`. -/
theorem lap_neg (u : V → ℝ) (v : V) : GMS3.lap G (fun w => -u w) v = -GMS3.lap G u v := by
  unfold GMS3.lap
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  ring

/-- The Laplacian of `u - m - c·h` (constants are harmonic, the Laplacian is linear). -/
theorem lap_sub_const_sub_mul (u h : V → ℝ) (m c : ℝ) (v : V) :
    GMS3.lap G (fun w => u w - m - c * h w) v = GMS3.lap G u v - c * GMS3.lap G h v := by
  unfold GMS3.lap
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  ring

/-! ### The minimum principle and the maximum-principle path -/

/-- **Minimum principle.** Let `K` be finite, let `g` be discrete harmonic at every vertex of `K` and nonnegative
at every neighbour of `K` outside `K`, and let every vertex of `K` be connected to a vertex outside `K`. Then
`g ≥ 0` on `K`. -/
theorem nonneg_of_lap_eq_zero {K : Set V} (hK : K.Finite) {g : V → ℝ}
    (hharm : ∀ v ∈ K, GMS3.lap G g v = 0)
    (hbd : ∀ v ∈ K, ∀ w, G.adj.Adj v w → w ∉ K → 0 ≤ g w)
    (hesc : ∀ v ∈ K, ∃ w, w ∉ K ∧ G.adj.Reachable v w) : ∀ v ∈ K, 0 ≤ g v := by
  by_contra hcon
  push Not at hcon
  obtain ⟨v₁, hv₁K, hv₁⟩ := hcon
  obtain ⟨v₀, hv₀K, hmin⟩ := Set.exists_min_image K g hK ⟨v₁, hv₁K⟩
  have hneg : g v₀ < 0 := lt_of_le_of_lt (hmin v₁ hv₁K) hv₁
  -- the minimizers of `g` in `K` form an adjacency-closed set
  have hclosed : ∀ v w, G.adj.Adj v w → v ∈ {v | v ∈ K ∧ g v = g v₀} →
      w ∈ {v | v ∈ K ∧ g v = g v₀} := by
    rintro v w hvw ⟨hvK, hveq⟩
    have hge : ∀ d ∈ G.outDarts v, g v ≤ g (G.dtgt d) := by
      intro d hd
      rcases dtgt_eq_or_adj G hd with h | h
      · rw [h]
      · by_cases hK' : G.dtgt d ∈ K
        · rw [hveq]
          exact hmin _ hK'
        · rw [hveq]
          exact hneg.le.trans (hbd v hvK _ h hK')
    have heq := eq_of_lap_eq_zero_of_ge G (hharm v hvK) hge
    obtain ⟨d, hd1, hd2⟩ := exists_dart_of_adj G hvw
    have hw : g w = g v₀ := by rw [← hd2, heq d ((Harmonic.mem_outDarts G).mpr hd1), hveq]
    refine ⟨?_, hw⟩
    by_contra hwK
    have h := hbd v hvK w hvw hwK
    rw [hw] at h
    linarith
  obtain ⟨w, hwK, ⟨p⟩⟩ := hesc v₀ hv₀K
  exact hwK (mem_of_walk G hclosed p ⟨hv₀K, rfl⟩).1

/-- **Maximum-principle path.** Let `K` be finite, let `u` be discrete harmonic at every vertex of `K`, and let
every vertex of `K` be connected to a vertex outside `K`. From every vertex `v₀` there is a walk to a vertex outside
`K` along which `u ≥ u(v₀)` (for `v₀ ∉ K` the trivial walk). -/
theorem exists_walk_le_of_lap_eq_zero {K : Set V} (hK : K.Finite) {u : V → ℝ}
    (hharm : ∀ v ∈ K, GMS3.lap G u v = 0)
    (hesc : ∀ v ∈ K, ∃ w, w ∉ K ∧ G.adj.Reachable v w) (v₀ : V) :
    ∃ w, w ∉ K ∧ ∃ p : G.adj.Walk v₀ w, ∀ v ∈ p.support, u v₀ ≤ u v := by
  by_contra hcon
  push Not at hcon
  -- the vertices reachable from `v₀` along walks on which `u ≥ u v₀`
  set S : Set V := {v | ∃ p : G.adj.Walk v₀ v, ∀ y ∈ p.support, u v₀ ≤ u y} with hSdef
  have hSK : S ⊆ K := by
    rintro v ⟨p, hp⟩
    by_contra hvK
    obtain ⟨y, hy, hlt⟩ := hcon v hvK p
    exact absurd (hp y hy) (not_le.mpr hlt)
  have hv₀S : v₀ ∈ S := ⟨SimpleGraph.Walk.nil, fun y hy => by
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hy
    rw [hy]⟩
  obtain ⟨v₁, hv₁S, hmax⟩ := Set.exists_max_image S u (hK.subset hSK) ⟨v₀, hv₀S⟩
  have hext : ∀ v w, v ∈ S → G.adj.Adj v w → u v₀ ≤ u w → w ∈ S := by
    rintro v w ⟨p, hp⟩ hvw huw
    refine ⟨p.concat hvw, fun y hy => ?_⟩
    rw [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at hy
    rcases hy with hy | rfl
    · exact hp y hy
    · exact huw
  have hle0 : ∀ v ∈ S, u v₀ ≤ u v := by
    rintro v ⟨p, hp⟩
    exact hp v p.end_mem_support
  -- the maximizers of `u` on `S` form an adjacency-closed set
  have hclosed : ∀ v w, G.adj.Adj v w → v ∈ {v | v ∈ S ∧ u v = u v₁} →
      w ∈ {v | v ∈ S ∧ u v = u v₁} := by
    rintro v w hvw ⟨hvS, hveq⟩
    have hle : ∀ d ∈ G.outDarts v, u (G.dtgt d) ≤ u v := by
      intro d hd
      rcases dtgt_eq_or_adj G hd with h | h
      · rw [h]
      · by_cases hu : u v₀ ≤ u (G.dtgt d)
        · rw [hveq]
          exact hmax _ (hext v _ hvS h hu)
        · exact (not_le.mp hu).le.trans (hle0 v hvS)
    have heq := eq_of_lap_eq_zero_of_le G (hharm v (hSK hvS)) hle
    obtain ⟨d, hd1, hd2⟩ := exists_dart_of_adj G hvw
    have hw : u w = u v := by rw [← hd2, heq d ((Harmonic.mem_outDarts G).mpr hd1)]
    exact ⟨hext v w hvS hvw (by rw [hw]; exact hle0 v hvS), hw.trans hveq⟩
  obtain ⟨w, hwK, ⟨p⟩⟩ := hesc v₁ (hSK hv₁S)
  exact hwK (hSK (mem_of_walk G hclosed p ⟨hv₁S, rfl⟩).1)

/-! ### Cells along walks -/

variable {G} {o : V}

/-- **Crossing lemma for graph walks.** If the cell of `a` has a point within distance `ρ` of `z` and the cell of
`b` a point at distance `≥ ρ` from `z`, then every walk from `a` to `b` has a vertex whose cell meets `∂B_ρ(z)`
(cells are connected and adjacent cells intersect). -/
theorem exists_mem_support_sphere (H : CellularEmbedding G o) {z : ℂ} {ρ : ℝ} :
    ∀ {a b : V} (p : G.adj.Walk a b), (∃ w ∈ H.cell a, dist w z ≤ ρ) →
      (∃ w ∈ H.cell b, ρ ≤ dist w z) → ∃ v ∈ p.support, (H.cell v ∩ sphere z ρ).Nonempty := by
  intro a b p
  induction p with
  | nil =>
    rintro ⟨w₁, hw₁, h₁⟩ ⟨w₂, hw₂, h₂⟩
    exact ⟨_, SimpleGraph.Walk.start_mem_support _,
      GoodScales.inter_sphere_nonempty_of_isPreconnected (H.isConnected_cell _).isPreconnected hw₂ hw₁
        h₂ h₁⟩
  | @cons a c b hac q ih =>
    rintro ⟨w₁, hw₁, h₁⟩ hb
    by_cases hfar : ∃ w ∈ H.cell a, ρ ≤ dist w z
    · obtain ⟨w₂, hw₂, h₂⟩ := hfar
      exact ⟨a, SimpleGraph.Walk.start_mem_support _,
        GoodScales.inter_sphere_nonempty_of_isPreconnected (H.isConnected_cell _).isPreconnected hw₂
          hw₁ h₂ h₁⟩
    · push Not at hfar
      obtain ⟨c', hc'a, hc'c⟩ := H.inter_of_adj a c hac
      obtain ⟨v, hv, hvs⟩ := ih ⟨c', hc'c, (hfar c' hc'a).le⟩ hb
      exact ⟨v, by rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ hv, hvs⟩

/-- A cell meeting `B_r(z)` but not `∂B_r(z)` lies in `B_r(z)`. -/
theorem cell_subset_ball_of_not_meet (H : CellularEmbedding G o) {v : V} {z : ℂ} {r : ℝ}
    (hmeet : (H.cell v ∩ ball z r).Nonempty) (hsph : ¬ (H.cell v ∩ sphere z r).Nonempty) :
    H.cell v ⊆ ball z r := by
  intro w hw
  by_contra hwb
  obtain ⟨w', hw', hw'b⟩ := hmeet
  rw [mem_ball] at hwb hw'b
  exact hsph (GoodScales.inter_sphere_nonempty_of_isPreconnected (H.isConnected_cell v).isPreconnected
    hw hw' (not_lt.mp hwb) hw'b.le)

/-- A cellular embedding has infinitely many vertices (finitely many compact cells do not cover `ℂ`). -/
theorem infinite_vertex (H : CellularEmbedding G o) : Infinite V := by
  by_contra hfin
  rw [not_infinite_iff_finite] at hfin
  have hcpt : IsCompact (⋃ x, H.cell x) := isCompact_iUnion fun x => H.isCompact_cell x
  rw [H.iUnion_cell] at hcpt
  exact noncompact_univ ℂ hcpt

variable (G) in
/-- In a connected graph with infinitely many vertices, every vertex of a finite set is connected to a vertex
outside it. -/
theorem exists_reachable_notMem (hconn : G.adj.Connected) [Infinite V] {K : Set V} (hK : K.Finite) :
    ∀ v ∈ K, ∃ w, w ∉ K ∧ G.adj.Reachable v w := by
  intro v _
  obtain ⟨w, hw⟩ := hK.infinite_compl.nonempty
  exact ⟨w, hw, hconn.preconnected v w⟩

end MatedCRTHarmonic.GMSMain.T15B
