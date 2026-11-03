/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS3.Energy at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.Harmonic.Graph
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Deg

/-!
# Dirichlet energy on finite sub-graphs and the Dirichlet principle

Source: Gwynne–Miller–Sheffield, *Harmonic functions on mated-CRT maps* [18]: Definition 1.1 of [18] (`Energy(g; G) = ∑_{{x,y} ∈ E(G)} (g(x) − g(y))²`, n-tuple edges counted n times), the sub-graph `G(D)` of
(1.5) (vertex set `V(D)`, every edge of `G` joining two of its vertices) and the Dirichlet
principle used in the proofs of Theorem 3.2 and Lemma 3.4.

For a locally finite multigraph `G` and a finite vertex set `S`:

* `edgesIn G S`: the edges with both ends in `S` (the edge set of `G(S)`; loops are included and never
  contribute);
* `energy G S f`: Definition 1.1 on `G(S)`; `tv G S f`: the total variation `∑ |f(x) − f(y)|` over the
  same edges;
* `lap G f x = ∑_{d leaves x} (f x − f (dtgt d))`: `f` is discrete harmonic at `x` iff `lap G f x = 0`;
* `sum_edgesIn_darts` (the darts of `G(S)`, grouped by their source), `sum_edgesIn_mul_sub` (summation
  by parts) and `energy_eq_sum_mul_lap` (energy of a function vanishing off `U` when `S` contains every
  neighbour of `U`);
* `energy_eq_add_of_harmonic`, `energy_le_of_harmonic` (**the Dirichlet principle**): a function which
  is discrete harmonic at every vertex of `S \ B` all of whose neighbours lie in `S` minimizes
  `energy G S` among the functions with the same values on `S ∩ B`;
* elementary bounds: `energy_nonneg`, `energy_mono`, `sq_sub_le_energy`, `energy_comp_le`
  (post-composition with a 1-Lipschitz map), `energy_const_mul`, `sum_edgesIn_add_le` (each edge charged
  to both of its ends), and `abs_sub_le_tv_of_reachable` (the total variation along a connected induced
  sub-graph bounds every oscillation).
-/

set_option autoImplicit false

noncomputable section

open Finset
open scoped Classical

namespace MatedCRTHarmonic.GMS3

open LFMultigraph Harmonic

variable {V E : Type*} (G : LFMultigraph V E)

/-- The edges of `G` with both ends in `S`: the edge set of the sub-graph `G(S)` of [18] (1.5). -/
def edgesIn (S : Finset V) : Finset E :=
  (S.biUnion fun x => (G.finite_inc x).toFinset).filter fun e => G.src e ∈ S ∧ G.tgt e ∈ S

theorem mem_edgesIn {S : Finset V} {e : E} : e ∈ edgesIn G S ↔ G.src e ∈ S ∧ G.tgt e ∈ S := by
  unfold edgesIn
  simp only [Finset.mem_filter, Finset.mem_biUnion, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  exact ⟨fun h => h.2, fun h => ⟨⟨G.src e, h.1, Or.inl rfl⟩, h⟩⟩

theorem edgesIn_mono {S T : Finset V} (h : S ⊆ T) : edgesIn G S ⊆ edgesIn G T := fun e he => by
  rw [mem_edgesIn] at he ⊢
  exact ⟨h he.1, h he.2⟩

/-- **Definition 1.1 of [18]** on the sub-graph `G(S)`: `∑_{e ∈ E(G(S))} (f(src e) − f(tgt e))²`. -/
def energy (S : Finset V) (f : V → ℝ) : ℝ :=
  ∑ e ∈ edgesIn G S, (f (G.src e) - f (G.tgt e)) ^ 2

/-- The total variation of `f` over the edges of `G(S)`. -/
def tv (S : Finset V) (f : V → ℝ) : ℝ :=
  ∑ e ∈ edgesIn G S, |f (G.src e) - f (G.tgt e)|

/-- The (unnormalized) graph Laplacian `∑_{d leaves x} (f x − f (dtgt d))`; `f` is discrete harmonic at
`x` iff it vanishes. -/
def lap (f : V → ℝ) (x : V) : ℝ :=
  ∑ d ∈ G.outDarts x, (f x - f (G.dtgt d))

theorem lap_eq (f : V → ℝ) (x : V) :
    lap G f x = G.deg x * f x - ∑ d ∈ G.outDarts x, f (G.dtgt d) := by
  unfold lap LFMultigraph.deg
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]

/-! ### Darts of `G(S)` and summation by parts -/

/-- The darts of `G(S)`, grouped by edge and by source vertex. -/
theorem sum_edgesIn_darts (S : Finset V) (F : G.Dart → ℝ) :
    ∑ e ∈ edgesIn G S, (F (e, false) + F (e, true)) =
      ∑ x ∈ S, ∑ d ∈ (G.outDarts x).filter (fun d => G.dtgt d ∈ S), F d := by
  rw [← Finset.sum_biUnion]
  · have hset : S.biUnion (fun x => (G.outDarts x).filter fun d => G.dtgt d ∈ S) =
        edgesIn G S ×ˢ (Finset.univ : Finset Bool) := by
      ext ⟨e, b⟩
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
        and_true, mem_edgesIn, mem_outDarts]
      cases b
      · simp only [dsrc_false, dtgt_false]
        exact ⟨fun ⟨x, hx, hs, ht⟩ => ⟨hs ▸ hx, ht⟩, fun h => ⟨G.src e, h.1, rfl, h.2⟩⟩
      · simp only [dsrc_true, dtgt_true]
        exact ⟨fun ⟨x, hx, hs, ht⟩ => ⟨ht, hs ▸ hx⟩, fun h => ⟨G.tgt e, h.2, rfl, h.1⟩⟩
    rw [hset, Finset.sum_product]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Fintype.sum_bool, add_comm]
  · intro x _ y _ hxy
    rw [Function.onFun, Finset.disjoint_left]
    intro d hd hd'
    exact hxy (((mem_outDarts G).mp (Finset.mem_filter.mp hd).1).symm.trans
      ((mem_outDarts G).mp (Finset.mem_filter.mp hd').1))

/-- **Summation by parts** on `G(S)`. -/
theorem sum_edgesIn_mul_sub (S : Finset V) (f h : V → ℝ) :
    ∑ e ∈ edgesIn G S, (h (G.src e) - h (G.tgt e)) * (f (G.src e) - f (G.tgt e)) =
      ∑ x ∈ S, h x * ∑ d ∈ (G.outDarts x).filter (fun d => G.dtgt d ∈ S), (f x - f (G.dtgt d)) := by
  have key := sum_edgesIn_darts G S (fun d => h (G.dsrc d) * (f (G.dsrc d) - f (G.dtgt d)))
  simp only [dsrc_false, dsrc_true, dtgt_false, dtgt_true] at key
  rw [show ∑ e ∈ edgesIn G S, (h (G.src e) - h (G.tgt e)) * (f (G.src e) - f (G.tgt e)) =
      ∑ e ∈ edgesIn G S, (h (G.src e) * (f (G.src e) - f (G.tgt e)) +
        h (G.tgt e) * (f (G.tgt e) - f (G.src e))) from
      Finset.sum_congr rfl fun e _ => by ring, key]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [(mem_outDarts G).mp (Finset.mem_filter.mp hd).1]

/-- If every neighbour of `x` lies in `S`, the filtered inner sum is the Laplacian. -/
theorem sum_filter_eq_lap {S : Finset V} {x : V} (hnb : ∀ d ∈ G.outDarts x, G.dtgt d ∈ S)
    (f : V → ℝ) :
    ∑ d ∈ (G.outDarts x).filter (fun d => G.dtgt d ∈ S), (f x - f (G.dtgt d)) = lap G f x := by
  unfold lap
  rw [Finset.filter_true_of_mem hnb]

/-- The energy of a function vanishing off `U`, when `S` contains `U` and all neighbours of `U`:
`energy S f = ∑_{x ∈ U} f(x) · lap f (x)`. -/
theorem energy_eq_sum_mul_lap {S U : Finset V} (f : V → ℝ) (hU : ∀ x ∉ U, f x = 0) (hUS : U ⊆ S)
    (hnb : ∀ x ∈ U, ∀ d ∈ G.outDarts x, G.dtgt d ∈ S) :
    energy G S f = ∑ x ∈ U, f x * lap G f x := by
  unfold energy
  rw [show ∑ e ∈ edgesIn G S, (f (G.src e) - f (G.tgt e)) ^ 2 =
      ∑ e ∈ edgesIn G S, (f (G.src e) - f (G.tgt e)) * (f (G.src e) - f (G.tgt e)) from
      Finset.sum_congr rfl fun e _ => sq _, sum_edgesIn_mul_sub]
  calc ∑ x ∈ S, f x * ∑ d ∈ (G.outDarts x).filter (fun d => G.dtgt d ∈ S), (f x - f (G.dtgt d))
      = ∑ x ∈ U, f x * ∑ d ∈ (G.outDarts x).filter (fun d => G.dtgt d ∈ S), (f x - f (G.dtgt d)) :=
        (Finset.sum_subset hUS fun x _ hx => by rw [hU x hx, zero_mul]).symm
    _ = ∑ x ∈ U, f x * lap G f x :=
        Finset.sum_congr rfl fun x hx => by rw [sum_filter_eq_lap G (hnb x hx)]

/-! ### The Dirichlet principle -/

/-- **Dirichlet principle, Pythagorean form.** If every vertex of `S` outside `B` has all of its
neighbours in `S`, `f` is discrete harmonic at those vertices, and `g = f` on `S ∩ B`, then
`energy S g = energy S f + energy S (g − f)`. -/
theorem energy_eq_add_of_harmonic {S : Finset V} {B : Set V} {f g : V → ℝ}
    (hnb : ∀ x ∈ S, x ∉ B → ∀ d ∈ G.outDarts x, G.dtgt d ∈ S)
    (hharm : ∀ x ∈ S, x ∉ B → lap G f x = 0) (hbd : ∀ x ∈ S, x ∈ B → g x = f x) :
    energy G S g = energy G S f + energy G S (g - f) := by
  have hcross : ∑ e ∈ edgesIn G S, ((g - f) (G.src e) - (g - f) (G.tgt e)) *
      (f (G.src e) - f (G.tgt e)) = 0 := by
    rw [sum_edgesIn_mul_sub]
    refine Finset.sum_eq_zero fun x hx => ?_
    by_cases hxB : x ∈ B
    · rw [Pi.sub_apply, hbd x hx hxB, sub_self, zero_mul]
    · rw [sum_filter_eq_lap G (hnb x hx hxB), hharm x hx hxB, mul_zero]
  unfold energy
  rw [← Finset.sum_add_distrib]
  have h2 : ∑ e ∈ edgesIn G S, ((g - f) (G.src e) - (g - f) (G.tgt e)) *
      (f (G.src e) - f (G.tgt e)) * 2 = 0 := by
    rw [← Finset.sum_mul, hcross, zero_mul]
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib, ← h2]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [Pi.sub_apply]
  ring

theorem energy_nonneg (S : Finset V) (f : V → ℝ) : 0 ≤ energy G S f :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **Dirichlet principle** ([18], [LP16, Exercise 2.13]): among functions with prescribed
values on `S ∩ B`, a function discrete harmonic at every vertex of `S \ B` (all of whose neighbours lie in
`S`) has the least energy on `G(S)`. -/
theorem energy_le_of_harmonic {S : Finset V} {B : Set V} {f g : V → ℝ}
    (hnb : ∀ x ∈ S, x ∉ B → ∀ d ∈ G.outDarts x, G.dtgt d ∈ S)
    (hharm : ∀ x ∈ S, x ∉ B → lap G f x = 0) (hbd : ∀ x ∈ S, x ∈ B → g x = f x) :
    energy G S f ≤ energy G S g := by
  rw [energy_eq_add_of_harmonic G hnb hharm hbd]
  exact le_add_of_nonneg_right (energy_nonneg G S _)

/-! ### Elementary bounds -/

theorem energy_mono {S T : Finset V} (h : S ⊆ T) (f : V → ℝ) : energy G S f ≤ energy G T f :=
  Finset.sum_le_sum_of_subset_of_nonneg (edgesIn_mono G h) fun _ _ _ => sq_nonneg _

theorem sq_sub_le_energy {S : Finset V} {e : E} (he : e ∈ edgesIn G S) (f : V → ℝ) :
    (f (G.src e) - f (G.tgt e)) ^ 2 ≤ energy G S f :=
  Finset.single_le_sum (f := fun e => (f (G.src e) - f (G.tgt e)) ^ 2)
    (fun _ _ => sq_nonneg _) he

theorem energy_congr {S : Finset V} {f g : V → ℝ} (h : ∀ x ∈ S, f x = g x) :
    energy G S f = energy G S g := by
  unfold energy
  refine Finset.sum_congr rfl fun e he => ?_
  rw [mem_edgesIn] at he
  rw [h _ he.1, h _ he.2]

/-- Post-composition with a 1-Lipschitz map does not increase the energy. -/
theorem energy_comp_le (S : Finset V) (f : V → ℝ) {φ : ℝ → ℝ}
    (hφ : ∀ a b, |φ a - φ b| ≤ |a - b|) : energy G S (φ ∘ f) ≤ energy G S f := by
  unfold energy
  refine Finset.sum_le_sum fun e _ => ?_
  simp only [Function.comp]
  rw [← sq_abs, ← sq_abs (f (G.src e) - f (G.tgt e))]
  exact pow_le_pow_left₀ (abs_nonneg _) (hφ _ _) 2

theorem energy_const_mul (S : Finset V) (c : ℝ) (f : V → ℝ) :
    energy G S (fun x => c * f x) = c ^ 2 * energy G S f := by
  unfold energy
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  ring

/-- Each edge of `G(S)` charged to both of its ends: for `φ ≥ 0` on `S`,
`∑_{e ∈ E(G(S))} (φ(src e) + φ(tgt e)) ≤ ∑_{x ∈ S} deg(x) φ(x)`. -/
theorem sum_edgesIn_add_le (S : Finset V) {φ : V → ℝ} (hφ : ∀ x ∈ S, 0 ≤ φ x) :
    ∑ e ∈ edgesIn G S, (φ (G.src e) + φ (G.tgt e)) ≤ ∑ x ∈ S, (G.deg x : ℝ) * φ x := by
  have key := sum_edgesIn_darts G S (fun d => φ (G.dsrc d))
  simp only [dsrc_false, dsrc_true] at key
  rw [key]
  refine Finset.sum_le_sum fun x hx => ?_
  have hsum : ∑ d ∈ (G.outDarts x).filter (fun d => G.dtgt d ∈ S), φ (G.dsrc d) =
      ((G.outDarts x).filter (fun d => G.dtgt d ∈ S)).card * φ x := by
    rw [Finset.sum_congr rfl fun d hd => by rw [(mem_outDarts G).mp (Finset.mem_filter.mp hd).1],
      Finset.sum_const, nsmul_eq_mul]
  rw [hsum]
  refine mul_le_mul_of_nonneg_right ?_ (hφ x hx)
  exact_mod_cast Finset.card_filter_le _ _

/-! ### Total variation along connected sub-graphs -/

/-- Along a trail of `G.adj` with support in `S`, the oscillation of `f` between the ends is at most
The total variation of `f` over those edges of `G(S)` whose ends are consecutive on the trail. -/
theorem abs_sub_le_sum_of_isTrail {S : Finset V} (f : V → ℝ) :
    ∀ {u v : V} (p : G.adj.Walk u v), p.IsTrail → (∀ y ∈ p.support, y ∈ S) →
      |f u - f v| ≤ ∑ e ∈ (edgesIn G S).filter (fun e => s(G.src e, G.tgt e) ∈ p.edges),
        |f (G.src e) - f (G.tgt e)| := by
  intro u v p
  induction p with
  | nil =>
    intro _ _
    rw [sub_self, abs_zero]
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  | @cons u w v hadj q ih =>
    intro htr hsupp
    rw [SimpleGraph.Walk.isTrail_cons] at htr
    have hu : u ∈ S := hsupp u (SimpleGraph.Walk.start_mem_support _)
    have hw : w ∈ S := hsupp w (by simp)
    have hq := ih htr.1 fun y hy => hsupp y (by simp [hy])
    obtain ⟨e, he, hsym, habs⟩ : ∃ e ∈ edgesIn G S, s(G.src e, G.tgt e) = s(u, w) ∧
        |f (G.src e) - f (G.tgt e)| = |f u - f w| := by
      obtain ⟨-, ⟨e, he1, he2⟩ | ⟨e, he1, he2⟩⟩ := (adj_iff G).mp hadj
      · refine ⟨e, (mem_edgesIn G).mpr ⟨he1 ▸ hu, he2 ▸ hw⟩, by rw [he1, he2], by rw [he1, he2]⟩
      · refine ⟨e, (mem_edgesIn G).mpr ⟨he1 ▸ hw, he2 ▸ hu⟩, by rw [he1, he2, Sym2.eq_swap],
          by rw [he1, he2, abs_sub_comm]⟩
    have hsplit : (edgesIn G S).filter (fun e => s(G.src e, G.tgt e) ∈ (SimpleGraph.Walk.cons
        hadj q).edges) = (edgesIn G S).filter (fun e => s(G.src e, G.tgt e) = s(u, w)) ∪
        (edgesIn G S).filter (fun e => s(G.src e, G.tgt e) ∈ q.edges) := by
      rw [← Finset.filter_or]
      refine Finset.filter_congr fun e _ => ?_
      rw [SimpleGraph.Walk.edges_cons, List.mem_cons]
    have hdisj : Disjoint ((edgesIn G S).filter (fun e => s(G.src e, G.tgt e) = s(u, w)))
        ((edgesIn G S).filter (fun e => s(G.src e, G.tgt e) ∈ q.edges)) := by
      rw [Finset.disjoint_filter]
      intro e _ h1 h2
      exact htr.2 (h1 ▸ h2)
    rw [hsplit, Finset.sum_union hdisj]
    have hone : |f u - f w| ≤ ∑ e ∈ (edgesIn G S).filter
        (fun e => s(G.src e, G.tgt e) = s(u, w)), |f (G.src e) - f (G.tgt e)| := by
      have hmem : e ∈ (edgesIn G S).filter (fun e => s(G.src e, G.tgt e) = s(u, w)) :=
        Finset.mem_filter.mpr ⟨he, hsym⟩
      rw [← habs]
      exact Finset.single_le_sum (f := fun e => |f (G.src e) - f (G.tgt e)|)
        (fun _ _ => abs_nonneg _) hmem
    calc |f u - f v| ≤ |f u - f w| + |f w - f v| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add hone hq

/-- **Total variation bound.** If `u, v ∈ S` are connected in the sub-graph of `G.adj` induced by `S`,
then `|f u − f v| ≤ tv G S f`. -/
theorem abs_sub_le_tv_of_reachable {S : Finset V} (f : V → ℝ) {u v : V} (hu : u ∈ S) (hv : v ∈ S)
    (h : (G.adj.induce (S : Set V)).Reachable ⟨u, hu⟩ ⟨v, hv⟩) : |f u - f v| ≤ tv G S f := by
  obtain ⟨w⟩ := h
  let w' : G.adj.Walk u v := w.map (SimpleGraph.Embedding.induce (S : Set V)).toHom
  have hsupp : ∀ y ∈ w'.support, y ∈ S := by
    intro y hy
    have hy' : y ∈ w.support.map (SimpleGraph.Embedding.induce (G := G.adj) (S : Set V)).toHom := by
      rwa [← SimpleGraph.Walk.support_map]
    obtain ⟨z, -, rfl⟩ := List.mem_map.mp hy'
    exact z.2
  let p := w'.toPath
  have hp : ∀ y ∈ (p : G.adj.Walk u v).support, y ∈ S := fun y hy =>
    hsupp y (SimpleGraph.Walk.support_toPath_subset_support w' hy)
  refine (abs_sub_le_sum_of_isTrail G f (p : G.adj.Walk u v) p.2.isTrail hp).trans ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    fun _ _ _ => abs_nonneg _

end MatedCRTHarmonic.GMS3
