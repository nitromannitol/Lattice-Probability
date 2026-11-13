/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.RouteM.BPointConnected at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.Core.CellInterfaces
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTGraph
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.PsiBundle
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.RCorollaryB

/-!
# Route M, Theorem B: the mated-CRT cells through a point induce a connected subgraph

(the drawing construction, Theorem B, and Details (a)).

Let `ω` be a path of `(L, R)` and `η : ℝ → ℂ` a curve forming a `Peanosphere ω η` (the deterministic bundle of
`RouteM/PsiBundle.lean`, TF2 Details (a)). For a mesh `ε`, vertex `x : ℤ` of the ε-mated-CRT map `G^ε` (frozen
`MatedCRT.graph`, [18] (1.1)) has the time interval `I_x = [ε(x − 1), εx]` and the cell `H_x = η(I_x)`.

**Theorem B** (`pointConnected_of_peanosphere_holds`): if `H` is a cellular embedding of `G^ε` with
`H.cell x = η '' [ε(x − 1), εx]`, then `H.PointConnected` (the Core interface (LC)): for every `q ∈ ℂ` the vertices
whose cells contain `q` induce a connected subgraph of `G^ε.adj`.

Proof (TF2 §5). Take `q ∈ H_x ∩ H_{x'}` and times `u ∈ I_x`, `u' ∈ I_{x'}` with `η u = η u' = q`. The field
`onlyMerge` (DMS Lemma 8.14, P2) joins `u` to `u'` by a finite chain of direct L/R relations; the field `merge`
(DMS Lemma 8.8, P1) puts every time of the chain in `η⁻¹(q)`. A direct relation `a < b` with `a ∈ I_x`, `b ∈ I_y`
makes `x, y` equal or adjacent: `x ≤ y`; consecutive vertices are adjacent; and for `y ≥ x + 2` the interval
`[εx, ε(y − 1)]` lies inside `[a, b]`, where the coordinate stays `≥ X a`, so condition (1.1) (`MatedCRT.SideCond`)
holds (`thmB_sideCond_of_directRel`). A grid time lies in two consecutive intervals, which are adjacent. Every vertex
met along the chain has a cell containing `q`.

Only the fields `merge`, `onlyMerge` (and `surj`, for nonemptiness) of `Peanosphere` are used, together with the
continuity of `ω` and [18] (1.1). The positivity of `ε` is not a hypothesis: it follows from the nonempty
interior of the cell `H_0` (`thmB_pos_of_cellularEmbedding`).

Also: the hypothesis-free core `thmB_induce_connected` (no cellular embedding; `0 < ε`), Corollary B′ for these cells
(`connected_verticesMeeting_of_peanosphere_holds`, via TFR's `connected_induce_verticesMeeting`), and the unit-mesh
forms (`…_unitMesh_holds`) matching the frozen cell coupling (`cell ω x = η([x − 1, x])`).
-/

set_option autoImplicit false

noncomputable section

open Set

namespace MatedCRTHarmonic.RouteM

variable {ε : ℝ} {ω : MatedCRT.Path2} {η : ℝ → ℂ}

/-! ### Vertex time intervals -/

/-- Every time lies in the time interval `[ε(x − 1), εx]` of some vertex `x` (namely `x = ⌈t/ε⌉`). -/
theorem thmB_exists_mem_Icc (hε : 0 < ε) (t : ℝ) :
    ∃ x : ℤ, t ∈ Icc (ε * ((x : ℝ) - 1)) (ε * x) := by
  refine ⟨⌈t / ε⌉, ?_, ?_⟩
  · have h1 : ((⌈t / ε⌉ : ℤ) : ℝ) < t / ε + 1 := Int.ceil_lt_add_one _
    have h2 : (((⌈t / ε⌉ : ℤ) : ℝ) - 1) * ε < t := (lt_div_iff₀ hε).1 (by linarith)
    linarith [mul_comm ε (((⌈t / ε⌉ : ℤ) : ℝ) - 1)]
  · have h1 : t / ε ≤ ((⌈t / ε⌉ : ℤ) : ℝ) := Int.le_ceil _
    have h2 : t ≤ ((⌈t / ε⌉ : ℤ) : ℝ) * ε := (div_le_iff₀ hε).1 h1
    linarith [mul_comm ε ((⌈t / ε⌉ : ℤ) : ℝ)]

/-- Times in increasing order lie in the time intervals of vertices in weakly increasing order. -/
theorem thmB_le_of_lt (hε : 0 < ε) {a b : ℝ} {x y : ℤ}
    (ha : a ∈ Icc (ε * ((x : ℝ) - 1)) (ε * x)) (hb : b ∈ Icc (ε * ((y : ℝ) - 1)) (ε * y))
    (hab : a < b) : x ≤ y := by
  by_contra hxy
  have hyx : y + 1 ≤ x := by omega
  have hyx' : (y : ℝ) + 1 ≤ x := by exact_mod_cast hyx
  have hmul : ε * (y : ℝ) ≤ ε * ((x : ℝ) - 1) := mul_le_mul_of_nonneg_left (by linarith) hε.le
  linarith [ha.1, hb.2]

/-- Two vertices whose time intervals share a time `t` with `x < y` are consecutive. -/
theorem thmB_eq_succ_of_mem (hε : 0 < ε) {t : ℝ} {x y : ℤ}
    (hx : t ∈ Icc (ε * ((x : ℝ) - 1)) (ε * x)) (hy : t ∈ Icc (ε * ((y : ℝ) - 1)) (ε * y))
    (hxy : x < y) : y = x + 1 := by
  have h1 : ε * ((y : ℝ) - 1) ≤ ε * x := hy.1.trans hx.2
  have h2 : (y : ℝ) - 1 ≤ x := le_of_mul_le_mul_left h1 hε
  have h3 : (y : ℝ) ≤ ((x + 1 : ℤ) : ℝ) := by push_cast; linarith
  have h4 : y ≤ x + 1 := by exact_mod_cast h3
  omega

/-! ### Adjacency in the mated-CRT map -/

/-- Consecutive vertices of the ε-mated-CRT map are adjacent (the hard-wired edge `(x, x + 1, false)`). -/
theorem thmB_adj_succ {h : MatedCRT.IsLocallyFinite ε ω} (x : ℤ) :
    (MatedCRT.graph ε ω h).adj.Adj x (x + 1) := by
  rw [LFMultigraph.adj, SimpleGraph.fromRel_adj]
  exact ⟨by omega, Or.inl ⟨⟨(x, x + 1, false), lt_add_one x, Or.inl ⟨rfl, rfl⟩⟩, rfl, rfl⟩⟩

/-- A non-consecutive pair `x + 1 < y` satisfying condition (1.1) for the coordinate selected by `b` is adjacent
(the edge `(x, y, b)`). -/
theorem thmB_adj_of_sideCond {h : MatedCRT.IsLocallyFinite ε ω} (b : Bool) {x y : ℤ} (hxy : x + 1 < y)
    (hside : MatedCRT.SideCond ε (fun t => if b then (ω t).2 else (ω t).1) x y) :
    (MatedCRT.graph ε ω h).adj.Adj x y := by
  rw [LFMultigraph.adj, SimpleGraph.fromRel_adj]
  exact ⟨by omega, Or.inl ⟨⟨(x, y, b), show x < y by omega, Or.inr ⟨show y ≠ x + 1 by omega, hside⟩⟩,
    rfl, rfl⟩⟩

/-- **The key step of TF2's proof of Theorem B (§5, step 3).** A direct relation of a continuous coordinate `X`
between a time `a ∈ I_x` and a time `b ∈ I_y` with `y ≥ x + 2` gives condition (1.1) for `x, y`: the middle interval
`[εx, ε(y − 1)]` lies in `[a, b]`, where `X ≥ X a`, while both end infima are `≤ X a = X b`. -/
theorem thmB_sideCond_of_directRel (hε : 0 < ε) {X : ℝ → ℝ} (hX : Continuous X) {a b : ℝ} {x y : ℤ}
    (hrel : directRel X a b)
    (ha : a ∈ Icc (ε * ((x : ℝ) - 1)) (ε * x)) (hb : b ∈ Icc (ε * ((y : ℝ) - 1)) (ε * y))
    (hxy : x + 1 < y) : MatedCRT.SideCond ε X x y := by
  obtain ⟨_, heq, habove⟩ := hrel
  have hbdd : ∀ c d : ℝ, BddBelow (X '' Icc c d) := fun c d =>
    (isCompact_Icc.image hX).bddBelow
  have hxle : MatedCRT.intervalInf X (ε * ((x : ℝ) - 1)) (ε * x) ≤ X a :=
    csInf_le (hbdd _ _) (mem_image_of_mem X ha)
  have hyle : MatedCRT.intervalInf X (ε * ((y : ℝ) - 1)) (ε * y) ≤ X a :=
    (csInf_le (hbdd _ _) (mem_image_of_mem X hb)).trans_eq heq.symm
  have hxy' : (x : ℝ) + 2 ≤ y := by exact_mod_cast (show x + 2 ≤ y by omega)
  have hmid : (Icc (ε * (x : ℝ)) (ε * ((y : ℝ) - 1))).Nonempty :=
    nonempty_Icc.2 (mul_le_mul_of_nonneg_left (by linarith) hε.le)
  have hge : X a ≤ MatedCRT.intervalInf X (ε * x) (ε * ((y : ℝ) - 1)) := by
    apply le_csInf (hmid.image X)
    rintro _ ⟨u, hu, rfl⟩
    have hau : a ≤ u := ha.2.trans hu.1
    have hub : u ≤ b := hu.2.trans hb.1
    rcases hau.eq_or_lt with hau | hau
    · rw [hau]
    rcases hub.eq_or_lt with hub | hub
    · rw [hub]
      exact heq.le
    exact (habove u ⟨hau, hub⟩).le
  exact max_le (hxle.trans hge) (hyle.trans hge)

/-- A direct L- or R-relation between a time of `I_x` and a time of `I_y` makes `x` and `y` equal or adjacent in the
ε-mated-CRT map. -/
theorem thmB_eq_or_adj_of_directRel (hε : 0 < ε) {h : MatedCRT.IsLocallyFinite ε ω} {a b : ℝ} {x y : ℤ}
    (hrel : directRel (fun u => (ω u).1) a b ∨ directRel (fun u => (ω u).2) a b)
    (ha : a ∈ Icc (ε * ((x : ℝ) - 1)) (ε * x)) (hb : b ∈ Icc (ε * ((y : ℝ) - 1)) (ε * y)) :
    x = y ∨ (MatedCRT.graph ε ω h).adj.Adj x y := by
  have hlt : a < b := by
    rcases hrel with hrel | hrel
    · exact hrel.1
    · exact hrel.1
  rcases (thmB_le_of_lt hε ha hb hlt).eq_or_lt with hxy | hxy
  · exact Or.inl hxy
  right
  by_cases hsucc : y = x + 1
  · subst hsucc
    exact thmB_adj_succ x
  have hxy' : x + 1 < y := by omega
  rcases hrel with hrel | hrel
  · exact thmB_adj_of_sideCond false hxy'
      (thmB_sideCond_of_directRel (X := fun u => (ω u).1) hε (continuous_fst.comp ω.continuous)
        hrel ha hb hxy')
  · exact thmB_adj_of_sideCond true hxy'
      (thmB_sideCond_of_directRel (X := fun u => (ω u).2) hε (continuous_snd.comp ω.continuous)
        hrel ha hb hxy')

/-- Two vertices whose time intervals share a time are equal or adjacent (a grid time lies in two consecutive
intervals). -/
theorem thmB_eq_or_adj_of_mem (hε : 0 < ε) {h : MatedCRT.IsLocallyFinite ε ω} {t : ℝ} {x y : ℤ}
    (hx : t ∈ Icc (ε * ((x : ℝ) - 1)) (ε * x)) (hy : t ∈ Icc (ε * ((y : ℝ) - 1)) (ε * y)) :
    x = y ∨ (MatedCRT.graph ε ω h).adj.Adj x y := by
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · right
    rw [thmB_eq_succ_of_mem hε hx hy hxy]
    exact thmB_adj_succ x
  · exact Or.inl hxy
  · right
    rw [thmB_eq_succ_of_mem hε hy hx hxy]
    exact (thmB_adj_succ y).symm

/-- Equal or adjacent vertices of `S` are reachable from each other in the subgraph induced on `S`. -/
theorem thmB_reachable_induce_of_eq_or_adj {V : Type*} {G : SimpleGraph V} {S : Set V} {x y : V}
    {hx : x ∈ S} {hy : y ∈ S} (hxy : x = y ∨ G.Adj x y) :
    (G.induce S).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  rcases hxy with rfl | hadj
  · rfl
  · exact SimpleGraph.Adj.reachable (SimpleGraph.induce_adj.2 hadj)

/-! ### Theorem B -/

/-- Induction along the chain of direct relations given by `onlyMerge` (TF2 §5, steps 2–4): if `a` and `b` are joined
by the equivalence relation generated by the direct L/R relations and `η a = q`, then any vertex whose time interval
contains `a` is joined to any vertex whose time interval contains `b` inside the subgraph induced on the vertices whose
cells contain `q`. -/
theorem thmB_reachable_of_eqvGen (P : Peanosphere ω η) (hε : 0 < ε) (h : MatedCRT.IsLocallyFinite ε ω) (q : ℂ)
    {a b : ℝ}
    (hab : Relation.EqvGen
      (fun s t => directRel (fun u => (ω u).1) s t ∨ directRel (fun u => (ω u).2) s t) a b) :
    η a = q → ∀ (x y : ℤ) (hx : q ∈ η '' Icc (ε * ((x : ℝ) - 1)) (ε * x))
      (hy : q ∈ η '' Icc (ε * ((y : ℝ) - 1)) (ε * y)),
      a ∈ Icc (ε * ((x : ℝ) - 1)) (ε * x) → b ∈ Icc (ε * ((y : ℝ) - 1)) (ε * y) →
      ((MatedCRT.graph ε ω h).adj.induce {z : ℤ | q ∈ η '' Icc (ε * ((z : ℝ) - 1)) (ε * z)}).Reachable
        ⟨x, hx⟩ ⟨y, hy⟩ := by
  induction hab with
  | rel a b hab =>
    intro _ x y hx hy ha hb
    exact thmB_reachable_induce_of_eq_or_adj (thmB_eq_or_adj_of_directRel hε hab ha hb)
  | refl a =>
    intro _ x y hx hy ha hb
    exact thmB_reachable_induce_of_eq_or_adj (thmB_eq_or_adj_of_mem hε ha hb)
  | symm a b hab ih =>
    intro hqb x y hx hy hb ha
    have hqa : η a = q := (eta_eq_of_eqvGen P hab).trans hqb
    exact (ih hqa y x hy hx ha hb).symm
  | trans a b c hab _ ih₁ ih₂ =>
    intro hqa x y hx hy ha hc
    obtain ⟨z, hz⟩ := thmB_exists_mem_Icc hε b
    have hqb : η b = q := (eta_eq_of_eqvGen P hab).symm.trans hqa
    have hzq : q ∈ η '' Icc (ε * ((z : ℝ) - 1)) (ε * z) := ⟨b, hz, hqb⟩
    exact (ih₁ hqa x z hx hzq ha hz).trans (ih₂ hqb z y hzq hy hz hc)

/-- **Theorem B, core form** (TF2 §5; no cellular embedding needed): for `0 < ε` and every `q ∈ ℂ`, the vertices `x`
of the ε-mated-CRT map with `q ∈ η '' [ε(x − 1), εx]` induce a connected subgraph. -/
theorem thmB_induce_connected (P : Peanosphere ω η) (hε : 0 < ε) (h : MatedCRT.IsLocallyFinite ε ω) (q : ℂ) :
    ((MatedCRT.graph ε ω h).adj.induce {x : ℤ | q ∈ η '' Icc (ε * ((x : ℝ) - 1)) (ε * x)}).Connected := by
  obtain ⟨t, ht⟩ := P.surj q
  obtain ⟨x₀, hx₀⟩ := thmB_exists_mem_Icc hε t
  have : Nonempty {x : ℤ | q ∈ η '' Icc (ε * ((x : ℝ) - 1)) (ε * x)} := ⟨⟨x₀, t, hx₀, ht⟩⟩
  refine ⟨?_⟩
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  obtain ⟨s, hs, hsq⟩ := hx
  obtain ⟨s', hs', hs'q⟩ := hy
  exact thmB_reachable_of_eqvGen P hε h q (P.onlyMerge s s' (hsq.trans hs'q.symm)) hsq x y _ _ hs hs'

/-- A cellular embedding of the ε-mated-CRT map with cells `η '' [ε(x − 1), εx]` forces `0 < ε`: otherwise the cell
`H_0 = η '' [−ε, 0]` has at most one point and empty interior. -/
theorem thmB_pos_of_cellularEmbedding {h : MatedCRT.IsLocallyFinite ε ω}
    (H : CellularEmbedding (MatedCRT.graph ε ω h) 0)
    (hcell : H.cell = fun x : ℤ => η '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) : 0 < ε := by
  by_contra hε
  have hε' : ε ≤ 0 := le_of_not_gt hε
  obtain ⟨w, hw⟩ := H.interior_cell_nonempty 0
  have hsub : H.cell 0 ⊆ {η 0} := by
    rw [hcell]
    rintro _ ⟨t, ht, rfl⟩
    simp only [Int.cast_zero, zero_sub, mul_neg, mul_one, mul_zero, mem_Icc] at ht
    have ht0 : t = 0 := by linarith [ht.1, ht.2]
    rw [ht0, mem_singleton_iff]
  have hw' := interior_mono hsub hw
  rw [interior_singleton] at hw'
  exact hw'

/-- **Theorem B** (TF2 §5, Details (a)): for a `Peanosphere ω η` and a cellular embedding `H` of the
ε-mated-CRT map whose cells are `H.cell x = η '' [ε(x − 1), εx]`, the cells through any point induce a connected
subgraph: `H.PointConnected`. -/
theorem pointConnected_of_peanosphere_holds {h : MatedCRT.IsLocallyFinite ε ω} (P : Peanosphere ω η)
    (H : CellularEmbedding (MatedCRT.graph ε ω h) 0)
    (hcell : H.cell = fun x : ℤ => η '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) :
    H.PointConnected := by
  have hε : 0 < ε := thmB_pos_of_cellularEmbedding H hcell
  intro q
  have hset : {x : ℤ | q ∈ H.cell x} = {x : ℤ | q ∈ η '' Icc (ε * ((x : ℝ) - 1)) (ε * x)} := by
    rw [hcell]
  rw [hset]
  exact thmB_induce_connected P hε h q

/-- **Corollary B′ for the mated-CRT cells** (TF2 §5): under the hypotheses of Theorem B, for every connected
`S ⊆ ℂ` the vertices whose cells meet `S` induce a connected subgraph. -/
theorem connected_verticesMeeting_of_peanosphere_holds {h : MatedCRT.IsLocallyFinite ε ω} (P : Peanosphere ω η)
    (H : CellularEmbedding (MatedCRT.graph ε ω h) 0)
    (hcell : H.cell = fun x : ℤ => η '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) {S : Set ℂ} (hS : IsConnected S) :
    ((MatedCRT.graph ε ω h).adj.induce (verticesMeeting H.cell S)).Connected :=
  connected_induce_verticesMeeting (pointConnected_of_peanosphere_holds P H hcell) hS

/-! ### Unit mesh (the frozen cell coupling's normalization `cell ω x = η([x − 1, x])`) -/

end MatedCRTHarmonic.RouteM
