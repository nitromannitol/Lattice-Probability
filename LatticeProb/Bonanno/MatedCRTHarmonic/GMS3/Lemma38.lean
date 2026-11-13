/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS3.Lemma38 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS3.Squares
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS3.Lemma37
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS3.FirstVisit

/-!
# GMS [18] Lemma 3.8 with squares, deterministic form

Source: GMS [18] Lemma 3.8 ([18]), corrected and
recast with squares: the circles and
radial segments of Step 2 are replaced by boundaries of axis-parallel squares and horizontal segments, so
that the connectivity used by the maximum principle (Step 3) follows from connectedness along lines (CAL);
`β ≤ α₁/4` is the condition making the Lemma 3.7 average small (here: `√K √E / ι` small).

Fix a centre `z`, an inner radius `ι = sr` and an outer radius `r ≥ 10 ι`; `In = V(∂B_ι(z))`,
`Out = V(∂B_r(z))` (cells meeting the circles). [18]'s `f^s_ε` is
`annHit H z ι r x = P_x[the first visit to In ∪ Out is in Out]`.

* `Lemma38Setup`: `ι > 0`, `10ι ≤ r`, cells meeting `B̄_r(z)` have diameter `≤ δ ≤ ι/6`.
* `annHit_eq_zero_of_mem_in`, `annHit_eq_one_of_mem_out`, `lap_annHit`, `annHit_eq_zero_of_inside`
  (the walk from a cell inside `B̄_ι` meets `In` first).
* `energy_annHit_le` (Step 1 via Dirichlet's principle): `Energy(annHit; G(V(A))) ≤ Energy(f^ε; G(V(A)))`
  for the sampled logarithmic function `f^ε` on `A = {ι < |u − z| < r}`, and
  `energy_annHit_D'_le`: the energy on `G(V(D'))`, `D' = {ι/2 < |u − z| < 9ι}`, is at most that on `G(V(A))`.
* `lemma38_core` (**[18] Lemma 3.8, deterministic form, one scale**): if `Energy(f^ε; G(V(A))) ≤ E`
  (Lemma 3.3), `∑_{V(D')} diam² deg ≤ K` ((3.19), Lemma 3.1 with `f = 1`) and CAL holds, then for every
  `κ > 0` and every `x` whose cell meets `B_{5ι}(z)` ([18] has `B_{4sr}`; `5ι` also covers its
  grid step `[s, 4s] ⊂ [s', 5s']`),
  `P_x[X hits V(∂B_ι(z)) before V(∂B_r(z))] ≥ 1 − (6 √K √E / ι + 2κ)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Real
open scoped ENNReal Classical

namespace MatedCRTHarmonic.GMS3

open LFMultigraph Harmonic HarmonicInfinity Markov

variable {V E : Type*} {G : LFMultigraph V E} {o : V} (H : CellularEmbedding G o)

/-- The cells meeting the circle `∂B_a(z)`: `V(∂B_a(z))`. -/
def vCircle (z : ℂ) (a : ℝ) : Set V := verticesMeeting H.cell {u | ‖u - z‖ = a}

/-- [18]'s `f^s_ε` of Lemma 3.8: `P_x[the first visit to V(∂B_ι) ∪ V(∂B_r) is in V(∂B_r)]`. -/
def annHit (z : ℂ) (ι r : ℝ) (x : V) : ℝ :=
  (hitDist G (vCircle H z ι ∪ vCircle H z r) x (vCircle H z r)).toReal

/-- The standing assumptions of the single-scale Lemma 3.8. -/
structure Lemma38Setup (z : ℂ) (ι r δ : ℝ) : Prop where
  ι_pos : 0 < ι
  ten_le : 10 * ι ≤ r
  δ_nonneg : 0 ≤ δ
  six_le : 6 * δ ≤ ι
  diam_le : ∀ x, (H.cell x ∩ closedBall z r).Nonempty → cellDiam H x ≤ δ

include H in
/-- A cellular embedding has infinitely many vertices (finitely many compact cells cannot cover `ℂ`). -/
theorem infinite_vertex : Infinite V := by
  by_contra hfin
  rw [not_infinite_iff_finite] at hfin
  have hcpt : IsCompact (⋃ x, H.cell x) := isCompact_iUnion fun x => H.isCompact_cell x
  rw [H.iUnion_cell] at hcpt
  exact noncompact_univ ℂ hcpt

variable {H}

theorem vCircle_disjoint {z : ℂ} {ι r δ : ℝ} (hS : Lemma38Setup H z ι r δ) :
    Disjoint (vCircle H z ι) (vCircle H z r) := by
  rw [Set.disjoint_left]
  rintro x ⟨u, hu, hu'⟩ ⟨v, hv, hv'⟩
  simp only [Set.mem_ofPred_eq] at hu' hv'
  have hd := hS.diam_le x ⟨v, hv, by rw [mem_closedBall, dist_eq_norm]; exact hv'.le⟩
  have h1 := dist_le_cellDiam H hv hu
  rw [dist_eq_norm] at h1
  have h2 : ‖v - z‖ - ‖u - z‖ ≤ ‖v - u‖ := by
    have := norm_sub_norm_le (v - z) (u - z)
    rwa [sub_sub_sub_cancel_right] at this
  have := hS.ten_le
  have := hS.six_le
  have := hS.ι_pos
  linarith

theorem annHit_eq_zero_of_mem_in {z : ℂ} {ι r δ : ℝ} (hS : Lemma38Setup H z ι r δ) {x : V}
    (hx : x ∈ vCircle H z ι) : annHit H z ι r x = 0 := by
  unfold annHit
  rw [hitDist_of_mem G (Set.mem_union_left _ hx), Set.indicator_of_notMem
    (Set.disjoint_left.mp (vCircle_disjoint hS) hx), ENNReal.toReal_zero]

theorem annHit_eq_one_of_mem_out {z : ℂ} {ι r : ℝ} {x : V} (hx : x ∈ vCircle H z r) :
    annHit H z ι r x = 1 := by
  unfold annHit
  rw [hitDist_of_mem G (Set.mem_union_right _ hx), Set.indicator_of_mem hx, Pi.one_apply,
    ENNReal.toReal_one]

theorem lap_annHit {z : ℂ} {ι r : ℝ} {x : V} (hx : x ∉ vCircle H z ι ∪ vCircle H z r) :
    lap G (annHit H z ι r) x = 0 :=
  lap_hitDist G hx _

/-- From a cell inside `B̄_ι(z)` the walk meets `V(∂B_ι)` before `V(∂B_r)`. -/
theorem annHit_eq_zero_of_inside (hconn : G.adj.Connected) {z : ℂ} {ι r δ : ℝ}
    (hS : Lemma38Setup H z ι r δ) {x : V} (hx : ∀ u ∈ H.cell x, ‖u - z‖ ≤ ι) :
    annHit H z ι r x = 0 := by
  have hle : hitDist G (vCircle H z ι ∪ vCircle H z r) x (vCircle H z r) ≤ ENNReal.ofReal 0 := by
    refine hitDist_le_of_firstVisit G hconn (I := vCircle H z ι ∪ vCircle H z r) le_rfl
      (G' := vCircle H z ι) (fun y hy => ?_) ?_
    · rw [hitDist_of_mem G (Set.mem_union_left _ hy),
        Set.indicator_of_notMem (Set.disjoint_left.mp (vCircle_disjoint hS) hy), ENNReal.ofReal_zero]
    · intro n X h0 hstep hn hfirst
      rcases hn with hin | hout
      · exact hin
      obtain ⟨v, hv, hv'⟩ := hout
      obtain ⟨u, hu⟩ := cell_nonempty H x
      obtain ⟨j, hj, hjm⟩ := exists_crossing_of_walk H (continuous_norm_sub_const z) (t := ι) n X hstep
        ⟨u, h0 ▸ hu, hx u hu⟩ ⟨v, hv, by simp only [Set.mem_ofPred_eq] at hv'; linarith [hS.ten_le,
          hS.ι_pos]⟩
      have hjm' : X j ∈ vCircle H z ι := hjm
      rcases Nat.lt_or_ge j n with hlt | hge
      · exact absurd (Set.mem_union_left _ hjm') (hfirst j hlt)
      · rw [show j = n by omega] at hjm'
        exact hjm'
  unfold annHit
  rw [ENNReal.ofReal_zero, nonpos_iff_eq_zero] at hle
  rw [hle, ENNReal.toReal_zero]

/-- **Total mass**: from a cell meeting `B̄_r(z)` the walk visits `V(∂B_ι) ∪ V(∂B_r)` a.s. -/
theorem walkLaw_hitTime_circles_ne_top (hconn : G.adj.Connected) {z : ℂ} {ι r : ℝ} {x : V}
    (hx : (H.cell x ∩ closedBall z r).Nonempty) :
    G.walkLaw x {ω | hitTime (vCircle H z ι ∪ vCircle H z r) (G.vertexPath ω) ≠ ⊤} = 1 := by
  have := infinite_vertex H
  set U : Set V := (vFin H (ball z r) : Set V)
  have hU : U.Finite := (vFin H (ball z r)).finite_toSet
  have hesc : ∀ y ∈ U, ∃ w, w ∉ U ∧ G.adj.Reachable y w := by
    intro y _
    obtain ⟨w, hw⟩ := (Set.infinite_univ.sdiff hU).nonempty
    exact ⟨w, hw.2, hconn.preconnected y w⟩
  refine walkLaw_hitTime_ne_top_of_exit G hconn hU hesc ?_
  intro n X h0 hstep hn
  obtain ⟨u, hu, hu'⟩ := hx
  obtain ⟨v, hv⟩ := cell_nonempty H (X n)
  have hvout : r ≤ ‖v - z‖ := by
    by_contra hlt
    push Not at hlt
    exact hn ((mem_vFin H isBounded_ball).mpr ⟨v, hv, by rw [mem_ball, dist_eq_norm]; exact hlt⟩)
  obtain ⟨j, hj, hjm⟩ := exists_crossing_of_walk H (continuous_norm_sub_const z) (t := r) n X hstep
    ⟨u, h0 ▸ hu, by rw [mem_closedBall, dist_eq_norm] at hu'; exact hu'⟩ ⟨v, hv, hvout⟩
  exact ⟨j, hj, Set.mem_union_right _ hjm⟩

/-- `P_x[hit V(∂B_ι) first] = 1 − annHit` (from a cell meeting `B̄_r(z)`). -/
theorem toReal_hitDist_in_eq {z : ℂ} {ι r δ : ℝ} (hS : Lemma38Setup H z ι r δ)
    (hconn : G.adj.Connected) {x : V} (hx : (H.cell x ∩ closedBall z r).Nonempty) :
    (hitDist G (vCircle H z ι ∪ vCircle H z r) x (vCircle H z ι)).toReal = 1 - annHit H z ι r x := by
  have h := hitDist_add_compl_eq_one G (walkLaw_hitTime_circles_ne_top hconn (ι := ι) hx)
    (vCircle H z ι)
  have h2 : hitDist G (vCircle H z ι ∪ vCircle H z r) x (vCircle H z ι)ᶜ =
      hitDist G (vCircle H z ι ∪ vCircle H z r) x (vCircle H z r) := by
    rw [hitDist_inter_self G _ (vCircle H z ι)ᶜ, hitDist_inter_self G _ (vCircle H z r)]
    congr 1
    ext y
    simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff]
    constructor
    · rintro ⟨h | h, h'⟩
      · exact absurd h h'
      · exact ⟨Or.inr h, h⟩
    · rintro ⟨-, h⟩
      exact ⟨Or.inr h, Set.disjoint_right.mp (vCircle_disjoint hS) h⟩
  rw [h2] at h
  unfold annHit
  have hf1 := hitDist_ne_top G (vCircle H z ι ∪ vCircle H z r) (vCircle H z ι) x
  have hf2 := hitDist_ne_top G (vCircle H z ι ∪ vCircle H z r) (vCircle H z r) x
  have := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_add hf1 hf2, ENNReal.toReal_one] at this
  linarith

/-! ### Step 1: the energy of `annHit` -/

/-- Energy comparison when every edge with a nonzero term lies in `G(T)`. -/
theorem energy_le_of_edges_subset (S T : Finset V) (f : V → ℝ)
    (h : ∀ e ∈ edgesIn G S, (f (G.src e) - f (G.tgt e)) ^ 2 ≠ 0 → e ∈ edgesIn G T) :
    energy G S f ≤ energy G T f := by
  unfold energy
  calc ∑ e ∈ edgesIn G S, (f (G.src e) - f (G.tgt e)) ^ 2
      = ∑ e ∈ (edgesIn G S).filter (fun e => (f (G.src e) - f (G.tgt e)) ^ 2 ≠ 0),
          (f (G.src e) - f (G.tgt e)) ^ 2 := (Finset.sum_filter_ne_zero _).symm
    _ ≤ ∑ e ∈ edgesIn G T, (f (G.src e) - f (G.tgt e)) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun e he => h e (Finset.mem_filter.mp he).1
          (Finset.mem_filter.mp he).2) fun _ _ _ => sq_nonneg _

/-- A cell meeting the open annulus `A = {ι < |u − z| < r}` but neither of its circles lies in `A`. -/
theorem cell_subset_annulus_of_not_circle {z : ℂ} {ι r : ℝ} {x : V}
    (hA : (H.cell x ∩ annulusSet z ι r).Nonempty) (hin : x ∉ vCircle H z ι)
    (hout : x ∉ vCircle H z r) : H.cell x ⊆ annulusSet z ι r := by
  obtain ⟨a, ha, haA⟩ := hA
  intro u hu
  refine ⟨?_, ?_⟩
  · by_contra h
    push Not at h
    obtain ⟨c, hc, hct⟩ := exists_mem_eq_of_isPreconnected (H.isConnected_cell x).isPreconnected
      (continuous_norm_sub_const z) hu ha h haA.1.le
    exact hin ⟨c, hc, hct⟩
  · by_contra h
    push Not at h
    obtain ⟨c, hc, hct⟩ := exists_mem_eq_of_isPreconnected (H.isConnected_cell x).isPreconnected
      (continuous_norm_sub_const z) ha hu haA.2.le h
    exact hout ⟨c, hc, hct⟩

/-- **Step 1 via Dirichlet's principle**: `Energy(annHit; G(V(A))) ≤ Energy(f^ε; G(V(A)))`. -/
theorem energy_annHit_le {z : ℂ} {ι r δ : ℝ} (hS : Lemma38Setup H z ι r δ) :
    energy G (vFin H (annulusSet z ι r)) (annHit H z ι r) ≤
      energy G (vFin H (annulusSet z ι r)) (logRad z ι r ∘ annRef H z ι r) := by
  have hb := isBounded_annulusSet z ι r
  have hι := hS.ι_pos
  have hr : 0 < r := by linarith [hS.ten_le]
  refine energy_le_of_harmonic G (B := vCircle H z ι ∪ vCircle H z r) ?_ ?_ ?_
  · intro x hx hxB d hd
    have hsub := cell_subset_annulus_of_not_circle ((mem_vFin H hb).mp hx)
      (fun h => hxB (Or.inl h)) (fun h => hxB (Or.inr h))
    exact dtgt_mem_vFin_of_subset H hb hsub hx hd
  · intro x _ hxB
    exact lap_annHit hxB
  · intro x _ hxB
    simp only [Function.comp]
    rcases hxB with hin | hout
    · rw [annHit_eq_zero_of_mem_in hS hin, logRad_of_norm_eq_left (norm_annRef_inner H hin)]
    · have hnin : ¬ (H.cell x ∩ {u | ‖u - z‖ = ι}).Nonempty := fun h =>
        Set.disjoint_left.mp (vCircle_disjoint hS) h hout
      rw [annHit_eq_one_of_mem_out hout, logRad_of_norm_eq_right hι hr (by linarith [hS.ten_le])
        (norm_annRef_outer H hnin hout)]

/-- Cells of `V(D')` outside `V(A)` lie in `B̄_ι(z)` (`D' = {ι/2 < |u − z| < 9ι}`). -/
theorem cell_inside_of_mem_D' {z : ℂ} {ι r δ : ℝ} (hS : Lemma38Setup H z ι r δ) {x : V}
    (hxD : x ∈ vFin H (annulusSet z (ι / 2) (9 * ι))) (hxA : x ∉ vFin H (annulusSet z ι r)) :
    ∀ u ∈ H.cell x, ‖u - z‖ ≤ ι := by
  have hι := hS.ι_pos
  have h10 := hS.ten_le
  obtain ⟨a, ha, haD⟩ := (mem_vFin H (isBounded_annulusSet z _ _)).mp hxD
  have hnA : ∀ u ∈ H.cell x, ‖u - z‖ ≤ ι ∨ r ≤ ‖u - z‖ := by
    intro u hu
    by_contra h
    push Not at h
    exact hxA ((mem_vFin H (isBounded_annulusSet z _ _)).mpr ⟨u, hu, h.1, h.2⟩)
  have ha' : ‖a - z‖ ≤ ι := by
    rcases hnA a ha with h | h
    · exact h
    · linarith [haD.2]
  intro u hu
  rcases hnA u hu with h | h
  · exact h
  · exfalso
    obtain ⟨c, hc, hct⟩ := exists_mem_eq_of_isPreconnected (H.isConnected_cell x).isPreconnected
      (continuous_norm_sub_const z) (t := (ι + r) / 2) ha hu (by linarith) (by linarith)
    exact hxA ((mem_vFin H (isBounded_annulusSet z _ _)).mpr ⟨c, hc, by
      constructor <;> linarith⟩)

/-- **The energy on `G(V(D'))` is at most the energy on `G(V(A))`** (`annHit = 0` near `B̄_ι`). -/
theorem energy_annHit_D'_le (hconn : G.adj.Connected) {z : ℂ} {ι r δ : ℝ}
    (hS : Lemma38Setup H z ι r δ) :
    energy G (vFin H (annulusSet z (ι / 2) (9 * ι))) (annHit H z ι r) ≤
      energy G (vFin H (annulusSet z ι r)) (annHit H z ι r) := by
  have hb := isBounded_annulusSet z ι r
  -- `annHit` vanishes at vertices of `V(D') \ V(A)` and at their neighbours
  have hzero : ∀ x ∈ vFin H (annulusSet z (ι / 2) (9 * ι)), x ∉ vFin H (annulusSet z ι r) →
      annHit H z ι r x = 0 := fun x hxD hxA =>
    annHit_eq_zero_of_inside hconn hS (cell_inside_of_mem_D' hS hxD hxA)
  have hnb : ∀ x ∈ vFin H (annulusSet z (ι / 2) (9 * ι)), x ∉ vFin H (annulusSet z ι r) →
      ∀ y ∈ vFin H (annulusSet z (ι / 2) (9 * ι)), G.adj.Adj x y → annHit H z ι r y = 0 := by
    intro x hxD hxA y hyD hadj
    by_cases hyA : y ∈ vFin H (annulusSet z ι r)
    · obtain ⟨c, hcx, hcy⟩ := H.inter_of_adj x y hadj
      obtain ⟨b, hby, hbA⟩ := (mem_vFin H hb).mp hyA
      obtain ⟨m, hm, hmt⟩ := exists_mem_eq_of_isPreconnected (H.isConnected_cell y).isPreconnected
        (continuous_norm_sub_const z) (t := ι) hcy hby (cell_inside_of_mem_D' hS hxD hxA c hcx)
        hbA.1.le
      exact annHit_eq_zero_of_mem_in hS ⟨m, hm, hmt⟩
    · exact hzero y hyD hyA
  refine energy_le_of_edges_subset _ _ _ fun e he hne => ?_
  rw [mem_edgesIn] at he ⊢
  have hloop : G.src e ≠ G.tgt e := fun h => hne (by rw [h, sub_self, sq, mul_zero])
  have hadj := adj_of_edge G hloop
  by_contra hcon
  rw [not_and_or] at hcon
  rcases hcon with h | h
  · exact hne (by rw [hzero _ he.1 h, hnb _ he.1 h _ he.2 hadj, sub_self, sq, mul_zero])
  · exact hne (by rw [hzero _ he.2 h, hnb _ he.2 h _ he.1 hadj.symm, sub_self, sq, mul_zero])

/-! ### Step 2: the families of squares and horizontal segments -/

/-- The horizontal segment at height `t` from the circle `∂B_ι(z)` to the abscissa `z.re + 7ι`. -/
def hSegP (z : ℂ) (ι t : ℝ) : Set ℂ :=
  segment ℝ (⟨z.re + Real.sqrt (ι ^ 2 - t ^ 2), z.im + t⟩ : ℂ) ⟨z.re + 7 * ι, z.im + t⟩

theorem sqrt_sub_le {ι t : ℝ} (hι : 0 < ι) : Real.sqrt (ι ^ 2 - t ^ 2) ≤ ι := by
  rw [Real.sqrt_le_left hι.le]
  nlinarith [sq_nonneg t]

theorem mem_hSegP {z u : ℂ} {ι t : ℝ} (hι : 0 < ι) :
    u ∈ hSegP z ι t ↔ u.im = z.im + t ∧ z.re + Real.sqrt (ι ^ 2 - t ^ 2) ≤ u.re ∧
      u.re ≤ z.re + 7 * ι := by
  unfold hSegP
  rw [mem_segment_horizontal (by linarith [sqrt_sub_le (t := t) hι])]

theorem norm_sub_sq_eq (u z : ℂ) : ‖u - z‖ ^ 2 = (u.re - z.re) ^ 2 + (u.im - z.im) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  ring

theorem sqrt_two_lt_three_halves : Real.sqrt 2 < 3 / 2 := by
  rw [Real.sqrt_lt' (by norm_num)]
  norm_num

theorem hSegP_subset {z : ℂ} {ι t : ℝ} (hι : 0 < ι) (ht : t ∈ Icc 0 (ι / 2)) :
    hSegP z ι t ⊆ annulusSet z (ι / 2) (9 * ι) := by
  intro u hu
  obtain ⟨him, h1, h2⟩ := (mem_hSegP hι).mp hu
  have hsq := norm_sub_sq_eq u z
  have hs0 : 0 ≤ Real.sqrt (ι ^ 2 - t ^ 2) := Real.sqrt_nonneg _
  have hsq' : Real.sqrt (ι ^ 2 - t ^ 2) ^ 2 = ι ^ 2 - t ^ 2 :=
    Real.sq_sqrt (by nlinarith [ht.1, ht.2])
  have hre : Real.sqrt (ι ^ 2 - t ^ 2) ≤ u.re - z.re := by linarith
  have hre2 : ι ^ 2 - t ^ 2 ≤ (u.re - z.re) ^ 2 := by
    rw [← hsq']; exact pow_le_pow_left₀ hs0 hre 2
  have him' : u.im - z.im = t := by linarith
  have hnorm0 : 0 ≤ ‖u - z‖ := norm_nonneg _
  constructor
  · have : ι ^ 2 ≤ ‖u - z‖ ^ 2 := by rw [hsq, him']; linarith
    nlinarith
  · have hre3 : (u.re - z.re) ^ 2 ≤ (7 * ι) ^ 2 :=
      pow_le_pow_left₀ (hs0.trans hre) (by linarith) 2
    have : ‖u - z‖ ^ 2 < (9 * ι) ^ 2 := by
      rw [hsq, him']; nlinarith [ht.1, ht.2]
    nlinarith

theorem abs_sub_le_dist_of_mem_hSegP {z u v : ℂ} {ι s t : ℝ} (hι : 0 < ι) (hu : u ∈ hSegP z ι s)
    (hv : v ∈ hSegP z ι t) : |s - t| ≤ dist u v := by
  have h1 := ((mem_hSegP hι).mp hu).1
  have h2 := ((mem_hSegP hι).mp hv).1
  rw [dist_eq_norm]
  calc |s - t| = |(u - v).im| := by rw [Complex.sub_im, h1, h2]; ring_nf
    _ ≤ ‖u - v‖ := Complex.abs_im_le_norm _

theorem sqLoop_subset {z : ℂ} {ι a : ℝ} (hι : 0 < ι) (ha : a ∈ Icc (5 * ι) (6 * ι)) :
    sqLoop z a ⊆ annulusSet z (ι / 2) (9 * ι) := by
  intro u hu
  have h1 : a ≤ ‖u - z‖ := hu ▸ supNorm_le_norm (u - z)
  have h2 : ‖u - z‖ ≤ Real.sqrt 2 * a := hu ▸ norm_le_sqrt_two_mul_supNorm (u - z)
  have h3 := sqrt_two_lt_three_halves
  have ha0 : 0 < a := by linarith [ha.1]
  constructor
  · linarith [ha.1]
  · calc ‖u - z‖ ≤ Real.sqrt 2 * a := h2
      _ < 3 / 2 * a := by gcongr
      _ ≤ 9 * ι := by linarith [ha.2]

/-- **[18] Lemma 3.8 with squares, deterministic form (one scale)**: with `E` bounding the energy of
The sampled logarithmic function on `G(V(A))` (Lemma 3.3) and `K` bounding `∑_{V(D')} diam² deg`
((3.19)), under CAL, for every `κ > 0` and every vertex `x` whose cell meets `B_{5ι}(z)` ([18] has
`B_{4sr}`; `5ι` also covers its grid step `[s, 4s] ⊂ [s', 5s']`):
`P_x[X hits V(∂B_ι(z)) before V(∂B_r(z))] ≥ 1 − (6 √K √E / ι + 2κ)`. -/
theorem lemma38_core (hconn : G.adj.Connected) (hcal : ConnectedAlongLines H) {z : ℂ}
    {ι r δ K E κ : ℝ} (hS : Lemma38Setup H z ι r δ)
    (hE : energy G (vFin H (annulusSet z ι r)) (logRad z ι r ∘ annRef H z ι r) ≤ E)
    (hK : ∑ x ∈ vFin H (annulusSet z (ι / 2) (9 * ι)), cellDiam H x ^ 2 * G.deg x ≤ K)
    (hκ : 0 < κ) {x : V} (hx : (H.cell x ∩ ball z (5 * ι)).Nonempty) :
    1 - (6 * Real.sqrt K * Real.sqrt E / ι + 2 * κ) ≤
      (hitDist G (vCircle H z ι ∪ vCircle H z r) x (vCircle H z ι)).toReal := by
  have hι := hS.ι_pos
  have h10 := hS.ten_le
  set f := annHit H z ι r with hfdef
  set D' := annulusSet z (ι / 2) (9 * ι) with hD'
  have hD'b : Bornology.IsBounded D' := isBounded_annulusSet z _ _
  have hEf : energy G (vFin H D') f ≤ E :=
    ((energy_annHit_D'_le hconn hS).trans (energy_annHit_le hS)).trans hE
  have hK0 : 0 ≤ K := (Finset.sum_nonneg fun x _ => by
    have := cellDiam_nonneg H x; positivity).trans hK
  set B := 2 * Real.sqrt K * Real.sqrt E with hBdef
  have hB0 : 0 ≤ B := by positivity
  have hsqE : Real.sqrt (energy G (vFin H D') f) ≤ Real.sqrt E := Real.sqrt_le_sqrt hEf
  -- the square family
  have hint1 : ∫⁻ a in Icc (5 * ι) (6 * ι), ENNReal.ofReal (tv G (vFin H (sqLoop z a)) f) ≤
      ENNReal.ofReal B := by
    refine (lemma37 H hD'b (sqLoop z) (C := 1) zero_le_one (fun a ha => sqLoop_subset hι ha)
      (fun s _ t _ u hu v hv => by rw [one_mul]; exact abs_sub_le_dist_of_mem_sqLoop hu hv) hK f).trans
      (ENNReal.ofReal_le_ofReal ?_)
    rw [hBdef]
    nlinarith [Real.sqrt_nonneg K]
  obtain ⟨a₁, ha₁, htv₁⟩ := exists_le_of_setLIntegral_le (c := B / ι + κ) (by linarith) hint1 hB0
    (by rw [show 6 * ι - 5 * ι = ι by ring, add_mul, div_mul_cancel₀ _ hι.ne']; nlinarith)
  -- the segment family
  have hint2 : ∫⁻ t in Icc 0 (ι / 2), ENNReal.ofReal (tv G (vFin H (hSegP z ι t)) f) ≤
      ENNReal.ofReal B := by
    refine (lemma37 H hD'b (hSegP z ι) (C := 1) zero_le_one (fun t ht => hSegP_subset hι ht)
      (fun s _ t _ u hu v hv => by rw [one_mul]; exact abs_sub_le_dist_of_mem_hSegP hι hu hv)
      hK f).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hBdef]
    nlinarith [Real.sqrt_nonneg K]
  obtain ⟨t₂, ht₂, htv₂⟩ := exists_le_of_setLIntegral_le (c := 2 * B / ι + κ) (by linarith) hint2
    hB0 (by
      have e : (2 * B / ι + κ) * (ι / 2 - 0) = B + κ * ι / 2 := by field_simp; ring
      rw [e]; nlinarith)
  -- the common vertex and the inner vertex
  have ha₁0 : 0 ≤ a₁ := by linarith [ha₁.1]
  set q : ℂ := ⟨z.re + a₁, z.im + t₂⟩ with hq
  have hqS : q ∈ sqLoop z a₁ := by
    show max |(q - z).re| |(q - z).im| = a₁
    simp only [hq, Complex.sub_re, Complex.sub_im, add_sub_cancel_left]
    rw [abs_of_nonneg ha₁0, abs_of_nonneg ht₂.1, max_eq_left (by linarith [ht₂.2, ha₁.1])]
  have hqP : q ∈ hSegP z ι t₂ := (mem_hSegP hι).mpr ⟨rfl, by
    simp only [hq]; linarith [sqrt_sub_le (t := t₂) hι, ha₁.1], by
    simp only [hq]; linarith [ha₁.2]⟩
  obtain ⟨w, hw⟩ : ∃ w, q ∈ H.cell w := by
    have : q ∈ ⋃ c, H.cell c := by rw [H.iUnion_cell]; trivial
    simpa using this
  set p₀ : ℂ := ⟨z.re + Real.sqrt (ι ^ 2 - t₂ ^ 2), z.im + t₂⟩ with hp₀
  have hp₀P : p₀ ∈ hSegP z ι t₂ := left_mem_segment ℝ _ _
  have hp₀c : ‖p₀ - z‖ = ι := by
    have hsq := norm_sub_sq_eq p₀ z
    simp only [hp₀, add_sub_cancel_left] at hsq
    rw [Real.sq_sqrt (by nlinarith [ht₂.1, ht₂.2])] at hsq
    have : ‖p₀ - z‖ ^ 2 = ι ^ 2 := by rw [hsq]; ring
    nlinarith [norm_nonneg (p₀ - z)]
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, p₀ ∈ H.cell x₀ := by
    have : p₀ ∈ ⋃ c, H.cell c := by rw [H.iUnion_cell]; trivial
    simpa using this
  have hfx₀ : f x₀ = 0 := annHit_eq_zero_of_mem_in hS ⟨p₀, hx₀, hp₀c⟩
  have hbS := isBounded_sqLoop z a₁
  have hbP : Bornology.IsBounded (hSegP z ι t₂) :=
    (isBounded_annulusSet z (ι / 2) (9 * ι)).subset (hSegP_subset hι ht₂)
  have hwS : w ∈ vFin H (sqLoop z a₁) := (mem_vFin H hbS).mpr ⟨q, hw, hqS⟩
  have hwP : w ∈ vFin H (hSegP z ι t₂) := (mem_vFin H hbP).mpr ⟨q, hw, hqP⟩
  have hx₀P : x₀ ∈ vFin H (hSegP z ι t₂) := (mem_vFin H hbP).mpr ⟨p₀, hx₀, hp₀P⟩
  -- the segment's cells are connected (CAL)
  have hsegconn : (G.adj.induce (vFin H (hSegP z ι t₂) : Set V)).Reachable ⟨w, hwP⟩ ⟨x₀, hx₀P⟩ := by
    have hsub : verticesMeeting H.cell (hSegP z ι t₂) ⊆ (vFin H (hSegP z ι t₂) : Set V) := by
      rw [coe_vFin hbP]
    have hc := hcal (⟨z.re + Real.sqrt (ι ^ 2 - t₂ ^ 2), z.im + t₂⟩ : ℂ)
      ⟨z.re + 7 * ι, z.im + t₂⟩ (Or.inr rfl)
    exact reachable_induce_of_subset hsub hc ⟨q, hw, hqP⟩ ⟨p₀, hx₀, hp₀P⟩
  -- maximum of `f` on the square loop
  have hmaxS : ∀ y ∈ vFin H (sqLoop z a₁), f y ≤ B / ι + κ + (2 * B / ι + κ) := by
    intro y hy
    have h1 := abs_sub_le_tv_of_reachable G f hy hwS (reachable_sqLoop hcal ha₁0 hy hwS)
    have h2 := abs_sub_le_tv_of_reachable G f hwP hx₀P hsegconn
    calc f y = f y - f x₀ := by rw [hfx₀, sub_zero]
      _ ≤ |f y - f w| + |f w - f x₀| := by
          have := abs_sub_le (f y) (f w) (f x₀)
          linarith [le_abs_self (f y - f x₀)]
      _ ≤ B / ι + κ + (2 * B / ι + κ) := add_le_add (h1.trans htv₁) (h2.trans htv₂)
  -- the maximum principle
  set M := B / ι + κ + (2 * B / ι + κ) with hM
  have hMP : hitDist G (vCircle H z ι ∪ vCircle H z r) x (vCircle H z r) ≤ ENNReal.ofReal M := by
    refine hitDist_le_of_firstVisit G hconn (I := vCircle H z ι ∪ vCircle H z r)
      (B := vCircle H z ι ∪ vCircle H z r ∪ (vFin H (sqLoop z a₁) : Set V)) Set.subset_union_left
      (G' := vCircle H z ι ∪ (vFin H (sqLoop z a₁) : Set V)) (fun y hy => ?_) ?_
    · rcases hy with hin | hsq
      · rw [hitDist_of_mem G (Set.mem_union_left _ hin),
          Set.indicator_of_notMem (Set.disjoint_left.mp (vCircle_disjoint hS) hin)]
        exact bot_le
      · rw [← ENNReal.ofReal_toReal (hitDist_ne_top G _ _ y)]
        exact ENNReal.ofReal_le_ofReal (hmaxS y hsq)
    · intro n X h0 hstep hn hfirst
      rcases hn with (hin | hout) | hsq
      · exact Or.inl hin
      · obtain ⟨u, hu, hu'⟩ := hx
        obtain ⟨v, hv, hv'⟩ := hout
        have hv'' : ‖v - z‖ = r := hv'
        obtain ⟨j, hj, hjm⟩ := exists_crossing_of_walk H
          (continuous_supNorm.comp (continuous_id.sub continuous_const)) (t := a₁) n X hstep
          ⟨u, h0 ▸ hu, by
            have : ‖u - z‖ < 5 * ι := by rw [mem_ball, dist_eq_norm] at hu'; exact hu'
            have := supNorm_le_norm (u - z)
            show supNorm (u - z) ≤ a₁
            linarith [ha₁.1]⟩
          ⟨v, hv, by
            have h1 := norm_le_sqrt_two_mul_supNorm (v - z)
            have h2 := sqrt_two_lt_three_halves
            have hsn := supNorm_nonneg (v - z)
            have h3 : Real.sqrt 2 * supNorm (v - z) ≤ 3 / 2 * supNorm (v - z) :=
              mul_le_mul_of_nonneg_right h2.le hsn
            show a₁ ≤ supNorm (v - z)
            linarith [ha₁.2]⟩
        have hjS : X j ∈ (vFin H (sqLoop z a₁) : Set V) := by
          rw [Finset.mem_coe, mem_vFin H hbS]
          exact hjm
        rcases Nat.lt_or_ge j n with hlt | hge
        · exact absurd (Set.mem_union_right _ hjS) (hfirst j hlt)
        · rw [show j = n by omega] at hjS
          exact Or.inr hjS
      · exact Or.inr hsq
  have hfx : f x ≤ M := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hMP
    rwa [ENNReal.toReal_ofReal (by rw [hM]; positivity)] at this
  have hxr : (H.cell x ∩ closedBall z r).Nonempty := by
    obtain ⟨u, hu, hu'⟩ := hx
    refine ⟨u, hu, ?_⟩
    rw [mem_closedBall]; rw [mem_ball] at hu'; linarith
  rw [toReal_hitDist_in_eq hS hconn hxr]
  have : M = 6 * Real.sqrt K * Real.sqrt E / ι + 2 * κ := by
    rw [hM, hBdef]; field_simp; ring
  linarith

end MatedCRTHarmonic.GMS3
