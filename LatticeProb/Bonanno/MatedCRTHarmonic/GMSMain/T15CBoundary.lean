/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSMain.T15CBoundary at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.T15CHitting
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS3.Recurrence
import LatticeProb.Bonanno.MatedCRTHarmonic.Infinite.Cellular

/-!
# [18] Theorem 3.9, boundary estimate: from (3.38) to (3.31)

Source: [18] , proof of Theorem 3.9, `[18]`: "Again using that `f^ε`
is discrete harmonic, we obtain (3.31)". Deterministic, for a cellular embedding `H` of a connected graph `G`.

Notation: `D` open and bounded, `V(D) = vFin H D`, `V(∂D) = verticesMeeting H.cell (frontier D)`, and [18]'s
harmonicity (`f^ε` discrete harmonic on `VG^ε(D) \ VG^ε(∂D)`, `[18]`) in the form of G3's Lemma 3.3:
`∀ x ∈ V(D), H_x ∩ ∂D = ∅ → lap G f x = 0` (`GMS3.lap`, the unnormalized graph Laplacian).

* `t15c_lap_sum`, `t15c_lap_sub`: the Laplacian is linear.
* `t15c_le_zero_of_lap_eq_zero` (**maximum principle**): on a connected infinite graph, a function harmonic at the
  vertices of `S \ B` (`S` finite, darts from `S \ B` stay in `S`) and `≤ 0` on `S ∩ B` is `≤ 0` on `S`.
* `t15c_walkLaw_hitTime_ne_top`: from `x ∈ V(D)` the walk hits `V(∂D)` almost surely (exit from the finite set
  `V(D) \ V(∂D)`); `t15c_hitDist_firstHit_compl_eq_zero`: the first hit lies in `V(D) ∩ V(∂D)` almost surely.
* `t15c_eq_sum_hitDist` (**harmonic representation**): `f(x) = ∑_{w ∈ V(D) ∩ V(∂D)} P_x[X_{T_{V(∂D)}} = w] f(w)`.
* `t15c_ge_of_hitDist_compl_le`, `t15c_le_of_hitDist_compl_le` (**(3.31) from (3.38)**): if `|f| ≤ M` on `V(D)`,
  `P_x[X_{T_{V(∂D)}} ∉ W] ≤ q` and `m ≤ f` (resp. `f ≤ m`) on `V(D) ∩ V(∂D) ∩ W`, with `m ≤ M` (resp. `-M ≤ m`), then
  `m − 2 M q ≤ f(x)` (resp. `f(x) ≤ m + 2 M q`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal Classical

namespace MatedCRTHarmonic.GMSMain

open Markov LFMultigraph GoodScales HarmonicInfinity GMS3

variable {V E : Type*} {G : LFMultigraph V E} {o : V}

/-! ### Linearity of the Laplacian and the maximum principle -/

/-- The Laplacian of a finite linear combination. -/
theorem t15c_lap_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (h : ι → V → ℝ) (x : V) :
    lap G (fun y => ∑ i ∈ s, c i * h i y) x = ∑ i ∈ s, c i * lap G (h i) x := by
  unfold lap
  simp_rw [← Finset.sum_sub_distrib, ← mul_sub, Finset.mul_sum]
  exact Finset.sum_comm

/-- The Laplacian of a finite linear combination, coefficients on the right. -/
theorem t15c_lap_sum_mul {ι : Type*} (s : Finset ι) (c : ι → ℝ) (h : ι → V → ℝ) (x : V) :
    lap G (fun y => ∑ i ∈ s, h i y * c i) x = ∑ i ∈ s, lap G (h i) x * c i := by
  simp_rw [mul_comm _ (c _)]
  exact t15c_lap_sum s c h x

/-- The Laplacian of a difference. -/
theorem t15c_lap_sub (f g : V → ℝ) (x : V) : lap G (fun y => f y - g y) x = lap G f x - lap G g x := by
  unfold lap
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  ring

/-- The Laplacian of a negation. -/
theorem t15c_lap_neg (f : V → ℝ) (x : V) : lap G (fun y => -f y) x = -lap G f x := by
  unfold lap
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  ring

/-- A vertex where a harmonic function attains its maximum over a set containing all its neighbours passes the
maximum to every neighbour. -/
theorem t15c_eq_of_lap_eq_zero_of_isMax {S : Finset V} {u : V → ℝ} {x : V}
    (hnb : ∀ d ∈ G.outDarts x, G.dtgt d ∈ S) (hharm : lap G u x = 0) (hmax : ∀ y ∈ S, u y ≤ u x)
    {y : V} (hxy : G.adj.Adj x y) : u y = u x := by
  obtain ⟨d, hd1, hd2⟩ := Harmonic.exists_dart_of_adj G hxy
  have hdmem : d ∈ G.outDarts x := (Harmonic.mem_outDarts G).mpr hd1
  have hnn : ∀ d' ∈ G.outDarts x, 0 ≤ u x - u (G.dtgt d') := fun d' hd' =>
    sub_nonneg.mpr (hmax _ (hnb d' hd'))
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hharm d hdmem
  rw [hd2] at hzero
  linarith

/-- **Maximum principle.** On a connected graph with infinitely many vertices, let `S` be finite, and let `u` be
harmonic at every vertex of `S \ B` whose darts all lead into `S`. If `u ≤ 0` on `S ∩ B`, then `u ≤ 0` on `S`. -/
theorem t15c_le_zero_of_lap_eq_zero [Infinite V] (hconn : G.adj.Connected) {S : Finset V} {B : Set V}
    {u : V → ℝ} (hnb : ∀ x ∈ S, x ∉ B → ∀ d ∈ G.outDarts x, G.dtgt d ∈ S)
    (hharm : ∀ x ∈ S, x ∉ B → lap G u x = 0) (hbd : ∀ x ∈ S, x ∈ B → u x ≤ 0) : ∀ x ∈ S, u x ≤ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x₀, hx₀S, hx₀⟩ := hcon
  have hne : S.Nonempty := ⟨x₀, hx₀S⟩
  obtain ⟨y₀, hy₀S, hy₀max⟩ := S.exists_max_image u hne
  set M := u y₀ with hM
  have hMpos : 0 < M := lt_of_lt_of_le hx₀ (hy₀max x₀ hx₀S)
  -- the maximum set is closed under adjacency
  have hclosed : ∀ x, x ∈ S → u x = M → ∀ y, G.adj.Adj x y → y ∈ S ∧ u y = M := by
    intro x hxS hxM y hxy
    have hxB : x ∉ B := fun hxB => by linarith [hbd x hxS hxB]
    obtain ⟨d, hd1, hd2⟩ := Harmonic.exists_dart_of_adj G hxy
    have hyS : y ∈ S := hd2 ▸ hnb x hxS hxB d ((Harmonic.mem_outDarts G).mpr hd1)
    refine ⟨hyS, ?_⟩
    rw [← hxM]
    exact t15c_eq_of_lap_eq_zero_of_isMax (hnb x hxS hxB) (hharm x hxS hxB)
      (fun y hy => hxM ▸ hy₀max y hy) hxy
  -- every vertex is in the maximum set
  have hwalk : ∀ (a v : V) (w : G.adj.Walk a v), a ∈ S → u a = M → v ∈ S ∧ u v = M := by
    intro a v w
    induction w with
    | nil => exact fun h1 h2 => ⟨h1, h2⟩
    | cons hadj _ ih =>
      intro h1 h2
      obtain ⟨h3, h4⟩ := hclosed _ h1 h2 _ hadj
      exact ih h3 h4
  have hall : ∀ v : V, v ∈ S := fun v => (hwalk y₀ v (hconn.preconnected y₀ v).some hy₀S rfl).1
  exact (Set.infinite_univ (α := V)) (S.finite_toSet.subset fun v _ => hall v)

/-! ### Hitting `V(∂D)` from `V(D)` -/

section Hitting

variable (H : CellularEmbedding G o)

/-- The vertices of `V(D) ∩ V(∂D)`, as a finite set. -/
def t15cBdry (D : Set ℂ) : Finset V := (vFin H D).filter fun w => (H.cell w ∩ frontier D).Nonempty

theorem t15c_mem_bdry {D : Set ℂ} (hDb : Bornology.IsBounded D) {w : V} :
    w ∈ t15cBdry H D ↔ (H.cell w ∩ D).Nonempty ∧ w ∈ verticesMeeting H.cell (frontier D) := by
  unfold t15cBdry
  rw [Finset.mem_filter, mem_vFin H hDb]
  rfl

variable {H}

/-- **From `x ∈ V(D)` the walk hits `V(∂D)` almost surely** (`D` open and bounded, `G` connected): it leaves the
finite set `V(D) \ V(∂D)`, and the first vertex outside it is in `V(∂D)`, or its cell misses `D`, in which case the
walk met `V(∂D)` earlier. -/
theorem t15c_walkLaw_hitTime_ne_top (hconn : G.adj.Connected) {D : Set ℂ} (hDo : IsOpen D)
    (hDb : Bornology.IsBounded D) {x : V} (hx : (H.cell x ∩ D).Nonempty) :
    G.walkLaw x {ω | hitTime (verticesMeeting H.cell (frontier D)) (G.vertexPath ω) ≠ ⊤} = 1 := by
  have : Countable V := countable_vertex H
  have : Countable G.State := countable_state G
  have : Infinite V := Infinite.infinite_of_cellularEmbedding H
  set U : Set V := (vFin H D : Set V) \ verticesMeeting H.cell (frontier D) with hU
  have hUfin : U.Finite := (vFin H D).finite_toSet.subset Set.sdiff_subset
  have hesc : ∀ y ∈ U, ∃ y', y' ∉ U ∧ G.adj.Reachable y y' := by
    intro y _
    obtain ⟨y', hy'⟩ := hUfin.infinite_compl.nonempty
    exact ⟨y', hy', hconn.preconnected y y'⟩
  have hexit := GMS3.walkLaw_hitTime_compl_ne_top G hUfin hesc x
  refine le_antisymm prob_le_one ?_
  rw [← hexit]
  refine measure_mono_ae ?_
  filter_upwards [walkLaw_compl_goodPath (G := G) x |> ae_iff.mpr] with ω hω hexitω
  obtain ⟨h0, hstep⟩ := hω
  have h0' : G.vertexPath ω 0 = x := by show G.stateVertex (ω 0) = x; rw [h0]; rfl
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hexitω
  have hnU : G.vertexPath ω n ∉ U := (hitTime_eq_coe_iff.mp hn.symm).1
  show hitTime (verticesMeeting H.cell (frontier D)) (G.vertexPath ω) ≠ ⊤
  refine ne_top_of_le_ne_top (ENat.natCast_ne_top n) ?_
  by_cases hB : G.vertexPath ω n ∈ verticesMeeting H.cell (frontier D)
  · exact hitTime_le_of_mem hB
  · have hnD : G.vertexPath ω n ∉ (vFin H D : Set V) := fun h => hnU ⟨h, hB⟩
    have hnsub : ¬ H.cell (G.vertexPath ω n) ⊆ D := by
      intro hsub
      apply hnD
      rw [Finset.mem_coe, mem_vFin H hDb]
      obtain ⟨q, hq⟩ := cell_nonempty H (G.vertexPath ω n)
      exact ⟨q, hq, hsub hq⟩
    exact t15c_hitTime_frontier_le hDo hstep (by rw [h0']; exact hx) hnsub

/-- **The first hit of `V(∂D)` lies in `V(D) ∩ V(∂D)`** almost surely. -/
theorem t15c_hitDist_firstHit_compl_eq_zero {D : Set ℂ} (hDo : IsOpen D) (hDb : Bornology.IsBounded D)
    {x : V} (hx : (H.cell x ∩ D).Nonempty) :
    hitDist G (verticesMeeting H.cell (frontier D)) x (t15cBdry H D : Set V)ᶜ = 0 := by
  have : Countable V := countable_vertex H
  have : Countable G.State := countable_state G
  refine measure_mono_null (fun ω hω => ?_) (walkLaw_compl_goodPath (G := G) x)
  intro hgood
  obtain ⟨h0, hstep⟩ := hgood
  have h0' : G.vertexPath ω 0 = x := by show G.stateVertex (ω 0) = x; rw [h0]; rfl
  obtain ⟨hT, hW⟩ := hω
  obtain ⟨T, hTeq⟩ := ENat.ne_top_iff_exists.mp hT
  rw [← hTeq, ENat.toNat_natCast] at hW
  apply hW
  rw [Finset.mem_coe, t15c_mem_bdry H hDb]
  exact ⟨t15c_firstHit_meets hDo hstep (by rw [h0']; exact hx) hTeq.symm,
    (hitTime_eq_coe_iff.mp hTeq.symm).1⟩

/-- The hitting distribution of `V(∂D)` from `x ∈ V(D)` has total mass one on `V(D) ∩ V(∂D)`. -/
theorem t15c_sum_hitDist_bdry (hconn : G.adj.Connected) {D : Set ℂ} (hDo : IsOpen D)
    (hDb : Bornology.IsBounded D) {x : V} (hx : (H.cell x ∩ D).Nonempty) :
    ∑ w ∈ t15cBdry H D, hitDist G (verticesMeeting H.cell (frontier D)) x {w} = 1 := by
  rw [← hitDist_eq_sum]
  have h := GMS3.hitDist_add_compl_eq_one G (t15c_walkLaw_hitTime_ne_top hconn hDo hDb hx)
    (t15cBdry H D : Set V)
  rwa [t15c_hitDist_firstHit_compl_eq_zero hDo hDb hx, add_zero] at h

/-- `toReal` form of the total mass. -/
theorem t15c_sum_toReal_hitDist_bdry (hconn : G.adj.Connected) {D : Set ℂ} (hDo : IsOpen D)
    (hDb : Bornology.IsBounded D) {x : V} (hx : (H.cell x ∩ D).Nonempty) :
    ∑ w ∈ t15cBdry H D, (hitDist G (verticesMeeting H.cell (frontier D)) x {w}).toReal = 1 := by
  rw [← ENNReal.toReal_sum fun w _ => GMS3.hitDist_ne_top G _ _ _, t15c_sum_hitDist_bdry hconn hDo hDb hx,
    ENNReal.toReal_one]

/-! ### The harmonic representation -/

/-- **Harmonic representation** (optional stopping, here via the maximum principle): if `f` is discrete harmonic on
`V(D) \ V(∂D)` (`D` open and bounded, `G` connected), then for `x ∈ V(D)`,
`f(x) = ∑_{w ∈ V(D) ∩ V(∂D)} P_x[X_{T_{V(∂D)}} = w] f(w)`. -/
theorem t15c_eq_sum_hitDist (hconn : G.adj.Connected) {D : Set ℂ} (hDo : IsOpen D)
    (hDb : Bornology.IsBounded D) (f : V → ℝ)
    (hharm : ∀ y ∈ vFin H D, ¬ (H.cell y ∩ frontier D).Nonempty → lap G f y = 0) {x : V}
    (hx : x ∈ vFin H D) :
    f x = ∑ w ∈ t15cBdry H D, (hitDist G (verticesMeeting H.cell (frontier D)) x {w}).toReal * f w := by
  have : Infinite V := Infinite.infinite_of_cellularEmbedding H
  set B : Set V := verticesMeeting H.cell (frontier D) with hB
  set g : V → ℝ := fun y => ∑ w ∈ t15cBdry H D, (hitDist G B y {w}).toReal * f w with hg
  -- `g` is harmonic off `B`
  have hgharm : ∀ y, y ∉ B → lap G g y = 0 := by
    intro y hy
    rw [hg, t15c_lap_sum_mul (h := fun w y => (hitDist G B y {w}).toReal)]
    refine Finset.sum_eq_zero fun w _ => ?_
    rw [GMS3.lap_hitDist G hy {w}, zero_mul]
  -- `g = f` on `V(D) ∩ V(∂D)`
  have hgbd : ∀ y ∈ t15cBdry H D, g y = f y := by
    intro y hy
    have hyB : y ∈ B := ((t15c_mem_bdry H hDb).mp hy).2
    rw [hg]
    simp only
    rw [Finset.sum_eq_single y]
    · rw [GMS3.hitDist_of_mem G hyB, Set.indicator_of_mem (Set.mem_singleton y), Pi.one_apply,
        ENNReal.toReal_one, one_mul]
    · intro w _ hwy
      rw [GMS3.hitDist_of_mem G hyB, Set.indicator_of_notMem (fun h => hwy (Set.mem_singleton_iff.mp h).symm),
        ENNReal.toReal_zero, zero_mul]
    · exact fun h => absurd hy h
  -- the neighbour condition
  have hnb : ∀ y ∈ vFin H D, y ∉ B → ∀ d ∈ G.outDarts y, G.dtgt d ∈ vFin H D := by
    intro y hy hyB d hd
    have hsub := cell_subset_of_inter_frontier_eq_empty H hDo ((mem_vFin H hDb).mp hy)
      (Set.not_nonempty_iff_eq_empty.mp hyB)
    exact dtgt_mem_vFin_of_subset H hDb hsub hy hd
  have hharmB : ∀ y ∈ vFin H D, y ∉ B → lap G f y = 0 := fun y hy hyB => hharm y hy hyB
  have hbdB : ∀ y ∈ vFin H D, y ∈ B → y ∈ t15cBdry H D := fun y hy hyB => by
    rw [t15c_mem_bdry H hDb]
    exact ⟨(mem_vFin H hDb).mp hy, hyB⟩
  -- `f - g ≤ 0` and `g - f ≤ 0` on `V(D)`
  have h1 := t15c_le_zero_of_lap_eq_zero hconn (S := vFin H D) (B := B) (u := fun y => f y - g y) hnb
    (fun y hy hyB => by rw [t15c_lap_sub, hharmB y hy hyB, hgharm y hyB, sub_zero])
    (fun y hy hyB => by rw [hgbd y (hbdB y hy hyB), sub_self])
  have h2 := t15c_le_zero_of_lap_eq_zero hconn (S := vFin H D) (B := B) (u := fun y => g y - f y) hnb
    (fun y hy hyB => by rw [t15c_lap_sub, hharmB y hy hyB, hgharm y hyB, sub_zero])
    (fun y hy hyB => by rw [hgbd y (hbdB y hy hyB), sub_self])
  have e1 := h1 x hx
  have e2 := h2 x hx
  show f x = g x
  linarith

/-! ### (3.31) from (3.38) -/

/-- The bad part of the hitting distribution is bounded by the hitting probability of `Wᶜ`. -/
theorem t15c_sum_bad_le {D : Set ℂ} (x : V) (W : Set V) :
    ∑ w ∈ (t15cBdry H D).filter (fun w => w ∉ W),
      (hitDist G (verticesMeeting H.cell (frontier D)) x {w}).toReal ≤
      (hitDist G (verticesMeeting H.cell (frontier D)) x Wᶜ).toReal := by
  rw [← ENNReal.toReal_sum fun w _ => GMS3.hitDist_ne_top G _ _ _, ← hitDist_eq_sum]
  refine ENNReal.toReal_mono (GMS3.hitDist_ne_top G _ _ _) (measure_mono fun ω hω => ⟨hω.1, ?_⟩)
  have h := hω.2
  rw [Finset.mem_coe, Finset.mem_filter] at h
  exact h.2

/-- **(3.31), lower bound, from (3.38)**. Let `G` be connected, `D` open and bounded, `f` discrete
harmonic on `V(D) \ V(∂D)` with `|f| ≤ M` on `V(D)`, and `x ∈ V(D)`. If the walk from `x` first hits `V(∂D)` outside
`W` with probability at most `q`, and `m ≤ f` on `V(D) ∩ V(∂D) ∩ W` with `m ≤ M`, then `m − 2 M q ≤ f(x)`. -/
theorem t15c_ge_of_hitDist_compl_le (hconn : G.adj.Connected) {D : Set ℂ} (hDo : IsOpen D)
    (hDb : Bornology.IsBounded D) (f : V → ℝ)
    (hharm : ∀ y ∈ vFin H D, ¬ (H.cell y ∩ frontier D).Nonempty → lap G f y = 0) {M : ℝ}
    (hM : ∀ y ∈ vFin H D, |f y| ≤ M) {x : V} (hx : x ∈ vFin H D) {W : Set V} {q : ℝ}
    (hq : hitDist G (verticesMeeting H.cell (frontier D)) x Wᶜ ≤ ENNReal.ofReal q) (hq0 : 0 ≤ q) {m : ℝ}
    (hm : ∀ y ∈ vFin H D, y ∈ verticesMeeting H.cell (frontier D) → y ∈ W → m ≤ f y) (hmM : m ≤ M) :
    m - 2 * M * q ≤ f x := by
  set B : Set V := verticesMeeting H.cell (frontier D) with hB
  set c : V → ℝ := fun w => (hitDist G B x {w}).toReal with hc
  have hc0 : ∀ w, 0 ≤ c w := fun w => ENNReal.toReal_nonneg
  have hxD : (H.cell x ∩ D).Nonempty := (mem_vFin H hDb).mp hx
  have hrep := t15c_eq_sum_hitDist hconn hDo hDb f hharm hx
  have hmass := t15c_sum_toReal_hitDist_bdry hconn hDo hDb hxD
  have hbad : ∑ w ∈ (t15cBdry H D).filter (fun w => w ∉ W), c w ≤ q :=
    (t15c_sum_bad_le x W).trans (ENNReal.toReal_le_of_le_ofReal hq0 hq)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x hx)
  -- `f(x) - m = ∑ c_w (f w - m)`
  have hdiff : f x - m = ∑ w ∈ t15cBdry H D, c w * (f w - m) := by
    have : ∑ w ∈ t15cBdry H D, c w * (f w - m) =
        ∑ w ∈ t15cBdry H D, c w * f w - m * ∑ w ∈ t15cBdry H D, c w := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun w _ => ?_
      ring
    rw [this, hmass, mul_one, ← hrep]
  have hsplit := Finset.sum_filter_add_sum_filter_not (t15cBdry H D) (fun w => w ∈ W)
    (fun w => c w * (f w - m))
  have hgood : 0 ≤ ∑ w ∈ (t15cBdry H D).filter (fun w => w ∈ W), c w * (f w - m) := by
    refine Finset.sum_nonneg fun w hw => ?_
    rw [Finset.mem_filter] at hw
    have hwb := (t15c_mem_bdry H hDb).mp hw.1
    have hwV : w ∈ vFin H D := (mem_vFin H hDb).mpr hwb.1
    exact mul_nonneg (hc0 w) (sub_nonneg.mpr (hm w hwV hwb.2 hw.2))
  have hbadterm : -(2 * M) * ∑ w ∈ (t15cBdry H D).filter (fun w => w ∉ W), c w ≤
      ∑ w ∈ (t15cBdry H D).filter (fun w => w ∉ W), c w * (f w - m) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun w hw => ?_
    rw [Finset.mem_filter] at hw
    have hwb := (t15c_mem_bdry H hDb).mp hw.1
    have hwV : w ∈ vFin H D := (mem_vFin H hDb).mpr hwb.1
    have hfw := neg_abs_le (f w) |>.trans' (neg_le_neg (hM w hwV))
    nlinarith [hc0 w]
  have hqb : -(2 * M) * q ≤ -(2 * M) * ∑ w ∈ (t15cBdry H D).filter (fun w => w ∉ W), c w :=
    mul_le_mul_of_nonpos_left hbad (by linarith)
  linarith

/-- **(3.31), upper bound, from (3.38)**: under the same hypotheses with `f ≤ m` on `V(D) ∩ V(∂D) ∩ W` and
`-M ≤ m`, `f(x) ≤ m + 2 M q`. -/
theorem t15c_le_of_hitDist_compl_le (hconn : G.adj.Connected) {D : Set ℂ} (hDo : IsOpen D)
    (hDb : Bornology.IsBounded D) (f : V → ℝ)
    (hharm : ∀ y ∈ vFin H D, ¬ (H.cell y ∩ frontier D).Nonempty → lap G f y = 0) {M : ℝ}
    (hM : ∀ y ∈ vFin H D, |f y| ≤ M) {x : V} (hx : x ∈ vFin H D) {W : Set V} {q : ℝ}
    (hq : hitDist G (verticesMeeting H.cell (frontier D)) x Wᶜ ≤ ENNReal.ofReal q) (hq0 : 0 ≤ q) {m : ℝ}
    (hm : ∀ y ∈ vFin H D, y ∈ verticesMeeting H.cell (frontier D) → y ∈ W → f y ≤ m) (hmM : -M ≤ m) :
    f x ≤ m + 2 * M * q := by
  have h := t15c_ge_of_hitDist_compl_le (H := H) hconn hDo hDb (fun y => -f y)
    (fun y hy hyB => by rw [t15c_lap_neg, hharm y hy hyB, neg_zero])
    (fun y hy => by rw [abs_neg]; exact hM y hy) hx hq hq0 (m := -m)
    (fun y hy hyB hyW => neg_le_neg (hm y hy hyB hyW)) (by linarith)
  linarith

end Hitting

end MatedCRTHarmonic.GMSMain
