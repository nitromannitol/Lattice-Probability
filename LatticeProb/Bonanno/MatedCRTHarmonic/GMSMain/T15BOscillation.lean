/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSMain.T15BOscillation at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.T15BMaxPrinciple
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS3.FirstVisit

/-!
# [18] Theorem 3.9: one-scale oscillation decay from (3.35)

Source: Gwynne–Miller–Sheffield, *Harmonic functions on mated-CRT maps* [18], Lemma 3.11 (display (3.35), `[18]`) and the proof of Theorem 3.9. [18] bounds the total-variation distance of hitting distributions with Lemma 3.10 (Wilson's
algorithm); here the same input (3.35) is used through the maximum principle instead, which needs no strong Markov property and no Wilson algorithm.

**One scale.** Let `u` be discrete harmonic at every vertex whose cell lies in the open disk `B_{2r}(z)` (cell meets
the disk, not its boundary circle), with `m ≤ u ≤ M` on `V(B̄_{2r}(z))`, and suppose that from every vertex of
`V(B_r(z))` the walk event of (3.35) (`DiscEvent`: the walk hits `V(∂B_{2r}(z))` and the vertices visited before
graph-disconnect `V(∂B_{r/2}(z))` from `V(∂B_{2r}(z))`) has probability `≥ p`. Then for `x, y ∈ V(B̄_{r/2}(z))`:
`(1 + p)(u(x) − u(y)) ≤ (1 − p)(M − m)` (`osc_step`), hence `u(x) − u(y) ≤ (1 − p)(M − m)` (`osc_step'`).

**Proof** (`lower_bound_of_disc`). From `x` the maximum-principle path (`exists_walk_le_of_lap_eq_zero`) leaves the
interior set `K`, so (crossing lemma) it contains a graph walk `q` from `V(∂B_{r/2}(z))` to `V(∂B_{2r}(z))` along which
`u ≥ u(x)`. On the event of (3.35) the walk visits `W = supp q` before `V(∂B_{2r}(z))`, and before that time it stays
in `K`; so `h(v) = P_v[the walk first enters B = W ∪ Kᶜ inside W] ≥ p` on `V(B_r(z))`. The function
`g = u − m − (u(x) − m)·h` is harmonic on `K \ W` (first-step equation `GMS3.hitDist_eq_avg`) and nonnegative at its
outer neighbours, so `g ≥ 0` (minimum principle): `u(v) ≥ m + p (u(x) − m)` on `V(B_r(z))`. Applied to `u` and `−u`,
these two bounds give the contraction.

The event `DiscEvent G J z r X` is, verbatim, the body of T15A's `Lemma311Event` (`GMSMain/T15ACore.lean`), so the two
agree by `Iff.rfl`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace MatedCRTHarmonic.GMSMain.T15B

open LFMultigraph Harmonic Markov

variable {V E : Type*} {G : LFMultigraph V E} {o : V}

/-- **The walk event of [18] (3.35)** at `(z, r)` for cells `J`: the walk hits `V(∂B_{2r}(z))` at a finite time `n`,
and the vertices visited strictly before `n` graph-disconnect `V(∂B_{r/2}(z))` from `V(∂B_{2r}(z))`.
Verbatim the body of T15A's `Lemma311Event` (`GMSMain/T15ACore.lean`). -/
def DiscEvent (G : LFMultigraph V E) (J : V → Set ℂ) (z : ℂ) (r : ℝ) (X : ℕ → V) : Prop :=
  ∃ n : ℕ, hitTime (verticesMeeting J (sphere z (2 * r))) X = n ∧
    G.Disconnects {y | ∃ m < n, X m = y} (verticesMeeting J (sphere z (r / 2)))
      (verticesMeeting J (sphere z (2 * r)))

variable (H : CellularEmbedding G o)

/-- **The lower bound of one scale.** Under the hypotheses of `osc_step` (with only the lower bound `m`), for every
`x ∈ V(B̄_{r/2}(z))` and every `v ∈ V(B_r(z))`: `m + p (u(x) − m) ≤ u(v)`. -/
theorem lower_bound_of_disc (hconn : G.adj.Connected) (u : V → ℝ) {z : ℂ} {r p m : ℝ} (hr : 0 < r)
    (hharm : ∀ v, (H.cell v ∩ ball z (2 * r)).Nonempty → ¬ (H.cell v ∩ sphere z (2 * r)).Nonempty →
      GMS3.lap G u v = 0)
    (hdisc : ∀ v ∈ verticesMeeting H.cell (ball z r),
      ENNReal.ofReal p ≤ G.walkLaw v {ω | DiscEvent G H.cell z r (G.vertexPath ω)})
    (hm : ∀ v ∈ verticesMeeting H.cell (closedBall z (2 * r)), m ≤ u v)
    {x : V} (hx : x ∈ verticesMeeting H.cell (closedBall z (r / 2))) :
    ∀ v ∈ verticesMeeting H.cell (ball z r), m + p * (u x - m) ≤ u v := by
  classical
  have : Countable V := GMS3.countable_vertex H
  have : Infinite V := infinite_vertex H
  set Out : Set V := verticesMeeting H.cell (sphere z (2 * r)) with hOut
  set K : Set V :=
    {v | (H.cell v ∩ ball z (2 * r)).Nonempty ∧ ¬ (H.cell v ∩ sphere z (2 * r)).Nonempty} with hKdef
  have hKfin : K.Finite :=
    (GMS3.finite_verticesMeeting H (isBounded_ball (x := z) (r := 2 * r))).subset fun v hv => hv.1
  have hKsub : ∀ v ∈ K, H.cell v ⊆ ball z (2 * r) := fun v hv =>
    cell_subset_ball_of_not_meet H hv.1 hv.2
  have hesc : ∀ {K₀ : Set V}, K₀.Finite → ∀ v ∈ K₀, ∃ w, w ∉ K₀ ∧ G.adj.Reachable v w :=
    fun hK₀ => exists_reachable_notMem G hconn hK₀
  -- the start `x` comes within `r/2` of `z`
  have hxpt : ∃ w ∈ H.cell x, dist w z ≤ r / 2 := by
    obtain ⟨w, hw, hwb⟩ := hx
    exact ⟨w, hw, mem_closedBall.mp hwb⟩
  have hxm : m ≤ u x := hm x (by
    obtain ⟨w, hw, hwb⟩ := hx
    exact ⟨w, hw, closedBall_subset_closedBall (by linarith) hwb⟩)
  /- Step 1: a graph walk `q` from `V(∂B_{r/2}(z))` to `V(∂B_{2r}(z))` along which `u ≥ u(x)`. -/
  obtain ⟨b, p₀, hbOut, hp₀⟩ :
      ∃ b, ∃ p₀ : G.adj.Walk x b, b ∈ Out ∧ ∀ y ∈ p₀.support, u x ≤ u y := by
    obtain ⟨w, hwK, p, hp⟩ :=
      exists_walk_le_of_lap_eq_zero G hKfin (fun v hv => hharm v hv.1 hv.2) (hesc hKfin) x
    have hfar : ∃ w' ∈ H.cell w, 2 * r ≤ dist w' z := by
      by_contra hcon
      push Not at hcon
      apply hwK
      obtain ⟨c, hc⟩ := GMS3.cell_nonempty H w
      refine ⟨⟨c, hc, mem_ball.mpr (hcon c hc)⟩, ?_⟩
      rintro ⟨c', hc', hc's⟩
      have h1 := hcon c' hc'
      rw [mem_sphere] at hc's
      linarith
    obtain ⟨w₀, hw₀, hw₀z⟩ := hxpt
    obtain ⟨b, hbp, hbs⟩ := exists_mem_support_sphere H p ⟨w₀, hw₀, by linarith⟩ hfar
    exact ⟨b, p.takeUntil b hbp, hbs, fun y hy =>
      hp y (SimpleGraph.Walk.support_takeUntil_subset_support p hbp hy)⟩
  have hbfar : ∃ w' ∈ H.cell b, r / 2 ≤ dist w' z := by
    obtain ⟨c, hc, hcs⟩ := hbOut
    exact ⟨c, hc, by rw [mem_sphere.mp hcs]; linarith⟩
  obtain ⟨a, hap, has⟩ := exists_mem_support_sphere H p₀ hxpt hbfar
  set q : G.adj.Walk a b := p₀.dropUntil a hap with hqdef
  have hq : ∀ y ∈ q.support, u x ≤ u y := fun y hy =>
    hp₀ y (SimpleGraph.Walk.support_dropUntil_subset_support p₀ hap hy)
  /- Step 2: the hitting probability `h` of `W = supp q` before `Kᶜ`. -/
  set W : Set V := {y | y ∈ q.support} with hWdef
  set B : Set V := W ∪ Kᶜ with hBdef
  set h : V → ℝ := fun v => (HarmonicInfinity.hitDist G B v W).toReal with hhdef
  have hh_W : ∀ v ∈ W, h v = 1 := by
    intro v hv
    simp only [hhdef, GMS3.hitDist_of_mem G (show v ∈ B from Or.inl hv) W, Set.indicator_of_mem hv,
      Pi.one_apply, ENNReal.toReal_one]
  have hh_notW : ∀ v ∈ B, v ∉ W → h v = 0 := by
    intro v hvB hv
    simp only [hhdef, GMS3.hitDist_of_mem G hvB W, Set.indicator_of_notMem hv, ENNReal.toReal_zero]
  have hlap_h : ∀ v, v ∉ B → GMS3.lap G h v = 0 := by
    intro v hv
    have havg := GMS3.hitDist_eq_avg G hv W
    have hdeg : (G.deg v : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Harmonic.deg_ne_zero G v)
    rw [GMS3.lap_eq]
    simp only [hhdef]
    rw [havg, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_sum (fun d _ => GMS3.hitDist_ne_top G B W _)]
    field_simp
    ring
  /- Step 3: `g = u − m − (u(x) − m) h ≥ 0` on `K \ W` (minimum principle). -/
  set c : ℝ := u x - m with hcdef
  have hc0 : 0 ≤ c := by rw [hcdef]; linarith
  set g : V → ℝ := fun v => u v - m - c * h v with hgdef
  have hgW : ∀ v ∈ W, 0 ≤ g v := by
    intro v hv
    simp only [hgdef, hh_W v hv, mul_one, hcdef]
    linarith [hq v hv]
  set K' : Set V := {v | v ∈ K ∧ v ∉ W} with hK'def
  have hK'fin : K'.Finite := hKfin.subset fun v (hv : v ∈ K') => hv.1
  have hgK' : ∀ v ∈ K', 0 ≤ g v := by
    refine nonneg_of_lap_eq_zero G hK'fin ?_ ?_ (hesc hK'fin)
    · intro v hv
      have hvB : v ∉ B := by
        rintro (hvW | hvK)
        · exact hv.2 hvW
        · exact hvK hv.1
      rw [hgdef, lap_sub_const_sub_mul, hharm v hv.1.1 hv.1.2, hlap_h v hvB, mul_zero, sub_zero]
    · intro v hv w hvw hwK'
      by_cases hwW : w ∈ W
      · exact hgW w hwW
      · have hwK : w ∉ K := fun hwK => hwK' ⟨hwK, hwW⟩
        simp only [hgdef, hh_notW w (Or.inr hwK) hwW, mul_zero, sub_zero]
        have hwball : w ∈ verticesMeeting H.cell (closedBall z (2 * r)) := by
          obtain ⟨c', hc'v, hc'w⟩ := H.inter_of_adj v w hvw
          exact ⟨c', hc'w, ball_subset_closedBall (hKsub v hv.1 hc'v)⟩
        linarith [hm w hwball]
  have hgv : ∀ v ∈ verticesMeeting H.cell (ball z r), 0 ≤ g v := by
    intro v hv
    by_cases hvW : v ∈ W
    · exact hgW v hvW
    · by_cases hvK : v ∈ K
      · exact hgK' v ⟨hvK, hvW⟩
      · simp only [hgdef, hh_notW v (Or.inr hvK) hvW, mul_zero, sub_zero]
        have hvball : v ∈ verticesMeeting H.cell (closedBall z (2 * r)) := by
          obtain ⟨c', hc'v, hc'b⟩ := hv
          exact ⟨c', hc'v, ball_subset_closedBall (ball_subset_ball (by linarith) hc'b)⟩
        linarith [hm v hvball]
  /- Step 4: on the event of (3.35) the walk first enters `B` inside `W`, so `p ≤ h(v)`. -/
  have hph : ∀ v ∈ verticesMeeting H.cell (ball z r), p ≤ h v := by
    intro v hv
    have hle : G.walkLaw v {ω | DiscEvent G H.cell z r (G.vertexPath ω)} ≤
        HarmonicInfinity.hitDist G B v W := by
      unfold HarmonicInfinity.hitDist
      refine measure_mono_ae ?_
      filter_upwards [GMS3.ae_isStepPath G hconn v] with ω hω hev
      obtain ⟨h0, hstep⟩ := hω
      obtain ⟨n, hn, hdis⟩ := hev
      obtain ⟨y, hyq, m', hm'n, hXm'⟩ := hdis a has b hbOut q
      -- before time `n` the walk stays in `K`
      have hXK : ∀ j, j < n → G.vertexPath ω j ∈ K := by
        intro j
        induction j with
        | zero =>
          intro hj
          have hX0 : G.vertexPath ω 0 = v := h0
          refine ⟨?_, fun hmeet => ?_⟩
          · rw [hX0]
            obtain ⟨c', hc'v, hc'b⟩ := hv
            exact ⟨c', hc'v, ball_subset_ball (by linarith) hc'b⟩
          · exact notMem_of_lt_hitTime (A := Out) (by rw [hn]; exact_mod_cast hj) hmeet
        | succ j ih =>
          intro hj
          have hjK := ih (by omega)
          refine ⟨?_, fun hmeet => ?_⟩
          · rcases hstep n j (by omega) with heq | hadj
            · rw [heq]
              exact hjK.1
            · obtain ⟨c', hc'j, hc'j1⟩ := H.inter_of_adj _ _ hadj
              exact ⟨c', hc'j1, hKsub _ hjK hc'j⟩
          · exact notMem_of_lt_hitTime (A := Out) (by rw [hn]; exact_mod_cast hj) hmeet
      have hXB : G.vertexPath ω m' ∈ B := Or.inl (by rw [hXm']; exact hyq)
      have hTB : hitTime B (G.vertexPath ω) ≠ ⊤ :=
        ne_top_of_le_ne_top (ENat.natCast_ne_top m') (hitTime_le_of_mem hXB)
      have hkle : (hitTime B (G.vertexPath ω)).toNat ≤ m' := by
        have h1 := hitTime_le_of_mem hXB
        rw [← coe_toNat_hitTime hTB] at h1
        exact_mod_cast h1
      have hkB : G.vertexPath ω (hitTime B (G.vertexPath ω)).toNat ∈ B :=
        stopState_hitTime_mem hTB
      have hkK := hXK (hitTime B (G.vertexPath ω)).toNat (by omega)
      refine ⟨hTB, ?_⟩
      rcases hkB with hW | hK
      · exact hW
      · exact absurd hkK hK
    rcases le_or_gt p 0 with hp0 | hp0
    · exact hp0.trans ENNReal.toReal_nonneg
    · exact (ENNReal.ofReal_le_iff_le_toReal (GMS3.hitDist_ne_top G B W v)).mp
        ((hdisc v hv).trans hle)
  /- Step 5: conclusion. -/
  intro v hv
  have h1 := hgv v hv
  have h2 := hph v hv
  simp only [hgdef] at h1
  have h3 : p * c ≤ h v * c := mul_le_mul_of_nonneg_right h2 hc0
  nlinarith

/-- **One-scale oscillation decay** ([18] (3.35) through the maximum principle). Let `u` be discrete harmonic at
every vertex whose cell meets `B_{2r}(z)` but not `∂B_{2r}(z)`, with `m ≤ u ≤ M` on `V(B̄_{2r}(z))`, and let the walk
event of (3.35) have probability `≥ p` from every vertex of `V(B_r(z))`. Then for `x, y ∈ V(B̄_{r/2}(z))`:
`(1 + p)(u(x) − u(y)) ≤ (1 − p)(M − m)`. -/
theorem osc_step (hconn : G.adj.Connected) (u : V → ℝ) {z : ℂ} {r p m M : ℝ} (hr : 0 < r)
    (hharm : ∀ v, (H.cell v ∩ ball z (2 * r)).Nonempty → ¬ (H.cell v ∩ sphere z (2 * r)).Nonempty →
      GMS3.lap G u v = 0)
    (hdisc : ∀ v ∈ verticesMeeting H.cell (ball z r),
      ENNReal.ofReal p ≤ G.walkLaw v {ω | DiscEvent G H.cell z r (G.vertexPath ω)})
    (hbd : ∀ v ∈ verticesMeeting H.cell (closedBall z (2 * r)), m ≤ u v ∧ u v ≤ M)
    {x y : V} (hx : x ∈ verticesMeeting H.cell (closedBall z (r / 2)))
    (hy : y ∈ verticesMeeting H.cell (closedBall z (r / 2))) :
    (1 + p) * (u x - u y) ≤ (1 - p) * (M - m) := by
  have hsub : ∀ w ∈ verticesMeeting H.cell (closedBall z (r / 2)), w ∈ verticesMeeting H.cell (ball z r) := by
    rintro w ⟨c, hc, hcb⟩
    exact ⟨c, hc, closedBall_subset_ball (by linarith) hcb⟩
  -- lower bound for `u` at `y`, from `x`
  have h1 := lower_bound_of_disc H hconn u hr hharm hdisc (fun v hv => (hbd v hv).1) hx y (hsub y hy)
  -- lower bound for `−u` at `x`, from `y`
  have h2 := lower_bound_of_disc H hconn (fun w => -u w) (m := -M) hr
    (fun v hv1 hv2 => by rw [lap_neg, hharm v hv1 hv2, neg_zero]) hdisc
    (fun v hv => neg_le_neg (hbd v hv).2) hy x (hsub x hx)
  nlinarith

/-- **One-scale oscillation decay, contraction form**: under the hypotheses of `osc_step` and `p ≤ 1`,
`u(x) − u(y) ≤ (1 − p)(M − m)` for `x, y ∈ V(B̄_{r/2}(z))`. -/
theorem osc_step' (hconn : G.adj.Connected) (u : V → ℝ) {z : ℂ} {r p m M : ℝ} (hr : 0 < r)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hharm : ∀ v, (H.cell v ∩ ball z (2 * r)).Nonempty → ¬ (H.cell v ∩ sphere z (2 * r)).Nonempty →
      GMS3.lap G u v = 0)
    (hdisc : ∀ v ∈ verticesMeeting H.cell (ball z r),
      ENNReal.ofReal p ≤ G.walkLaw v {ω | DiscEvent G H.cell z r (G.vertexPath ω)})
    (hbd : ∀ v ∈ verticesMeeting H.cell (closedBall z (2 * r)), m ≤ u v ∧ u v ≤ M)
    {x y : V} (hx : x ∈ verticesMeeting H.cell (closedBall z (r / 2)))
    (hy : y ∈ verticesMeeting H.cell (closedBall z (r / 2))) :
    u x - u y ≤ (1 - p) * (M - m) := by
  have h := osc_step H hconn u hr hharm hdisc hbd hx hy
  have hMm : m ≤ M := by
    obtain ⟨c, hc, hcb⟩ := hx
    have := hbd x ⟨c, hc, closedBall_subset_closedBall (by linarith) hcb⟩
    linarith [this.1, this.2]
  have hR : 0 ≤ (1 - p) * (M - m) := mul_nonneg (by linarith) (by linarith)
  rcases le_or_gt (u x - u y) 0 with hneg | hpos
  · linarith
  · nlinarith

end MatedCRTHarmonic.GMSMain.T15B
