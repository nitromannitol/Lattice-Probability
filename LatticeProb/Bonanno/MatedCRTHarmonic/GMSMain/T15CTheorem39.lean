/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSMain.T15CTheorem39 at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.T15CBoundary
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.T15ACore

/-!
# [18] Theorem 3.9, boundary continuity estimate (3.31)

Source: [18] , Theorem 3.9, (3.31), proved at
`[18]` through (3.38). The input is [18] (3.35) in the exact shape
(`GMSMain/T15ACore.lean`: `T15A.Lemma311Event`, `T15A.Lemma311Holds`, `T15A.Lemma311Bad`).

**Erratum (the floor `ε^β`).** (3.38) and (3.31) as printed use `dist(η(x), ∂D)` alone. (3.35) is only available at
radii `r ≥ ε^β`, so the scales `r = e^{−k}` of `[18]` must stop at `ε^β`, and the error term becomes
`A ‖f‖ (t / (dist(η(x), ∂D) ∨ ε^β))^{−ξ}`. The printed form is false in general: fix the environment, let `D` be
`B_ρ(0)` minus a slit whose tip approaches `η(x)` without entering `H_x`, take boundary data `0` on
`V(∂D ∩ B_t(η(x)))` and `1` elsewhere. Then `f(x)` stays bounded below by the positive probability that the walk
escapes the slit's cells and first hits `V(∂D)` far away, while `A (t / dist)^{−ξ} → 0`. The floor changes only
exponents downstream ((3.33), Theorem 1.5).

Also used, as [18] does implicitly: (3.35) at an ambient radius `ρ' > ρ`, so that the scales around `η(x)` stay
inside the ball where (3.35) holds; (3.31) is proved for **every** point `z` of the cell `H_x` (in particular
`z = η(x)`); `‖f‖_∞` is any bound `M` for `|f|` on `V(D)`; and [18]'s simple connectivity of `D` is used only through
"`ℂ \ D` is connected", which is the hypothesis here (`IsPreconnected Dᶜ`; `D` need not be connected).

* `t15cXi p = log((1 − p)⁻¹) / log 4`, the exponent from `p` (scale ratio `4`).
* `t15c_hitDist_compl_le_rpow` (**(3.38), one point**): if (3.35) holds at `z` for all `r ∈ [r_lo, R]`, then
  `P_x[X_{T_{V(∂D)}} ∉ V(D) ∩ V(∂D ∩ B_t(z))] ≤ (max(2 dist(z, ∂D), r_lo) / min(R, t/2))^ξ`.
* `t15c_hitDist_compl_le_of_lemma311Holds` (**(3.38), [18]'s form**, on T15A's event `Lemma311Holds H ε ρ' β p`):
  for `D ⊆ B_ρ(0)`, `ρ < ρ'`, every `t > 0`,
  `P_x[...] ≤ κ^ξ (t / max(dist(z, ∂D), ε^β))^{−ξ}`, `κ = 4 (3ρ + ρ') / (ρ' − ρ)`; and
  `t15c_hitDist_ge_of_lemma311Holds`, the printed form `P_x[first hit in V(D) ∩ V(∂D ∩ B_t(z))] ≥ 1 − κ^ξ (…)^{−ξ}`.
* `T15CBoundaryEstimate H ε ρ β ξ A` (the conclusion (3.31) on one environment) and
  `t15c_boundaryEstimate_of_lemma311Holds` (**(3.31), deterministic on the good event**).
* `t15c_boundaryEstimateBad_of_lemma311Bad` (**(3.31) with probability `1 − O(ε^α)`**) for a random cell family
  with connected graphs and (LC) almost surely, from T15A's `Lemma311Bad F ρ'`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal Classical

namespace MatedCRTHarmonic.GMSMain

open Markov LFMultigraph GoodScales HarmonicInfinity GMS3

variable {V E : Type*} {G : LFMultigraph V E} {o : V}

/-! ### From T15A's event to the trace form -/

/-- T15A's walk event of (3.35) (hit at a finite time `n`, trace before `n` disconnects) implies the trace form used
here (`walkTrace`). -/
theorem t15c_disconnects_walkTrace_of_lemma311Event {J : V → Set ℂ} {z : ℂ} {r : ℝ} {ω : ℕ → G.State}
    (h : T15A.Lemma311Event G J z r (G.vertexPath ω)) :
    G.Disconnects (walkTrace G (verticesMeeting J (sphere z (2 * r))) ω)
      (verticesMeeting J (sphere z (r / 2))) (verticesMeeting J (sphere z (2 * r))) := by
  obtain ⟨n, hn, hdisc⟩ := h
  intro a ha c hc w
  obtain ⟨y, hyw, m, hm, hmy⟩ := hdisc a ha c hc w
  exact ⟨y, hyw, m, by rw [hn]; exact_mod_cast hm, hmy⟩

/-- T15A's (3.35) at one `(z, r)` gives `t15cDisconnectionAt`. -/
theorem t15c_disconnectionAt_of_lemma311 {H : CellularEmbedding G o} {p : ℝ} {z : ℂ} {r : ℝ}
    (h : ∀ y ∈ verticesMeeting H.cell (ball z r),
      ENNReal.ofReal p ≤ G.walkLaw y {ξ | T15A.Lemma311Event G H.cell z r (G.vertexPath ξ)}) :
    t15cDisconnectionAt G H p z r := fun y hy =>
  (h y hy).trans (measure_mono fun _ hω => t15c_disconnects_walkTrace_of_lemma311Event hω)

/-! ### The exponent -/

/-- The exponent of (3.38) from the success probability `p` of (3.35), for scales growing by the factor `4`. -/
def t15cXi (p : ℝ) : ℝ := Real.log (1 - p)⁻¹ / Real.log 4

theorem t15cXi_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : 0 < t15cXi p := by
  unfold t15cXi
  have h1 : 1 < (1 - p)⁻¹ := by
    rw [lt_inv_comm₀ one_pos (by linarith), inv_one]
    linarith
  exact div_pos (Real.log_pos h1) (Real.log_pos (by norm_num))

/-- **Counting scales.** For `0 < p < 1` and `0 < r₀ ≤ s`, with `K = ⌊log₄(s / r₀)⌋₊ + 1`: every radius `4^j r₀`,
`j < K`, is `≤ s`, and `(1 − p)^K ≤ (r₀ / s)^ξ`. -/
theorem t15c_scales {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {r₀ s : ℝ} (hr₀ : 0 < r₀) (hrs : r₀ ≤ s) :
    (∀ j < ⌊Real.logb 4 (s / r₀)⌋₊ + 1, (4 : ℝ) ^ j * r₀ ≤ s) ∧
      (1 - p) ^ (⌊Real.logb 4 (s / r₀)⌋₊ + 1) ≤ (r₀ / s) ^ t15cXi p := by
  have hs : 0 < s := lt_of_lt_of_le hr₀ hrs
  have hq : 1 ≤ s / r₀ := (one_le_div hr₀).mpr hrs
  set L := Real.logb 4 (s / r₀) with hL
  have hL0 : 0 ≤ L := Real.logb_nonneg (by norm_num) hq
  refine ⟨fun j hj => ?_, ?_⟩
  · have hjL : j ≤ ⌊L⌋₊ := by omega
    have h1 : (4 : ℝ) ^ j ≤ (4 : ℝ) ^ ⌊L⌋₊ := pow_le_pow_right₀ (by norm_num) hjL
    have h2 : (4 : ℝ) ^ (⌊L⌋₊ : ℝ) ≤ (4 : ℝ) ^ L :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.floor_le hL0)
    have h3 : (4 : ℝ) ^ L = s / r₀ := Real.rpow_logb (by norm_num) (by norm_num) (by positivity)
    rw [Real.rpow_natCast] at h2
    have h4 : (4 : ℝ) ^ j ≤ s / r₀ := by linarith
    rwa [le_div_iff₀ hr₀] at h4
  · have hp' : 0 < 1 - p := by linarith
    have hK : L ≤ ((⌊L⌋₊ + 1 : ℕ) : ℝ) := by
      push_cast
      exact (Nat.lt_floor_add_one L).le
    calc (1 - p) ^ (⌊L⌋₊ + 1) = (1 - p) ^ (((⌊L⌋₊ + 1 : ℕ) : ℝ)) := (Real.rpow_natCast _ _).symm
      _ ≤ (1 - p) ^ L := Real.rpow_le_rpow_of_exponent_ge hp' (by linarith) hK
      _ = (r₀ / s) ^ t15cXi p := by
          rw [Real.rpow_def_of_pos hp', Real.rpow_def_of_pos (by positivity), hL, Real.logb, t15cXi,
            Real.log_inv, Real.log_div hr₀.ne' hs.ne', Real.log_div hs.ne' hr₀.ne']
          congr 1
          ring

/-! ### Geometry of the frontier -/

/-- A nonempty bounded open set in `ℂ` has nonempty frontier. -/
theorem t15c_frontier_nonempty {D : Set ℂ} (hDb : Bornology.IsBounded D) (hne : D.Nonempty) :
    (frontier D).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hclopen : IsClopen D := isClopen_iff_frontier_eq_empty.mpr h
  rcases isClopen_iff.mp hclopen with h1 | h1
  · exact hne.ne_empty h1
  · rw [h1] at hDb
    exact NormedSpace.unbounded_univ ℝ ℂ hDb

/-- A point of `∂D` realizing `dist(z, ∂D)`; it lies outside the open set `D`. -/
theorem t15c_exists_frontier_infDist {D : Set ℂ} (hDo : IsOpen D) (hfr : (frontier D).Nonempty) (z : ℂ) :
    ∃ w ∉ D, dist w z = infDist z (frontier D) := by
  obtain ⟨w, hw, hwd⟩ := isClosed_frontier.exists_infDist_eq_dist hfr z
  refine ⟨w, fun hwD => ?_, by rw [hwd, dist_comm]⟩
  rw [hDo.frontier_eq] at hw
  exact hw.2 hwD

/-- If `∂D ⊆ B_t(z)`, the walk from `x ∈ V(D)` first hits `V(∂D)` inside `V(D) ∩ V(∂D ∩ B_t(z))` almost surely. -/
theorem t15c_hitDist_compl_eq_zero_of_frontier_subset {H : CellularEmbedding G o} {D : Set ℂ}
    (hDo : IsOpen D) (hDb : Bornology.IsBounded D) {x : V} (hx : (H.cell x ∩ D).Nonempty) {z : ℂ} {t : ℝ}
    (hsub : frontier D ⊆ ball z t) :
    hitDist G (verticesMeeting H.cell (frontier D)) x
      (verticesMeeting H.cell D ∩ verticesMeeting H.cell (frontier D ∩ ball z t))ᶜ = 0 := by
  refine measure_mono_null ?_ (t15c_hitDist_firstHit_compl_eq_zero (H := H) hDo hDb hx)
  intro ω hω
  obtain ⟨hT, hW⟩ := hω
  refine ⟨hT, fun hb => hW ?_⟩
  rw [Finset.mem_coe, t15c_mem_bdry H hDb] at hb
  obtain ⟨hbD, q, hq, hqf⟩ := hb
  exact ⟨hbD, q, hq, hqf, hsub hqf⟩

/-! ### (3.38) at one point, with the floor `r_lo` -/

/-- **(3.38) at one point** (`[18]`, corrected floor). Let `G` be connected, `H` satisfy (LC), `D` open and
bounded with `ℂ \ D` preconnected, `H_x ∩ D ≠ ∅`, `z ∈ H_x`, `0 < p < 1`, `0 < r_lo`, `0 < R`, `0 < t`. If (3.35)
(T15A's event) holds at `z` with probability `≥ p` for every radius `r ∈ [r_lo, R]`, then
`P_x[X_{T_{V(∂D)}} ∉ V(D) ∩ V(∂D ∩ B_t(z))] ≤ (max(2 dist(z, ∂D), r_lo) / min(R, t/2))^ξ`, `ξ = t15cXi p`. -/
theorem t15c_hitDist_compl_le_rpow {H : CellularEmbedding G o} (hLC : H.PointConnected) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) {D : Set ℂ} (hDo : IsOpen D) (hDb : Bornology.IsBounded D)
    (hDc : IsPreconnected Dᶜ) {x : V} (hxD : (H.cell x ∩ D).Nonempty) {z : ℂ} (hz : z ∈ H.cell x)
    {rlo R t : ℝ} (hrlo : 0 < rlo) (hR : 0 < R) (ht : 0 < t)
    (h35 : ∀ r, rlo ≤ r → r ≤ R → ∀ y ∈ verticesMeeting H.cell (ball z r),
      ENNReal.ofReal p ≤ G.walkLaw y {ξ | T15A.Lemma311Event G H.cell z r (G.vertexPath ξ)}) :
    hitDist G (verticesMeeting H.cell (frontier D)) x
      (verticesMeeting H.cell D ∩ verticesMeeting H.cell (frontier D ∩ ball z t))ᶜ ≤
      ENNReal.ofReal ((max (2 * infDist z (frontier D)) rlo / min R (t / 2)) ^ t15cXi p) := by
  set r₀ := max (2 * infDist z (frontier D)) rlo with hr₀def
  set s := min R (t / 2) with hsdef
  have hr₀ : 0 < r₀ := lt_of_lt_of_le hrlo (le_max_right _ _)
  have hs : 0 < s := lt_min hR (by linarith)
  have hξ := t15cXi_pos hp0 hp1
  rcases lt_or_ge s r₀ with hlt | hle
  · -- no scale fits: the bound is at least one
    have h1 : 1 ≤ (r₀ / s) ^ t15cXi p :=
      Real.one_le_rpow ((one_le_div hs).mpr hlt.le) hξ.le
    calc hitDist G (verticesMeeting H.cell (frontier D)) x _ ≤ 1 := GMS3.hitDist_le_one G _ _ _
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ ENNReal.ofReal ((r₀ / s) ^ t15cXi p) := ENNReal.ofReal_le_ofReal h1
  · obtain ⟨hscale, hpow⟩ := t15c_scales hp0 hp1 hr₀ hle
    have hfr : (frontier D).Nonempty := t15c_frontier_nonempty hDb (hxD.mono Set.inter_subset_right)
    obtain ⟨w₀, hw₀, hw₀d⟩ := t15c_exists_frontier_infDist hDo hfr z
    refine (t15c_hitDist_compl_le_of_disconnectionAt hLC hp0.le hp1.le hDo hDb hDc hxD hz hr₀ hw₀
      (by rw [hw₀d]; linarith [le_max_left (2 * infDist z (frontier D)) rlo]) (t := t)
      (K := ⌊Real.logb 4 (s / r₀)⌋₊ + 1) (fun j hj => ?_) (fun j hj => ?_)).trans
      (ENNReal.ofReal_le_ofReal hpow)
    · have := hscale j hj
      have : s ≤ t / 2 := min_le_right _ _
      linarith
    · refine t15c_disconnectionAt_of_lemma311 (h35 _ ?_ ?_)
      · exact (le_max_right _ _).trans (le_mul_of_one_le_left hr₀.le (one_le_pow₀ (by norm_num)))
      · exact (hscale j hj).trans (min_le_left _ _)

/-! ### (3.38) in [18]'s form on T15A's event -/

/-- The constant of (3.38) in [18]'s form: `κ = 4 (3ρ + ρ') / (ρ' − ρ)`. -/
def t15cKappa (ρ ρ' : ℝ) : ℝ := 4 * (3 * ρ + ρ') / (ρ' - ρ)

theorem t15cKappa_pos {ρ ρ' : ℝ} (hρ : 0 < ρ) (hρρ' : ρ < ρ') : 0 < t15cKappa ρ ρ' := by
  unfold t15cKappa
  have : 0 < ρ' - ρ := by linarith
  have : 0 < 3 * ρ + ρ' := by linarith
  positivity

/-- `κ^ξ (t/d)^{−ξ} = (κ d / t)^ξ`. -/
theorem t15c_rpow_form {κ d t ξ : ℝ} (hκ : 0 ≤ κ) (hd : 0 < d) (ht : 0 < t) :
    κ ^ ξ * (t / d) ^ (-ξ) = (κ * d / t) ^ ξ := by
  rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity), inv_div,
    ← Real.mul_rpow hκ (by positivity), mul_div_assoc]

/-- The frontier of a subset of `B_ρ(0)` lies in the closed ball. -/
theorem t15c_frontier_subset_closedBall {D : Set ℂ} {ρ : ℝ} (hDρ : D ⊆ ball (0 : ℂ) ρ) :
    frontier D ⊆ closedBall (0 : ℂ) ρ :=
  frontier_subset_closure.trans ((closure_mono hDρ).trans closure_ball_subset_closedBall)

/-- **(3.38) in [18]'s form** (`[18]`, with the floor `ε^β`), on T15A's event `Lemma311Holds H ε ρ' β p`
(**[18] (3.35) at ambient radius `ρ' > ρ`**). Let `G` be connected, `H` satisfy (LC), `0 < p < 1`, `D ⊆ B_ρ(0)` open
with `ℂ \ D` preconnected, `x ∈ V(D)`, `z ∈ H_x`, `t > 0`. Then the walk from `x` first hits `V(∂D)` outside
`V(D) ∩ V(∂D ∩ B_t(z))` with probability at most `κ^ξ (t / max(dist(z, ∂D), ε^β))^{−ξ}`. -/
theorem t15c_hitDist_compl_le_of_lemma311Holds {H : CellularEmbedding G o} (hLC : H.PointConnected)
    {ε ρ ρ' β p : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) (hρρ' : ρ < ρ') (hp0 : 0 < p) (hp1 : p < 1)
    (h311 : T15A.Lemma311Holds H ε ρ' β p) {D : Set ℂ} (hDo : IsOpen D) (hDρ : D ⊆ ball (0 : ℂ) ρ)
    (hDc : IsPreconnected Dᶜ) {x : V} (hxD : (H.cell x ∩ D).Nonempty) {z : ℂ} (hz : z ∈ H.cell x) {t : ℝ}
    (ht : 0 < t) :
    hitDist G (verticesMeeting H.cell (frontier D)) x
      (verticesMeeting H.cell D ∩ verticesMeeting H.cell (frontier D ∩ ball z t))ᶜ ≤
      ENNReal.ofReal (t15cKappa ρ ρ' ^ t15cXi p *
        (t / max (infDist z (frontier D)) (ε ^ β)) ^ (-t15cXi p)) := by
  have hDb : Bornology.IsBounded D := Metric.isBounded_ball.subset hDρ
  set d := infDist z (frontier D) with hd
  have hεβ : 0 < ε ^ β := Real.rpow_pos_of_pos hε β
  set d' := max d (ε ^ β) with hd'
  have hd'0 : 0 < d' := lt_of_lt_of_le hεβ (le_max_right _ _)
  have hd0 : 0 ≤ d := infDist_nonneg
  set κ := t15cKappa ρ ρ' with hκ
  have hκ0 : 0 < κ := t15cKappa_pos hρ hρρ'
  have hξ := t15cXi_pos hp0 hp1
  rw [t15c_rpow_form hκ0.le hd'0 ht]
  have hfr := t15c_frontier_subset_closedBall hDρ
  have hfrne : (frontier D).Nonempty := t15c_frontier_nonempty hDb (hxD.mono Set.inter_subset_right)
  have hρ'ρ : 0 < ρ' - ρ := by linarith
  rcases lt_or_ge (‖z‖ + ρ) t with hfar | hnear
  · -- `∂D ⊆ B_t(z)`: no bad first hit
    rw [t15c_hitDist_compl_eq_zero_of_frontier_subset hDo hDb hxD (fun w hw => ?_)]
    · exact zero_le
    · rw [mem_ball, dist_eq_norm]
      have := mem_closedBall_zero_iff.mp (hfr hw)
      linarith [norm_sub_le w z]
  · rcases le_or_gt ((ρ + ρ') / 2) ‖z‖ with hzfar | hzin
    · -- `z` far from `B_ρ(0)`: the bound is at least one
      have hdz : ‖z‖ - ρ ≤ d := by
        rw [hd, le_infDist hfrne]
        intro w hw
        have := mem_closedBall_zero_iff.mp (hfr hw)
        rw [dist_eq_norm]
        linarith [norm_sub_norm_le z w]
      have hκd : 1 ≤ κ * d' / t := by
        rw [le_div_iff₀ ht, one_mul]
        have h1 : κ * (‖z‖ - ρ) ≤ κ * d' :=
          mul_le_mul_of_nonneg_left (hdz.trans (le_max_left _ _)) hκ0.le
        have h2 : ‖z‖ + ρ ≤ κ * (‖z‖ - ρ) := by
          rw [hκ, t15cKappa, div_mul_eq_mul_div, le_div_iff₀ hρ'ρ]
          nlinarith
        linarith
      calc hitDist G (verticesMeeting H.cell (frontier D)) x _ ≤ 1 := GMS3.hitDist_le_one G _ _ _
        _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
        _ ≤ ENNReal.ofReal ((κ * d' / t) ^ t15cXi p) :=
            ENNReal.ofReal_le_ofReal (Real.one_le_rpow hκd hξ.le)
    · -- `z` inside `B_{(ρ+ρ')/2}(0)`: the scales `[ε^β, (ρ' − ρ)/4]`
      set R := (ρ' - ρ) / 4 with hR
      have hR0 : 0 < R := by positivity
      have h35 : ∀ r, ε ^ β ≤ r → r ≤ R → ∀ y ∈ verticesMeeting H.cell (ball z r),
          ENNReal.ofReal p ≤ G.walkLaw y {ξ | T15A.Lemma311Event G H.cell z r (G.vertexPath ξ)} := by
        intro r hr1 hr2
        refine h311 z r hr1 (by linarith) fun w hw => ?_
        rw [mem_ball_zero_iff]
        rw [mem_ball, dist_eq_norm] at hw
        linarith [norm_le_norm_add_norm_sub' w z, norm_sub_rev w z]
      refine (t15c_hitDist_compl_le_rpow hLC hp0 hp1 hDo hDb hDc hxD hz hεβ hR0 ht h35).trans
        (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow
          (div_nonneg (le_max_of_le_right hεβ.le) (le_min hR0.le (by linarith))) ?_ hξ.le))
      -- `max(2d, ε^β) / min(R, t/2) ≤ κ d' / t`
      set c := 2 * (3 * ρ + ρ') / (ρ' - ρ) with hc
      have hc2 : 2 ≤ c := by rw [hc, le_div_iff₀ hρ'ρ]; linarith
      have hmin : t / c ≤ min R (t / 2) := by
        refine le_min ?_ ?_
        · rw [hR, hc, div_div_eq_mul_div, div_le_div_iff₀ (by linarith) (by norm_num)]
          nlinarith
        · exact div_le_div_of_nonneg_left ht.le (by norm_num) hc2
      have hnum : max (2 * d) (ε ^ β) ≤ 2 * d' := by
        refine max_le (by linarith [le_max_left d (ε ^ β)]) ?_
        linarith [le_max_right d (ε ^ β)]
      calc max (2 * d) (ε ^ β) / min R (t / 2) ≤ 2 * d' / (t / c) :=
            div_le_div₀ (by positivity) hnum (by positivity) hmin
        _ = κ * d' / t := by
            rw [hκ, t15cKappa, hc]
            field_simp
            ring

/-- **(3.38) in [18]'s form, good-event form**: under the hypotheses of
`t15c_hitDist_compl_le_of_lemma311Holds` and connectivity of `G`, the walk from `x` first hits `V(∂D)` at a vertex of
`V(D) ∩ V(∂D ∩ B_t(z))` with probability at least `1 − κ^ξ (t / max(dist(z, ∂D), ε^β))^{−ξ}`. -/
theorem t15c_hitDist_ge_of_lemma311Holds {H : CellularEmbedding G o} (hconn : G.adj.Connected)
    (hLC : H.PointConnected) {ε ρ ρ' β p : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) (hρρ' : ρ < ρ') (hp0 : 0 < p)
    (hp1 : p < 1) (h311 : T15A.Lemma311Holds H ε ρ' β p) {D : Set ℂ} (hDo : IsOpen D)
    (hDρ : D ⊆ ball (0 : ℂ) ρ) (hDc : IsPreconnected Dᶜ) {x : V} (hxD : (H.cell x ∩ D).Nonempty) {z : ℂ}
    (hz : z ∈ H.cell x) {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (1 - t15cKappa ρ ρ' ^ t15cXi p *
        (t / max (infDist z (frontier D)) (ε ^ β)) ^ (-t15cXi p)) ≤
      hitDist G (verticesMeeting H.cell (frontier D)) x
        (verticesMeeting H.cell D ∩ verticesMeeting H.cell (frontier D ∩ ball z t)) := by
  have hDb : Bornology.IsBounded D := Metric.isBounded_ball.subset hDρ
  set W := verticesMeeting H.cell D ∩ verticesMeeting H.cell (frontier D ∩ ball z t) with hW
  set q := t15cKappa ρ ρ' ^ t15cXi p * (t / max (infDist z (frontier D)) (ε ^ β)) ^ (-t15cXi p) with hq
  have hq0 : 0 ≤ q := mul_nonneg (Real.rpow_nonneg (t15cKappa_pos hρ hρρ').le _)
    (Real.rpow_nonneg (div_nonneg ht.le (le_max_of_le_right (Real.rpow_pos_of_pos hε β).le)) _)
  have hsum := GMS3.hitDist_add_compl_eq_one G (t15c_walkLaw_hitTime_ne_top (H := H) hconn hDo hDb hxD) W
  have hbad := t15c_hitDist_compl_le_of_lemma311Holds hLC hε hρ hρρ' hp0 hp1 h311 hDo hDρ hDc hxD hz ht
  rw [ENNReal.ofReal_sub _ hq0, ENNReal.ofReal_one]
  calc 1 - ENNReal.ofReal q ≤ 1 - hitDist G (verticesMeeting H.cell (frontier D)) x Wᶜ :=
        tsub_le_tsub_left hbad _
    _ = hitDist G (verticesMeeting H.cell (frontier D)) x W := by
        rw [← hsum, ENNReal.add_sub_cancel_right (GMS3.hitDist_ne_top G _ _ _)]

/-! ### (3.31) on one environment -/

/-- **The conclusion of [18] (3.31) on one environment** (`[18]`, corrected with the floor `ε^β`), the
form T15B consumes. For every open `D ⊆ B_ρ(0)` with `ℂ \ D` preconnected, every `f` discrete harmonic on
`V(D) \ V(∂D)` (`GMS3.lap G f = 0`, the sum of S0V's `IsHarmonicExtension`), every bound `M ≥ |f|` on `V(D)`
(`‖f‖_∞`), every `x ∈ V(D)`, every point `z` of the cell `H_x` (e.g. `η(x)`), every `t > 0` and every lower
(resp. upper) bound `m` of `f` on `V(D) ∩ V(∂D ∩ B_t(z))` with `m ≤ M` (resp. `−M ≤ m`):
`m − A M (t / (dist(z, ∂D) ∨ ε^β))^{−ξ} ≤ f(x)` (resp. `f(x) ≤ m + A M (…)^{−ξ}`). With `m` the minimum (resp.
maximum) of `f` over that vertex set this is (3.31); the side conditions on `m` hold automatically then. -/
def T15CBoundaryEstimate (H : CellularEmbedding G o) (ε ρ β ξ A : ℝ) : Prop :=
  ∀ D : Set ℂ, IsOpen D → D ⊆ ball (0 : ℂ) ρ → IsPreconnected Dᶜ →
    ∀ f : V → ℝ, (∀ y ∈ verticesMeeting H.cell D, y ∉ verticesMeeting H.cell (frontier D) → lap G f y = 0) →
    ∀ M : ℝ, (∀ y ∈ verticesMeeting H.cell D, |f y| ≤ M) →
    ∀ x ∈ verticesMeeting H.cell D, ∀ z ∈ H.cell x, ∀ t : ℝ, 0 < t → ∀ m : ℝ,
      ((∀ y ∈ verticesMeeting H.cell D ∩ verticesMeeting H.cell (frontier D ∩ ball z t), m ≤ f y) → m ≤ M →
        m - A * M * (t / max (infDist z (frontier D)) (ε ^ β)) ^ (-ξ) ≤ f x) ∧
      ((∀ y ∈ verticesMeeting H.cell D ∩ verticesMeeting H.cell (frontier D ∩ ball z t), f y ≤ m) → -M ≤ m →
        f x ≤ m + A * M * (t / max (infDist z (frontier D)) (ε ^ β)) ^ (-ξ))

/-- **[18] (3.31), deterministic on the good event**: on T15A's event `Lemma311Holds H ε ρ' β p`
((3.35) at an ambient radius `ρ' > ρ`), for a connected graph with (LC) and `0 < p < 1`, the boundary estimate holds
with `ξ = t15cXi p` and `A = 2 κ^ξ`, `κ = 4 (3ρ + ρ') / (ρ' − ρ)`. -/
theorem t15c_boundaryEstimate_of_lemma311Holds {H : CellularEmbedding G o} (hconn : G.adj.Connected)
    (hLC : H.PointConnected) {ε ρ ρ' β p : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) (hρρ' : ρ < ρ') (hp0 : 0 < p)
    (hp1 : p < 1) (h311 : T15A.Lemma311Holds H ε ρ' β p) :
    T15CBoundaryEstimate H ε ρ β (t15cXi p) (2 * t15cKappa ρ ρ' ^ t15cXi p) := by
  intro D hDo hDρ hDc f hharm M hM x hx z hz t ht m
  have hDb : Bornology.IsBounded D := Metric.isBounded_ball.subset hDρ
  have hxv : x ∈ vFin H D := (mem_vFin H hDb).mpr hx
  have hharm' : ∀ y ∈ vFin H D, ¬ (H.cell y ∩ frontier D).Nonempty → lap G f y = 0 := fun y hy hyB =>
    hharm y ((mem_vFin H hDb).mp hy) hyB
  have hM' : ∀ y ∈ vFin H D, |f y| ≤ M := fun y hy => hM y ((mem_vFin H hDb).mp hy)
  set q := t15cKappa ρ ρ' ^ t15cXi p * (t / max (infDist z (frontier D)) (ε ^ β)) ^ (-t15cXi p) with hq
  have hq0 : 0 ≤ q := mul_nonneg (Real.rpow_nonneg (t15cKappa_pos hρ hρρ').le _)
    (Real.rpow_nonneg (div_nonneg ht.le (le_max_of_le_right (Real.rpow_pos_of_pos hε β).le)) _)
  have hbound := t15c_hitDist_compl_le_of_lemma311Holds hLC hε hρ hρρ' hp0 hp1 h311 hDo hDρ hDc hx hz ht
  have herr : 2 * t15cKappa ρ ρ' ^ t15cXi p * M *
      (t / max (infDist z (frontier D)) (ε ^ β)) ^ (-t15cXi p) = 2 * M * q := by
    rw [hq]; ring
  refine ⟨fun hm hmM => ?_, fun hm hmM => ?_⟩
  · rw [herr]
    exact t15c_ge_of_hitDist_compl_le (H := H) hconn hDo hDb f hharm' hM' hxv hbound hq0
      (fun y hy hyB hyW => hm y hyW) hmM
  · rw [herr]
    exact t15c_le_of_hitDist_compl_le (H := H) hconn hDo hDb f hharm' hM' hxv hbound hq0
      (fun y hy hyB hyW => hm y hyW) hmM

/-! ### (3.31) with probability `1 − O(ε^α)` -/

/-- The environments of a random cell family at mesh `ε = 2⁻ᵏ` on which (3.31) holds with constants
`(ρ, β, ξ, A)`. -/
def T15CBoundaryGood (F : CellFamily.RandomCellFamily) (k : ℕ) (ρ β ξ A : ℝ) : Set F.Ω :=
  {ω | T15CBoundaryEstimate (F.H k ω) (CellFamily.mesh k) ρ β ξ A}

/-- **[18] Theorem 3.9, boundary estimate (3.31), with probability `1 − O(ε^α)`** (`[18]`, corrected
floor), for a random cell family whose graphs are a.s. connected and whose cells a.s. satisfy (LC), from T15A's
`Lemma311Bad F ρ'` ([18] Lemma 3.11 at an ambient radius `ρ' > ρ`): there are `α, β, ξ, A > 0` and `C` such that
at every dyadic mesh `ε = 2⁻ᵏ` the event that (3.31) fails (for some `D, f, M, x, z, t, m`) has probability
`≤ C ε^α` (outer measure, the project's bad-event convention). -/
theorem t15c_boundaryEstimateBad_of_lemma311Bad (F : CellFamily.RandomCellFamily) {ρ ρ' : ℝ} (hρ : 0 < ρ)
    (hρρ' : ρ < ρ') (h311 : T15A.Lemma311Bad F ρ') (hconn : ∀ k, ∀ᵐ ω ∂F.P, (F.G k ω).adj.Connected)
    (hLC : ∀ k, ∀ᵐ ω ∂F.P, (F.H k ω).PointConnected) :
    ∃ α : ℝ, 0 < α ∧ ∃ β : ℝ, 0 < β ∧ ∃ ξ : ℝ, 0 < ξ ∧ ∃ A : ℝ, 0 < A ∧ ∃ C : ℝ,
      ∀ k, F.P (T15CBoundaryGood F k ρ β ξ A)ᶜ ≤ ENNReal.ofReal (C * CellFamily.mesh k ^ α) := by
  obtain ⟨α, hα, β, hβ, p, hp, C, hC⟩ := h311
  set p' := min p (1 / 2) with hp'
  have hp'0 : 0 < p' := lt_min hp (by norm_num)
  have hp'1 : p' < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  refine ⟨α, hα, β, hβ, t15cXi p', t15cXi_pos hp'0 hp'1, 2 * t15cKappa ρ ρ' ^ t15cXi p',
    mul_pos two_pos (Real.rpow_pos_of_pos (t15cKappa_pos hρ hρρ') _), C, fun k => ?_⟩
  have hm0 : 0 < CellFamily.mesh k := zpow_pos (by norm_num) _
  have hsub : (T15CBoundaryGood F k ρ β (t15cXi p') (2 * t15cKappa ρ ρ' ^ t15cXi p'))ᶜ ⊆
      (T15A.Lemma311Good F k ρ' β p)ᶜ ∪ ({ω | ¬ (F.G k ω).adj.Connected} ∪
        {ω | ¬ (F.H k ω).PointConnected}) := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq, not_or, not_not] at hcon
    obtain ⟨hgood, hc, hl⟩ := hcon
    exact hω (t15c_boundaryEstimate_of_lemma311Holds hc hl hm0 hρ hρρ' hp'0 hp'1
      (T15A.Lemma311Holds.mono hgood hm0 (zpow_le_one_of_nonpos₀ (by norm_num) (by simp)) le_rfl le_rfl
        (min_le_left _ _)))
  have hN1 : F.P {ω | ¬ (F.G k ω).adj.Connected} = 0 := ae_iff.mp (hconn k)
  have hN2 : F.P {ω | ¬ (F.H k ω).PointConnected} = 0 := ae_iff.mp (hLC k)
  calc F.P (T15CBoundaryGood F k ρ β (t15cXi p') (2 * t15cKappa ρ ρ' ^ t15cXi p'))ᶜ
      ≤ F.P ((T15A.Lemma311Good F k ρ' β p)ᶜ ∪ ({ω | ¬ (F.G k ω).adj.Connected} ∪
          {ω | ¬ (F.H k ω).PointConnected})) := measure_mono hsub
    _ ≤ F.P (T15A.Lemma311Good F k ρ' β p)ᶜ + (F.P {ω | ¬ (F.G k ω).adj.Connected} +
          F.P {ω | ¬ (F.H k ω).PointConnected}) :=
        (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
    _ = F.P (T15A.Lemma311Good F k ρ' β p)ᶜ := by rw [hN1, hN2, add_zero, add_zero]
    _ ≤ ENNReal.ofReal (C * CellFamily.mesh k ^ α) := hC k

end MatedCRTHarmonic.GMSMain
