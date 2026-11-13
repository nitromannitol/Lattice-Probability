/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSMain.T15BInterior at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.T15BOscillation

/-!
# [18] Theorem 3.9, interior continuity estimate (3.30)

Source: Gwynne–Miller–Sheffield, *Harmonic functions on mated-CRT maps* [18], Theorem 3.9, display (3.30), and its proof
(`[18]`, display (3.37)).

**Deterministic form (3.30′)**. On one environment: a cellular embedding `H`
of a connected graph, an open set `D`, a scale floor `s > 0` (in [18], `s = ε^β`), and (3.35) with probability `p > 0`
at every `(z, r)` with `r ≥ s` and `B_{2r}(z) ⊆ D` (`DiscEvent`). Then every `u` that is discrete harmonic on
`V(D) \ V(∂D)` with `|u| ≤ M` on `V(D)` satisfies, for every interior vertex `x` (`H_x` meets `D`, not `∂D`), every
`y ∈ V(D)` and all `z_x ∈ H_x`, `z_y ∈ H_y` (`interior_estimate`):

  `|u(x) − u(y)| · dist(z_x, ∂D)^ξ ≤ A · M · (s ∨ |z_x − z_y|)^ξ`,

with `ξ = holderExponent p = log₄(1/(1 − min p (1/2))) > 0` and `A = holderConst p = 2·16^ξ` depending only on `p`
(DB5's `ξ₀ = log₂(1/(1 − p))` comes from Lemma 3.10 at dyadic scales; the oscillation route contracts by `1 − p`
per factor `4` of the radius). The ratio form is `interior_estimate_ratio` (`GMSMain/T15BTheorem15.lean`).

**Proof.** `osc_iterate`: iterate the one-scale contraction `osc_step'` over the radii `R/(4·4^j)`, `j < n`, about
`z_x ∈ D`, where `R = dist(z_x, ∂D)` (so `B_R(z_x) ⊆ D`) and `4^n ≤ R/(4δ) < 4^{n+1}`, `δ = s ∨ |z_x − z_y|`; then
`(1 − p')^n ≤ (16δ/R)^ξ` for `1 − p' = 1 − min p (1/2) = 4^{−ξ}`. If `R ≤ 4δ`, the bound `|u(x) − u(y)| ≤ 2M` suffices.

**Correction of [18] (3.30) (erratum).** [18] prints `(ε ∨ |η(x) − η(y)|)/dist(η(x), ∂D)` and says "we have absorbed
`β` into `ξ`"; the proof only reaches the scale `ε^β` (Lemma 3.11 holds for `r ≥ ε^β`), and the
absorption fails when `dist(η(x), ∂D) < ε^β` (then `(ε^β/dist)^ξ` is not `≤ A (ε/dist)^{ξ'}` for any `ξ' ≤ ξ`). The
corrected estimate has `ε^β ∨ |η(x) − η(y)|` (here `s ∨ |z_x − z_y|`); Theorem 1.5 is unaffected, since
`ε^β ∨ d ≤ (ε ∨ d)^β` for `d ≤ 1`. The estimate is stated in multiplied-out form (no division by
`dist(η(x), ∂D)`, which may vanish).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace MatedCRTHarmonic.GMSMain.T15B

open LFMultigraph Harmonic Markov

/-! ### The exponent and the constant -/

/-- The Hölder exponent of the interior estimate: `ξ(p) = log₄ (1/(1 − p'))`, `p' = min p (1/2)`. -/
def holderExponent (p : ℝ) : ℝ := Real.logb 4 (1 - min p (1 / 2))⁻¹

/-- The constant of the interior estimate: `A(p) = 2 · 16^{ξ(p)}`. -/
def holderConst (p : ℝ) : ℝ := 2 * 16 ^ holderExponent p

theorem holderExponent_pos {p : ℝ} (hp : 0 < p) : 0 < holderExponent p := by
  unfold holderExponent
  have h1 : 0 < min p (1 / 2) := lt_min hp (by norm_num)
  have h2 : min p (1 / 2) ≤ 1 / 2 := min_le_right _ _
  refine Real.logb_pos (by norm_num) ?_
  rw [one_lt_inv_iff₀]
  constructor <;> linarith

theorem holderConst_pos (p : ℝ) : 0 < holderConst p := by
  unfold holderConst
  positivity

theorem two_le_holderConst {p : ℝ} (hp : 0 < p) : 2 ≤ holderConst p := by
  unfold holderConst
  have h : (1 : ℝ) ≤ 16 ^ holderExponent p :=
    Real.one_le_rpow (by norm_num) (holderExponent_pos hp).le
  linarith

/-- `1 − min p (1/2) = 4^{−ξ(p)}`. -/
theorem one_sub_min_eq_rpow {p : ℝ} (hp : 0 < p) :
    1 - min p (1 / 2) = (4 : ℝ) ^ (-holderExponent p) := by
  have h1 : 0 < min p (1 / 2) := lt_min hp (by norm_num)
  have h2 : min p (1 / 2) ≤ 1 / 2 := min_le_right _ _
  have hθ : 0 < 1 - min p (1 / 2) := by linarith
  unfold holderExponent
  rw [Real.rpow_neg (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (inv_pos.mpr hθ),
    inv_inv]

/-- `θ^n ≤ t^ξ` whenever `θ = 4^{−ξ}`, `ξ ≥ 0` and `4^{−n} ≤ t`. -/
theorem pow_le_rpow_of_inv_pow_le {θ ξ t : ℝ} (hθ : θ = (4 : ℝ) ^ (-ξ)) (hξ : 0 ≤ ξ) {n : ℕ}
    (ht : ((4 : ℝ) ^ n)⁻¹ ≤ t) : θ ^ n ≤ t ^ ξ := by
  have h4 : (0 : ℝ) ≤ 4 := by norm_num
  have heq : θ ^ n = (((4 : ℝ) ^ n)⁻¹) ^ ξ := by
    rw [hθ, ← Real.rpow_natCast, ← Real.rpow_mul h4, mul_comm, Real.rpow_mul h4, Real.rpow_natCast,
      Real.rpow_neg (by positivity), Real.inv_rpow (by positivity)]
  rw [heq]
  exact Real.rpow_le_rpow (by positivity) ht hξ

/-! ### Geometric facts -/

/-- A preconnected set meeting the open set `D` but not its frontier lies in `D`. -/
theorem subset_of_isPreconnected_of_inter_frontier {s D : Set ℂ} (hs : IsPreconnected s) (hD : IsOpen D)
    (hmeet : (s ∩ D).Nonempty) (hfr : s ∩ frontier D = ∅) : s ⊆ D := by
  have hcover : s ⊆ D ∪ (closure D)ᶜ := by
    intro z hz
    by_cases hzD : z ∈ D
    · exact Or.inl hzD
    · refine Or.inr fun hzc => ?_
      have : z ∈ frontier D := by
        rw [frontier, hD.interior_eq]
        exact ⟨hzc, hzD⟩
      exact (Set.eq_empty_iff_forall_notMem.mp hfr) z ⟨hz, this⟩
  rcases hs.subset_or_subset hD isClosed_closure.isOpen_compl
    (Disjoint.mono_left subset_closure disjoint_compl_right) hcover with h | h
  · exact h
  · obtain ⟨z, hz1, hz2⟩ := hmeet
    exact absurd (subset_closure hz2) (h hz1)

/-- The open disk of radius `dist(z, ∂D)` about a point `z ∈ D` of an open set lies in `D`. -/
theorem ball_infDist_frontier_subset {D : Set ℂ} (hD : IsOpen D) {z : ℂ} (hz : z ∈ D) :
    ball z (infDist z (frontier D)) ⊆ D := by
  rcases (infDist_nonneg (x := z) (s := frontier D)).eq_or_lt with h | h
  · rw [← h, ball_zero]
    exact empty_subset _
  refine subset_of_isPreconnected_of_inter_frontier isPreconnected_ball hD ⟨z, mem_ball_self h, hz⟩ ?_
  ext w
  simp only [mem_inter_iff, mem_ball, mem_empty_iff_false, iff_false, not_and]
  intro hw hwf
  have := infDist_le_dist_of_mem (x := z) hwf
  rw [dist_comm] at hw
  linarith

/-! ### Iterating the one-scale decay -/

variable {V E : Type*} {G : LFMultigraph V E} {o : V} (H : CellularEmbedding G o)

/-- A vertex of `V(B̄_a(z))` lies in `V(B̄_b(z))` for `a ≤ b`. -/
theorem mem_verticesMeeting_closedBall_mono {z : ℂ} {a b : ℝ} (hab : a ≤ b) {v : V}
    (hv : v ∈ verticesMeeting H.cell (closedBall z a)) : v ∈ verticesMeeting H.cell (closedBall z b) := by
  obtain ⟨c, hc, hcb⟩ := hv
  exact ⟨c, hc, closedBall_subset_closedBall hab hcb⟩

/-- **Iterated oscillation decay** (the multi-scale part of the proof of [18] (3.30)). Let `B_R(z) ⊆ D` with `D`
open, `u` discrete harmonic at every vertex of `V(D) \ V(∂D)` with `|u| ≤ M` on `V(D)`, `0 ≤ p ≤ 1`, and let (3.35)
hold with probability `p` at the radii `R/(4·4^j)`, `j < n`, about `z`. Then `u(x) − u(y) ≤ (1 − p)^n · 2M` for all
`x, y ∈ V(B̄_{R/(2·4^n)}(z))`. -/
theorem osc_iterate (hconn : G.adj.Connected) (u : V → ℝ) {D : Set ℂ} (hDo : IsOpen D) {z : ℂ}
    {R p Mb : ℝ} (hR : 0 < R) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hball : ball z R ⊆ D)
    (hharm : ∀ v, (H.cell v ∩ D).Nonempty → ¬ (H.cell v ∩ frontier D).Nonempty → GMS3.lap G u v = 0)
    (hMb : ∀ v ∈ verticesMeeting H.cell D, |u v| ≤ Mb) :
    ∀ n : ℕ, (∀ j < n, ∀ v ∈ verticesMeeting H.cell (ball z (R / (4 * 4 ^ j))),
      ENNReal.ofReal p ≤ G.walkLaw v {ω | DiscEvent G H.cell z (R / (4 * 4 ^ j)) (G.vertexPath ω)}) →
    ∀ x ∈ verticesMeeting H.cell (closedBall z (R / (2 * 4 ^ n))),
      ∀ y ∈ verticesMeeting H.cell (closedBall z (R / (2 * 4 ^ n))), u x - u y ≤ (1 - p) ^ n * (2 * Mb) := by
  have hcb : closedBall z (R / 2) ⊆ D := (closedBall_subset_ball (by linarith)).trans hball
  intro n
  induction n with
  | zero =>
    intro _ x hx y hy
    have hx' : x ∈ verticesMeeting H.cell D := by
      obtain ⟨c, hc, hcb'⟩ := hx
      exact ⟨c, hc, hcb (by simpa using hcb')⟩
    have hy' : y ∈ verticesMeeting H.cell D := by
      obtain ⟨c, hc, hcb'⟩ := hy
      exact ⟨c, hc, hcb (by simpa using hcb')⟩
    have h1 := hMb x hx'
    have h2 := hMb y hy'
    rw [pow_zero, one_mul]
    have := abs_le.mp h1
    have := abs_le.mp h2
    linarith
  | succ n ih =>
    intro hdisc x hx y hy
    set r : ℝ := R / (4 * 4 ^ n) with hrdef
    have hr : 0 < r := by positivity
    have h2r : 2 * r = R / (2 * 4 ^ n) := by rw [hrdef]; field_simp; ring
    have hr2 : r / 2 = R / (2 * 4 ^ (n + 1)) := by rw [hrdef, pow_succ]; field_simp
    have ih' := ih (fun j hj => hdisc j (by omega))
    -- the bounds on `V(B̄_{2r}(z))`
    set S : Set V := verticesMeeting H.cell (closedBall z (2 * r)) with hSdef
    have hSfin : S.Finite := GMS3.finite_verticesMeeting H isBounded_closedBall
    have hSne : S.Nonempty := by
      obtain ⟨v, hv⟩ : ∃ v, z ∈ H.cell v := by
        have : z ∈ ⋃ v, H.cell v := by rw [H.iUnion_cell]; exact mem_univ z
        simpa using this
      exact ⟨v, z, hv, mem_closedBall_self (by linarith)⟩
    obtain ⟨v₀, hv₀S, hmin⟩ := Set.exists_min_image S u hSfin hSne
    have hbd : ∀ v ∈ verticesMeeting H.cell (closedBall z (2 * r)),
        u v₀ ≤ u v ∧ u v ≤ u v₀ + (1 - p) ^ n * (2 * Mb) := by
      intro v hv
      refine ⟨hmin v hv, ?_⟩
      have := ih' v (by rw [← h2r]; exact hv) v₀ (by rw [← h2r]; exact hv₀S)
      linarith
    have hharm' : ∀ v, (H.cell v ∩ ball z (2 * r)).Nonempty → ¬ (H.cell v ∩ sphere z (2 * r)).Nonempty →
        GMS3.lap G u v = 0 := by
      intro v hv1 hv2
      have hsub : H.cell v ⊆ D := (cell_subset_ball_of_not_meet H hv1 hv2).trans
        ((ball_subset_ball (by rw [h2r]; exact div_le_self hR.le (by
          have : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
          linarith))).trans hball)
      refine hharm v ?_ ?_
      · obtain ⟨c, hc⟩ := GMS3.cell_nonempty H v
        exact ⟨c, hc, hsub hc⟩
      · rintro ⟨c, hc, hcf⟩
        exact (Set.eq_empty_iff_forall_notMem.mp hDo.inter_frontier_eq) c ⟨hsub hc, hcf⟩
    have hstep := osc_step' H hconn u hr hp0 hp1 hharm' (hdisc n (by omega)) hbd
      (x := x) (y := y) (by rw [hr2]; exact hx) (by rw [hr2]; exact hy)
    calc u x - u y ≤ (1 - p) * (u v₀ + (1 - p) ^ n * (2 * Mb) - u v₀) := hstep
      _ = (1 - p) ^ (n + 1) * (2 * Mb) := by ring

/-! ### The interior estimate (3.30′) -/

/-- **[18] (3.30), interior continuity estimate, corrected form (3.30′)** (deterministic, on one environment). Let `D` be open, `s > 0` a scale floor (in [18] `s = ε^β`), and suppose the walk
event of (3.35) has probability `≥ p > 0` from every vertex of `V(B_r(z))` whenever `r ≥ s` and `B_{2r}(z) ⊆ D`. Let
`u` be discrete harmonic on `V(D) \ V(∂D)` with `|u| ≤ M` on `V(D)`. Then for every interior vertex `x` (its cell
meets `D` but not `∂D`), every `y ∈ V(D)` and all points `z_x ∈ H_x`, `z_y ∈ H_y` (in [18] `z_x = η(x)`):
`|u(x) − u(y)| · dist(z_x, ∂D)^ξ ≤ A · M · (s ∨ |z_x − z_y|)^ξ`, with `ξ = holderExponent p`, `A = holderConst p`. -/
theorem interior_estimate (hconn : G.adj.Connected) (u : V → ℝ) {D : Set ℂ} (hDo : IsOpen D)
    {p s Mb : ℝ} (hp : 0 < p) (hs : 0 < s)
    (hharm : ∀ v, (H.cell v ∩ D).Nonempty → ¬ (H.cell v ∩ frontier D).Nonempty → GMS3.lap G u v = 0)
    (hMb : ∀ v ∈ verticesMeeting H.cell D, |u v| ≤ Mb)
    (hdisc : ∀ (z : ℂ) (r : ℝ), s ≤ r → ball z (2 * r) ⊆ D → ∀ v ∈ verticesMeeting H.cell (ball z r),
      ENNReal.ofReal p ≤ G.walkLaw v {ω | DiscEvent G H.cell z r (G.vertexPath ω)})
    {x y : V} (hx : x ∈ verticesMeeting H.cell D) (hxA : x ∉ verticesMeeting H.cell (frontier D))
    (hy : y ∈ verticesMeeting H.cell D) {zx zy : ℂ} (hzx : zx ∈ H.cell x) (hzy : zy ∈ H.cell y) :
    |u x - u y| * infDist zx (frontier D) ^ holderExponent p ≤
      holderConst p * Mb * max s (dist zx zy) ^ holderExponent p := by
  set ξ := holderExponent p with hξdef
  have hξ : 0 < ξ := holderExponent_pos hp
  set R := infDist zx (frontier D) with hRdef
  set δ := max s (dist zx zy) with hδdef
  have hδ : 0 < δ := lt_of_lt_of_le hs (le_max_left _ _)
  have hR0 : 0 ≤ R := infDist_nonneg
  have hMb0 : 0 ≤ Mb := (abs_nonneg _).trans (hMb x hx)
  have hdiff : |u x - u y| ≤ 2 * Mb := by
    have h1 := abs_le.mp (hMb x hx)
    have h2 := abs_le.mp (hMb y hy)
    rw [abs_le]
    constructor <;> linarith
  have h16 : (16 : ℝ) ^ ξ * δ ^ ξ = (16 * δ) ^ ξ := (Real.mul_rpow (by norm_num) hδ.le).symm
  unfold holderConst
  rw [← hξdef]
  rcases le_or_gt R (4 * δ) with hRle | hRgt
  · -- few scales: the trivial bound
    have h1 : R ^ ξ ≤ (16 * δ) ^ ξ := Real.rpow_le_rpow hR0 (by linarith) hξ.le
    calc |u x - u y| * R ^ ξ ≤ (2 * Mb) * (16 * δ) ^ ξ :=
          mul_le_mul hdiff h1 (Real.rpow_nonneg hR0 _) (by linarith)
      _ = 2 * 16 ^ ξ * Mb * δ ^ ξ := by rw [← h16]; ring
  · -- many scales: iterate
    have hRpos : 0 < R := by linarith
    have hzxD : zx ∈ D := GMS3.cell_subset_of_inter_frontier_eq_empty H hDo hx
      (Set.not_nonempty_iff_eq_empty.mp hxA) hzx
    have hball : ball zx R ⊆ D := ball_infDist_frontier_subset hDo hzxD
    obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near (x := R / (4 * δ)) (y := (4 : ℝ))
      (by rw [le_div_iff₀ (by positivity)]; linarith) (by norm_num)
    have h4n : (0 : ℝ) < 4 ^ n := by positivity
    have hscale : δ ≤ R / (4 * 4 ^ n) := by
      rw [le_div_iff₀ (by positivity)]
      rw [le_div_iff₀ (by positivity)] at hn1
      linarith
    set p' := min p (1 / 2) with hp'def
    have hp'0 : 0 ≤ p' := le_min hp.le (by norm_num)
    have hp'1 : p' ≤ 1 := (min_le_right _ _).trans (by norm_num)
    have hdisc' : ∀ j < n, ∀ v ∈ verticesMeeting H.cell (ball zx (R / (4 * 4 ^ j))),
        ENNReal.ofReal p' ≤ G.walkLaw v {ω | DiscEvent G H.cell zx (R / (4 * 4 ^ j)) (G.vertexPath ω)} := by
      intro j hj v hv
      refine (ENNReal.ofReal_le_ofReal (min_le_left _ _)).trans (hdisc zx _ ?_ ?_ v hv)
      · -- `s ≤ δ ≤ R/(4·4^n) ≤ R/(4·4^j)`
        have hj' : (4 : ℝ) ^ j ≤ 4 ^ n := pow_le_pow_right₀ (by norm_num) hj.le
        have : R / (4 * 4 ^ n) ≤ R / (4 * 4 ^ j) :=
          div_le_div_of_nonneg_left hRpos.le (by positivity) (by linarith)
        linarith [le_max_left s (dist zx zy)]
      · refine (ball_subset_ball ?_).trans hball
        have : (1 : ℝ) ≤ 4 ^ j := one_le_pow₀ (by norm_num)
        rw [show 2 * (R / (4 * 4 ^ j)) = R / (2 * 4 ^ j) by field_simp; ring]
        exact div_le_self hRpos.le (by linarith)
    have hxin : x ∈ verticesMeeting H.cell (closedBall zx (R / (2 * 4 ^ n))) :=
      ⟨zx, hzx, mem_closedBall_self (by positivity)⟩
    have hyin : y ∈ verticesMeeting H.cell (closedBall zx (R / (2 * 4 ^ n))) := by
      refine ⟨zy, hzy, mem_closedBall.mpr ?_⟩
      rw [dist_comm]
      have h1 : dist zx zy ≤ δ := le_max_right _ _
      have h2 : R / (4 * 4 ^ n) ≤ R / (2 * 4 ^ n) :=
        div_le_div_of_nonneg_left hRpos.le (by positivity) (by linarith)
      linarith
    have hxy := osc_iterate H hconn u hDo hRpos hp'0 hp'1 hball hharm hMb n hdisc' x hxin y hyin
    have hyx := osc_iterate H hconn u hDo hRpos hp'0 hp'1 hball hharm hMb n hdisc' y hyin x hxin
    have habs : |u x - u y| ≤ (1 - p') ^ n * (2 * Mb) := by
      rw [abs_le]
      constructor <;> linarith
    -- `(1 − p')^n ≤ (16δ/R)^ξ`
    have hθ : 1 - p' = (4 : ℝ) ^ (-ξ) := one_sub_min_eq_rpow hp
    have hinv : ((4 : ℝ) ^ n)⁻¹ ≤ 16 * δ / R := by
      rw [inv_le_comm₀ h4n (by positivity), inv_div, div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ (by positivity), pow_succ] at hn2
      linarith
    have hpow : (1 - p') ^ n ≤ (16 * δ / R) ^ ξ := pow_le_rpow_of_inv_pow_le hθ hξ.le hinv
    have hRξ : 0 < R ^ ξ := Real.rpow_pos_of_pos hRpos ξ
    have hcancel : (16 * δ / R) ^ ξ * R ^ ξ = (16 * δ) ^ ξ := by
      rw [Real.div_rpow (by positivity) hRpos.le, div_mul_cancel₀ _ hRξ.ne']
    calc |u x - u y| * R ^ ξ ≤ ((1 - p') ^ n * (2 * Mb)) * R ^ ξ :=
          mul_le_mul_of_nonneg_right habs hRξ.le
      _ ≤ ((16 * δ / R) ^ ξ * (2 * Mb)) * R ^ ξ := by
          refine mul_le_mul_of_nonneg_right ?_ hRξ.le
          exact mul_le_mul_of_nonneg_right hpow (by linarith)
      _ = 2 * Mb * ((16 * δ / R) ^ ξ * R ^ ξ) := by ring
      _ = 2 * 16 ^ ξ * Mb * δ ^ ξ := by rw [hcancel, ← h16]; ring

end MatedCRTHarmonic.GMSMain.T15B
