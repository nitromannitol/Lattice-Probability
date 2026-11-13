import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.T15BTheorem15

/-!
# Hölder continuity of discrete harmonic functions with discrete Hölder boundary data

Source: Gwynne–Miller–Sheffield, *Harmonic functions on mated-CRT maps* (arXiv:1807.07511), proof of Theorem 3.9: the
assembly of (3.33) from the interior estimate (3.30), the boundary estimate (3.31) and the comparison of boundary
values (3.32). This is `theorem15_deterministic` with the continuous boundary data (a Hölder function `f` on `∂D` and
the discrete harmonic extension of its (1.6) values) replaced by discrete boundary data: a function `g : V → ℝ`,
discrete harmonic on `V(D) \ V(∂D)`, whose values on the boundary vertices `V(D) ∩ V(∂D)` satisfy
`|g(a) − g(b)| ≤ C' (ε ∨ |pt a − pt b|)^χ` and `|g(a)| ≤ M`. Only the step (3.32) changes
(`abs_sub_le_of_discreteBdry` replaces `abs_sub_le_of_bdry`), together with the maximum principle
(`abs_le_of_discreteBoundary` replaces `abs_le_of_isHarmonicExtension`).

Main results:
* `abs_le_of_discreteBoundary`: the maximum principle, `|g| ≤ M` on `V(D)`.
* `theorem15_deterministic_discreteBoundary`: `|g(x) − g(y)| ≤ K (ε ∨ |pt x − pt y|)^ξ'` for `x, y ∈ V(D)`, with
  `K = theorem15DiscreteConst p C₁ ξ₁ β q χ C' M` and `ξ' = theorem15DiscreteExponent p ξ₁ β q χ ∈ (0, 1)`.
* `theorem15DiscreteConst_le`: `K ≤ max C₀ (A₀ M)` with `C₀ = theorem15DiscreteBdryConst χ C'` and
  `A₀ = theorem15DiscreteMassConst p C₁ ξ₁`; `A₀` depends only on the constants `(p, C₁, ξ₁)` of (3.30) and (3.31).
* `theorem15_deterministic_discreteBoundary_max`: the estimate with the constant `max C₀ (A₀ M)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal Topology

namespace MatedCRTHarmonic.GMSMain.T15B

open LFMultigraph Harmonic Markov

variable {V E : Type*} {G : LFMultigraph V E} {o : V} (H : CellularEmbedding G o)

/-! ### The maximum principle for discrete boundary data -/

/-- **The maximum principle on `V(D)` for discrete boundary data**: if `g` is discrete harmonic on `V(D) \ V(∂D)` and
`|g| ≤ M` on the boundary vertices `V(D) ∩ V(∂D)` (`D` bounded open, the graph connected), then `|g| ≤ M` on
`V(D)`. -/
theorem abs_le_of_discreteBoundary (hconn : G.adj.Connected) {D : Set ℂ} (hDo : IsOpen D)
    (hDb : Bornology.IsBounded D) {g : V → ℝ}
    (hharm : ∀ v ∈ verticesMeeting H.cell D, v ∉ verticesMeeting H.cell (frontier D) → GMS3.lap G g v = 0)
    {M : ℝ} (hbdM : ∀ v ∈ verticesMeeting H.cell D, v ∈ verticesMeeting H.cell (frontier D) → |g v| ≤ M) :
    ∀ v ∈ verticesMeeting H.cell D, |g v| ≤ M := by
  have : Infinite V := infinite_vertex H
  set K : Set V := {v | v ∈ verticesMeeting H.cell D ∧ v ∉ verticesMeeting H.cell (frontier D)}
  have hKfin : K.Finite := (GMS3.finite_verticesMeeting H hDb).subset fun v hv => hv.1
  have hesc := exists_reachable_notMem G hconn hKfin
  -- outer neighbours of `K` are boundary vertices of `V(D)`
  have hout : ∀ v ∈ K, ∀ w, G.adj.Adj v w → w ∉ K → |g w| ≤ M := by
    intro v hv w hvw hwK
    have hsub : H.cell v ⊆ D := GMS3.cell_subset_of_inter_frontier_eq_empty H hDo hv.1
      (Set.not_nonempty_iff_eq_empty.mp hv.2)
    have hwD : w ∈ verticesMeeting H.cell D := by
      obtain ⟨c, hcv, hcw⟩ := H.inter_of_adj v w hvw
      exact ⟨c, hcw, hsub hcv⟩
    have hwb : w ∈ verticesMeeting H.cell (frontier D) := by
      by_contra h
      exact hwK ⟨hwD, h⟩
    exact hbdM w hwD hwb
  have h1 := nonneg_of_lap_eq_zero G hKfin (g := fun w => M - g w)
    (fun v hv => by rw [lap_const_sub, hharm v hv.1 hv.2, neg_zero])
    (fun v hv w hvw hwK => by have := abs_le.mp (hout v hv w hvw hwK); linarith) hesc
  have h2 := nonneg_of_lap_eq_zero G hKfin (g := fun w => M + g w)
    (fun v hv => by rw [lap_const_add, hharm v hv.1 hv.2])
    (fun v hv w hvw hwK => by have := abs_le.mp (hout v hv w hvw hwK); linarith) hesc
  intro v hv
  by_cases hvb : v ∈ verticesMeeting H.cell (frontier D)
  · exact hbdM v hv hvb
  · have a1 := h1 v ⟨hv, hvb⟩
    have a2 := h2 v ⟨hv, hvb⟩
    rw [abs_le]
    constructor <;> linarith

/-! ### Boundary values -/

/-- **Comparison of boundary values from discrete Hölder data** (the step (3.32)): if
`|g(a) − g(b)| ≤ C' (ε ∨ |pt a − pt b|)^χ` for boundary vertices `a, b ∈ V(D) ∩ V(∂D)`, then for boundary vertices
`a, b` with cells of diameter `≤ s₁`, `ε ≤ s₁`, and points `z ∈ H_a`, `w ∈ H_b`:
`|g(a) − g(b)| ≤ C' (2 s₁ + |z − w|)^χ`. -/
theorem abs_sub_le_of_discreteBdry (pt : V → ℂ) (hpt : ∀ v, pt v ∈ H.cell v) {D : Set ℂ} {g : V → ℝ}
    {ε C' χ s₁ : ℝ} (hC' : 0 ≤ C') (hχ : 0 < χ)
    (hbdry : ∀ a ∈ verticesMeeting H.cell D, a ∈ verticesMeeting H.cell (frontier D) →
      ∀ b ∈ verticesMeeting H.cell D, b ∈ verticesMeeting H.cell (frontier D) →
        |g a - g b| ≤ C' * max ε (dist (pt a) (pt b)) ^ χ)
    {a b : V} (ha : a ∈ verticesMeeting H.cell D) (hab : a ∈ verticesMeeting H.cell (frontier D))
    (hb : b ∈ verticesMeeting H.cell D) (hbb : b ∈ verticesMeeting H.cell (frontier D))
    (hsa : diam (H.cell a) ≤ s₁) (hsb : diam (H.cell b) ≤ s₁) (hεs : ε ≤ s₁) {z w : ℂ}
    (hz : z ∈ H.cell a) (hw : w ∈ H.cell b) : |g a - g b| ≤ C' * (2 * s₁ + dist z w) ^ χ := by
  refine (hbdry a ha hab b hb hbb).trans (mul_le_mul_of_nonneg_left ?_ hC')
  have hs₁ : 0 ≤ s₁ := diam_nonneg.trans hsa
  have hzw : 0 ≤ dist z w := dist_nonneg
  have h1 : dist (pt a) z ≤ s₁ :=
    (dist_le_diam_of_mem (H.isCompact_cell a).isBounded (hpt a) hz).trans hsa
  have h2 : dist w (pt b) ≤ s₁ :=
    (dist_le_diam_of_mem (H.isCompact_cell b).isBounded hw (hpt b)).trans hsb
  have h3 := dist_triangle4 (pt a) z w (pt b)
  refine Real.rpow_le_rpow (le_max_of_le_right dist_nonneg) (max_le ?_ ?_) hχ.le
  · linarith
  · linarith

/-! ### The interior vertex -/

/-- **An interior vertex, discrete boundary data** (cases 2–3 of the proof of `theorem15_deterministic`). Under the
good-event hypotheses of `theorem15_deterministic_discreteBoundary`, let `x` be an interior vertex of `V(D)`,
`y ∈ V(D)`, and `0 < τ < 1/2` with `ε^β ∨ |pt x − pt y| ≤ τ⁴`. Then
`|g(x) − g(y)| ≤ A M (τ²)^{ξ₀} + 2 C' (5τ)^χ + (1 + 2^{ξ₁}) C₁ M τ^{ξ₁}` (`ξ₀ = holderExponent p`,
`A = holderConst p`): by (3.30′) if `dist(pt x, ∂D) ≥ τ²`, by (3.31′) at scale `t = τ` otherwise. -/
theorem abs_sub_le_of_interior_discreteBoundary (hconn : G.adj.Connected) (pt : V → ℂ)
    (hpt : ∀ v, pt v ∈ H.cell v) {D : Set ℂ} (hDo : IsOpen D) (hDb : Bornology.IsBounded D)
    {ε β q p C₁ ξ₁ : ℝ} (hε0 : 0 < ε) (hεq1 : ε ≤ ε ^ q) (hβq : ε ^ q ≤ ε ^ β) (hp : 0 < p)
    (hC₁ : 0 ≤ C₁) (hξ₁ : 0 < ξ₁)
    (hsmall : ∀ v ∈ verticesMeeting H.cell D, diam (H.cell v) ≤ ε ^ q)
    (h335 : ∀ (z : ℂ) (r : ℝ), ε ^ β ≤ r → ball z (2 * r) ⊆ D → ∀ v ∈ verticesMeeting H.cell (ball z r),
      ENNReal.ofReal p ≤ G.walkLaw v {ω | DiscEvent G H.cell z r (G.vertexPath ω)})
    (h331 : BoundaryEstimate G H.cell pt D (ε ^ β) C₁ ξ₁)
    {g : V → ℝ} {C' χ M : ℝ} (hC' : 0 ≤ C') (hχ : 0 < χ) (hM : 0 ≤ M)
    (hharm : ∀ v ∈ verticesMeeting H.cell D, v ∉ verticesMeeting H.cell (frontier D) → GMS3.lap G g v = 0)
    (hbdry : ∀ a ∈ verticesMeeting H.cell D, a ∈ verticesMeeting H.cell (frontier D) →
      ∀ b ∈ verticesMeeting H.cell D, b ∈ verticesMeeting H.cell (frontier D) →
        |g a - g b| ≤ C' * max ε (dist (pt a) (pt b)) ^ χ)
    (hbdM : ∀ a ∈ verticesMeeting H.cell D, a ∈ verticesMeeting H.cell (frontier D) → |g a| ≤ M)
    {x y : V} (hx : x ∈ verticesMeeting H.cell D) (hxA : x ∉ verticesMeeting H.cell (frontier D))
    (hy : y ∈ verticesMeeting H.cell D) {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1 / 2)
    (hδ : max (ε ^ β) (dist (pt x) (pt y)) ≤ τ ^ 4) :
    |g x - g y| ≤ holderConst p * M * (τ ^ 2) ^ holderExponent p + 2 * (C' * (5 * τ) ^ χ) +
      (1 + 2 ^ ξ₁) * (C₁ * M * τ ^ ξ₁) := by
  have hgM := abs_le_of_discreteBoundary H hconn hDo hDb hharm hbdM
  have hgM' : ∀ v ∈ verticesMeeting H.cell D, |(fun w => -g w) v| ≤ M := fun v hv => by
    rw [abs_neg]; exact hgM v hv
  have hharm' : ∀ v ∈ verticesMeeting H.cell D, v ∉ verticesMeeting H.cell (frontier D) →
      GMS3.lap G (fun w => -g w) v = 0 := fun v hv hvb => by rw [lap_neg, hharm v hv hvb, neg_zero]
  set d := dist (pt x) (pt y)
  have hd : d ≤ τ ^ 4 := (le_max_right _ _).trans hδ
  have hsβ : ε ^ β ≤ τ ^ 4 := (le_max_left _ _).trans hδ
  have hsq : ε ^ q ≤ τ ^ 4 := hβq.trans hsβ
  have hd0 : 0 ≤ d := dist_nonneg
  have hτ4τ2 : τ ^ 4 ≤ τ ^ 2 := pow_le_pow_of_le_one hτ0.le (by linarith) (by norm_num)
  have hτ2 : τ ^ 2 < τ := by nlinarith
  have hτ4 : 2 * τ ^ 4 < τ := by nlinarith [pow_pos hτ0 3]
  have hτ4' : τ ^ 4 ≤ τ := by nlinarith [pow_pos hτ0 3]
  have hτ2' : 2 * τ ^ 2 < τ := by nlinarith
  set A := holderConst p with hAdef
  set ξ₀ := holderExponent p with hξ₀def
  have hξ₀ : 0 < ξ₀ := holderExponent_pos hp
  have hA : 0 ≤ A := (holderConst_pos p).le
  set K5 := C' * (5 * τ) ^ χ
  have hK5 : 0 ≤ K5 := mul_nonneg hC' (Real.rpow_nonneg (by linarith) _)
  have hT1 : 0 ≤ A * M * (τ ^ 2) ^ ξ₀ := mul_nonneg (mul_nonneg hA hM) (Real.rpow_nonneg (by positivity) _)
  have hT3 : 0 ≤ C₁ * M * τ ^ ξ₁ := mul_nonneg (mul_nonneg hC₁ hM) (Real.rpow_nonneg hτ0.le _)
  have h2ξ : (1 : ℝ) ≤ 2 ^ ξ₁ := Real.one_le_rpow (by norm_num) hξ₁.le
  set R := infDist (pt x) (frontier D) with hRdef
  have hR0 : 0 ≤ R := infDist_nonneg
  have hDne : D.Nonempty := by
    obtain ⟨c, _, hc⟩ := hx
    exact ⟨c, hc⟩
  -- comparison of boundary values within distance `3τ`, from the discrete Hölder data
  have hcmp : ∀ a ∈ verticesMeeting H.cell D, a ∈ verticesMeeting H.cell (frontier D) →
      ∀ b ∈ verticesMeeting H.cell D, b ∈ verticesMeeting H.cell (frontier D) →
      ∀ pa ∈ H.cell a, ∀ pb ∈ H.cell b, dist pa pb ≤ 3 * τ → |g a - g b| ≤ K5 := by
    intro a ha hab b hb hbb pa hpa pb hpb hdist
    refine (abs_sub_le_of_discreteBdry H pt hpt hC' hχ hbdry ha hab hb hbb (hsmall a ha) (hsmall b hb)
      hεq1 hpa hpb).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (by linarith) hχ.le) hC'
  rcases le_or_gt (τ ^ 2) R with hRτ | hRτ
  · /- Case 2: `dist(pt x, ∂D) ≥ τ²`, the interior estimate (3.30′). -/
    have h := interior_estimate H hconn g hDo hp (Real.rpow_pos_of_pos hε0 β)
      (fun v hv hvb => hharm v hv hvb) hgM h335 hx hxA hy (hpt x) (hpt y)
    rw [← hAdef, ← hξ₀def, ← hRdef] at h
    have hpos : 0 < (τ ^ 2) ^ ξ₀ := Real.rpow_pos_of_pos (by positivity) _
    have h1 : max (ε ^ β) d ^ ξ₀ ≤ (τ ^ 2) ^ ξ₀ * (τ ^ 2) ^ ξ₀ := by
      rw [← Real.mul_rpow (by positivity) (by positivity), show τ ^ 2 * τ ^ 2 = τ ^ 4 by ring]
      exact Real.rpow_le_rpow (le_max_of_le_left (Real.rpow_nonneg hε0.le _)) hδ hξ₀.le
    have h2 : (τ ^ 2) ^ ξ₀ ≤ R ^ ξ₀ := Real.rpow_le_rpow (by positivity) hRτ hξ₀.le
    have h3 : |g x - g y| * (τ ^ 2) ^ ξ₀ ≤ (A * M * (τ ^ 2) ^ ξ₀) * (τ ^ 2) ^ ξ₀ := by
      calc |g x - g y| * (τ ^ 2) ^ ξ₀ ≤ |g x - g y| * R ^ ξ₀ :=
            mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
        _ ≤ A * M * max (ε ^ β) d ^ ξ₀ := h
        _ ≤ A * M * ((τ ^ 2) ^ ξ₀ * (τ ^ 2) ^ ξ₀) := mul_le_mul_of_nonneg_left h1 (mul_nonneg hA hM)
        _ = (A * M * (τ ^ 2) ^ ξ₀) * (τ ^ 2) ^ ξ₀ := by ring
    have h4 := le_of_mul_le_mul_right h3 hpos
    have h5 : 0 ≤ (1 + 2 ^ ξ₁) * (C₁ * M * τ ^ ξ₁) := mul_nonneg (by positivity) hT3
    linarith [h4, h5, hK5]
  · /- Case 3: `dist(pt x, ∂D) < τ²`, the boundary estimate (3.31′) at scale `τ`. -/
    have ht : R < τ := lt_trans hRτ hτ2
    -- the error term of (3.31′) at `x`
    have herrx : C₁ * M * (max R (ε ^ β) / τ) ^ ξ₁ ≤ C₁ * M * τ ^ ξ₁ := by
      refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) ?_ hξ₁.le) (mul_nonneg hC₁ hM)
      rw [div_le_iff₀ hτ0]
      have : max R (ε ^ β) ≤ τ ^ 2 := max_le hRτ.le (hsβ.trans hτ4τ2)
      nlinarith
    -- (3.31′) at `x`, for `g` and for `-g`
    have hup : ∀ c : ℝ, (∀ a ∈ verticesMeeting H.cell D,
        a ∈ verticesMeeting H.cell (frontier D ∩ ball (pt x) τ) → g a ≤ c) → -M ≤ c →
        g x ≤ c + C₁ * M * τ ^ ξ₁ := fun c hc hcM =>
      (h331 g M (fun v hv hvb => hharm v hv hvb) hgM x hx hxA τ ht c hc hcM).trans (by linarith)
    have hlo : ∀ c : ℝ, (∀ a ∈ verticesMeeting H.cell D,
        a ∈ verticesMeeting H.cell (frontier D ∩ ball (pt x) τ) → -g a ≤ c) → -M ≤ c →
        -g x ≤ c + C₁ * M * τ ^ ξ₁ := fun c hc hcM =>
      (h331 (fun w => -g w) M hharm' hgM' x hx hxA τ ht c hc hcM).trans (by linarith)
    by_cases hyA : y ∈ verticesMeeting H.cell (frontier D)
    · /- `y` is a boundary vertex: compare with `g(y)` directly. -/
      obtain ⟨qy, hqy, hqyD⟩ := hyA
      have hqyx : dist qy (pt x) < τ := by
        have h1 : dist qy (pt y) ≤ ε ^ q :=
          (dist_le_diam_of_mem (H.isCompact_cell y).isBounded hqy (hpt y)).trans (hsmall y hy)
        have h2 := dist_triangle qy (pt y) (pt x)
        rw [dist_comm (pt y) (pt x)] at h2
        linarith
      have hnear : ∀ a ∈ verticesMeeting H.cell D,
          a ∈ verticesMeeting H.cell (frontier D ∩ ball (pt x) τ) → |g a - g y| ≤ K5 := by
        intro a ha hab
        obtain ⟨pa, hpa, hpaD, hpab⟩ := hab
        refine hcmp a ha ⟨pa, hpa, hpaD⟩ y hy ⟨qy, hqy, hqyD⟩ pa hpa qy hqy ?_
        have h1 := dist_triangle pa (pt x) qy
        rw [mem_ball] at hpab
        rw [dist_comm (pt x) qy] at h1
        linarith
      have hgy := abs_le.mp (hgM y hy)
      have hu := hup (g y + K5) (fun a ha hab => by
        have := abs_le.mp (hnear a ha hab); linarith) (by linarith)
      have hl := hlo (-g y + K5) (fun a ha hab => by
        have := abs_le.mp (hnear a ha hab); linarith) (by linarith)
      have h2T3 : 0 ≤ 2 ^ ξ₁ * (C₁ * M * τ ^ ξ₁) := mul_nonneg (by positivity) hT3
      rw [abs_le]
      constructor
      · linarith [hu, hl, hT1, hT3, h2T3, hK5]
      · linarith [hu, hl, hT1, hT3, h2T3, hK5]
    · /- `y` is interior: (3.31′) at `y` too, comparing with a boundary vertex near `pt y`. -/
      have hRy : infDist (pt y) (frontier D) ≤ R + d := by
        have := infDist_le_infDist_add_dist (x := pt y) (y := pt x) (s := frontier D)
        rw [dist_comm] at this
        linarith
      have hty : infDist (pt y) (frontier D) < τ := by linarith
      have herry : C₁ * M * (max (infDist (pt y) (frontier D)) (ε ^ β) / τ) ^ ξ₁ ≤
          2 ^ ξ₁ * (C₁ * M * τ ^ ξ₁) := by
        have hm : max (infDist (pt y) (frontier D)) (ε ^ β) / τ ≤ 2 * τ := by
          rw [div_le_iff₀ hτ0]
          have : max (infDist (pt y) (frontier D)) (ε ^ β) ≤ 2 * τ ^ 2 :=
            max_le (by linarith) (by linarith)
          nlinarith
        calc C₁ * M * (max (infDist (pt y) (frontier D)) (ε ^ β) / τ) ^ ξ₁
            ≤ C₁ * M * (2 * τ) ^ ξ₁ :=
              mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hm hξ₁.le)
                (mul_nonneg hC₁ hM)
          _ = 2 ^ ξ₁ * (C₁ * M * τ ^ ξ₁) := by
              rw [Real.mul_rpow (by norm_num) hτ0.le]; ring
      have hupy : ∀ c : ℝ, (∀ b ∈ verticesMeeting H.cell D,
          b ∈ verticesMeeting H.cell (frontier D ∩ ball (pt y) τ) → g b ≤ c) → -M ≤ c →
          g y ≤ c + 2 ^ ξ₁ * (C₁ * M * τ ^ ξ₁) := fun c hc hcM =>
        (h331 g M (fun v hv hvb => hharm v hv hvb) hgM y hy hyA τ hty c hc hcM).trans (by linarith)
      have hloy : ∀ c : ℝ, (∀ b ∈ verticesMeeting H.cell D,
          b ∈ verticesMeeting H.cell (frontier D ∩ ball (pt y) τ) → -g b ≤ c) → -M ≤ c →
          -g y ≤ c + 2 ^ ξ₁ * (C₁ * M * τ ^ ξ₁) := fun c hc hcM =>
        (h331 (fun w => -g w) M hharm' hgM' y hy hyA τ hty c hc hcM).trans (by linarith)
      obtain ⟨b₀, hb₀, q₀, hq₀, hq₀D, hq₀b⟩ := exists_bdry_vertex_near H hDb hDne hty
      rw [mem_ball] at hq₀b
      have hb₀b : b₀ ∈ verticesMeeting H.cell (frontier D) := ⟨q₀, hq₀, hq₀D⟩
      have hnearx : ∀ a ∈ verticesMeeting H.cell D,
          a ∈ verticesMeeting H.cell (frontier D ∩ ball (pt x) τ) → |g a - g b₀| ≤ K5 := by
        intro a ha hab
        obtain ⟨pa, hpa, hpaD, hpab⟩ := hab
        refine hcmp a ha ⟨pa, hpa, hpaD⟩ b₀ hb₀ hb₀b pa hpa q₀ hq₀ ?_
        rw [mem_ball] at hpab
        have h1 := dist_triangle4 pa (pt x) (pt y) q₀
        rw [dist_comm (pt y) q₀] at h1
        linarith
      have hneary : ∀ b ∈ verticesMeeting H.cell D,
          b ∈ verticesMeeting H.cell (frontier D ∩ ball (pt y) τ) → |g b - g b₀| ≤ K5 := by
        intro b hb hbb
        obtain ⟨pb, hpb, hpbD, hpbb⟩ := hbb
        refine hcmp b hb ⟨pb, hpb, hpbD⟩ b₀ hb₀ hb₀b pb hpb q₀ hq₀ ?_
        rw [mem_ball] at hpbb
        have h1 := dist_triangle pb (pt y) q₀
        rw [dist_comm (pt y) q₀] at h1
        linarith
      have hgb := abs_le.mp (hgM b₀ hb₀)
      have hu := hup (g b₀ + K5) (fun a ha hab => by
        have := abs_le.mp (hnearx a ha hab); linarith) (by linarith)
      have hl := hlo (-g b₀ + K5) (fun a ha hab => by
        have := abs_le.mp (hnearx a ha hab); linarith) (by linarith)
      have huy := hupy (g b₀ + K5) (fun b hb hbb => by
        have := abs_le.mp (hneary b hb hbb); linarith) (by linarith)
      have hly := hloy (-g b₀ + K5) (fun b hb hbb => by
        have := abs_le.mp (hneary b hb hbb); linarith) (by linarith)
      rw [abs_le]
      constructor
      · linarith [hu, hly, hT1, hT3, h2ξ]
      · linarith [huy, hl, hT1, hT3, h2ξ]

/-! ### The constants -/

/-- The exponent `ξ'` of the estimate with discrete boundary data: the exponent `theorem15Exponent` of
`theorem15_deterministic`, `ξ' = min(β ξ₀/2, β χ/4, β ξ₁/4, q χ)` with `ξ₀ = holderExponent p`. -/
def theorem15DiscreteExponent (p ξ₁ β q χ : ℝ) : ℝ :=
  theorem15Exponent p ξ₁ β q χ

/-- The constant `K` of the estimate with discrete boundary data: the constant `theorem15Const` of
`theorem15_deterministic` with the Hölder constant `C'` and the bound `M` of the boundary data,
`K = max (3^χ C' + A M + 2·5^χ C' + (1 + 2^{ξ₁}) C₁ M) (2 M / w₀^{ξ'})`, `w₀ = (1/16)^{1/β}`. -/
def theorem15DiscreteConst (p C₁ ξ₁ β q χ C' M : ℝ) : ℝ :=
  theorem15Const p C₁ ξ₁ β q χ C' M

/-- The part `C₀ = 2 (3^χ + 2·5^χ) C'` of `theorem15DiscreteConst` coming from the Hölder constant of the boundary
data. -/
def theorem15DiscreteBdryConst (χ C' : ℝ) : ℝ :=
  2 * ((3 ^ χ + 2 * 5 ^ χ) * C')

/-- The factor `A₀ = 2 (A + (1 + 2^{ξ₁}) C₁ + 2·2^{ξ₁})` of the bound `M` in `theorem15DiscreteConst`
(`A = holderConst p`); it depends only on the constants of (3.30′) and (3.31′). -/
def theorem15DiscreteMassConst (p C₁ ξ₁ : ℝ) : ℝ :=
  2 * (holderConst p + (1 + 2 ^ ξ₁) * C₁ + 2 * 2 ^ ξ₁)

theorem theorem15DiscreteExponent_pos {p ξ₁ β q χ : ℝ} (hp : 0 < p) (hξ₁ : 0 < ξ₁) (hβ : 0 < β)
    (hq : 0 < q) (hχ : 0 < χ) : 0 < theorem15DiscreteExponent p ξ₁ β q χ :=
  theorem15Exponent_pos hp hξ₁ hβ hq hχ

theorem theorem15DiscreteExponent_lt_one {p ξ₁ β q χ : ℝ} (hβ1 : β ≤ 1) (hχ : 0 < χ) (hχ1 : χ ≤ 1) :
    theorem15DiscreteExponent p ξ₁ β q χ < 1 := by
  have h1 : β * χ ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hβ1) hχ.le]
  unfold theorem15DiscreteExponent theorem15Exponent
  exact lt_of_le_of_lt ((min_le_left _ _).trans (min_le_right _ _)) (by linarith)

theorem theorem15DiscreteMassConst_pos {p C₁ ξ₁ : ℝ} (hC₁ : 0 ≤ C₁) :
    0 < theorem15DiscreteMassConst p C₁ ξ₁ := by
  have hA := holderConst_pos p
  have h2 : (0 : ℝ) ≤ 2 ^ ξ₁ := by positivity
  have h3 : 0 ≤ (1 + 2 ^ ξ₁) * C₁ := mul_nonneg (by positivity) hC₁
  unfold theorem15DiscreteMassConst
  linarith

/-- **The dependence of `K` on the bound `M` of the boundary data**:
`theorem15DiscreteConst p C₁ ξ₁ β q χ C' M ≤ max C₀ (A₀ M)` with `C₀ = theorem15DiscreteBdryConst χ C'` (free of
`M`) and `A₀ = theorem15DiscreteMassConst p C₁ ξ₁` (free of `M`, `χ`, `C'`, `β`, `q`). -/
theorem theorem15DiscreteConst_le {p C₁ ξ₁ β q χ C' M : ℝ} (hβ : 0 < β) (hC₁ : 0 ≤ C₁) (hM : 0 ≤ M) :
    theorem15DiscreteConst p C₁ ξ₁ β q χ C' M ≤
      max (theorem15DiscreteBdryConst χ C') (theorem15DiscreteMassConst p C₁ ξ₁ * M) := by
  have hw₀0 : 0 < theorem15Threshold β := Real.rpow_pos_of_pos (by norm_num) _
  have hw₀1 : theorem15Threshold β ≤ 1 := Real.rpow_le_one (by norm_num) (by norm_num) (by positivity)
  have hξle : theorem15Exponent p ξ₁ β q χ ≤ β * ξ₁ / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hlow : theorem15Threshold β ^ (β * ξ₁ / 4) ≤ theorem15Threshold β ^ theorem15Exponent p ξ₁ β q χ :=
    Real.rpow_le_rpow_of_exponent_ge hw₀0 hw₀1 hξle
  have heq : theorem15Threshold β ^ (β * ξ₁ / 4) * 2 ^ ξ₁ = 1 := by
    have h16 : (2 : ℝ) ^ ξ₁ = 16 ^ (ξ₁ / 4) := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      congr 1
      ring
    rw [h16, theorem15Threshold, ← Real.rpow_mul (by norm_num),
      show 1 / β * (β * ξ₁ / 4) = ξ₁ / 4 by
        rw [one_div, ← mul_div_assoc, ← mul_assoc, inv_mul_cancel₀ hβ.ne', one_mul],
      ← Real.mul_rpow (by norm_num) (by norm_num)]
    norm_num
  have hpos : 0 < theorem15Threshold β ^ theorem15Exponent p ξ₁ β q χ := Real.rpow_pos_of_pos hw₀0 _
  have h2ξ : (0 : ℝ) ≤ 2 ^ ξ₁ := by positivity
  have hdiv : 2 * M / theorem15Threshold β ^ theorem15Exponent p ξ₁ β q χ ≤ 2 * 2 ^ ξ₁ * M := by
    rw [div_le_iff₀ hpos]
    have h1 := mul_le_mul_of_nonneg_right hlow h2ξ
    have h2 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 2 * M)
    calc 2 * M = 2 * M * (theorem15Threshold β ^ (β * ξ₁ / 4) * 2 ^ ξ₁) := by rw [heq, mul_one]
      _ ≤ 2 * M * (theorem15Threshold β ^ theorem15Exponent p ξ₁ β q χ * 2 ^ ξ₁) := h2
      _ = 2 * 2 ^ ξ₁ * M * theorem15Threshold β ^ theorem15Exponent p ξ₁ β q χ := by ring
  have hA : 0 ≤ holderConst p := (holderConst_pos p).le
  have hc : 0 ≤ (holderConst p + (1 + 2 ^ ξ₁) * C₁) * M :=
    mul_nonneg (add_nonneg hA (mul_nonneg (by positivity) hC₁)) hM
  have hm0 : 0 ≤ 2 ^ ξ₁ * M := mul_nonneg h2ξ hM
  unfold theorem15DiscreteConst theorem15Const theorem15MainConst theorem15DiscreteBdryConst
    theorem15DiscreteMassConst
  refine max_le ?_ (le_max_of_le_right ?_)
  · rcases le_total ((3 ^ χ + 2 * 5 ^ χ) * C') ((holderConst p + (1 + 2 ^ ξ₁) * C₁ + 2 * 2 ^ ξ₁) * M)
      with h | h
    · exact le_max_of_le_right (by linarith)
    · exact le_max_of_le_left (by linarith)
  · linarith

/-! ### Theorem 1.5 with discrete boundary data -/

/-- **[18] Theorem 1.5 / (3.33) with discrete boundary data, deterministic on the good event** (the proof of
`theorem15_deterministic` with (3.32) replaced by a discrete hypothesis). Let `H` be a cellular embedding of a
connected graph with marked points `pt v ∈ H_v`, `D` bounded open, `0 < ε ≤ 1` and `0 < β ≤ q ≤ 1`, and assume on
this environment:
* the cells of `V(D)` have diameter `≤ ε^q` ([18] Lemma 2.7);
* (3.35) with probability `p > 0` at every `(z, r)` with `r ≥ ε^β`, `B_{2r}(z) ⊆ D` (`DiscEvent`);
* (3.31′) with floor `ε^β` and constants `C₁ ≥ 0`, `ξ₁ > 0` (`BoundaryEstimate`).
Let `g : V → ℝ` be discrete harmonic on `V(D) \ V(∂D)`, with `|g(a) − g(b)| ≤ C' (ε ∨ |pt a − pt b|)^χ` and
`|g(a)| ≤ M` for all boundary vertices `a, b ∈ V(D) ∩ V(∂D)` (`C' ≥ 0`, `χ > 0`, `M ≥ 0`). Then for all
`x, y ∈ V(D)`: `|g(x) − g(y)| ≤ K (ε ∨ |pt x − pt y|)^ξ'`, `K = theorem15DiscreteConst p C₁ ξ₁ β q χ C' M`,
`ξ' = theorem15DiscreteExponent p ξ₁ β q χ`. -/
theorem theorem15_deterministic_discreteBoundary (hconn : G.adj.Connected) (pt : V → ℂ)
    (hpt : ∀ v, pt v ∈ H.cell v) {D : Set ℂ} (hDo : IsOpen D) (hDb : Bornology.IsBounded D)
    {ε β q p C₁ ξ₁ : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hβ : 0 < β) (hβq : β ≤ q) (hq1 : q ≤ 1)
    (hp : 0 < p) (hC₁ : 0 ≤ C₁) (hξ₁ : 0 < ξ₁)
    (hsmall : ∀ v ∈ verticesMeeting H.cell D, diam (H.cell v) ≤ ε ^ q)
    (h335 : ∀ (z : ℂ) (r : ℝ), ε ^ β ≤ r → ball z (2 * r) ⊆ D → ∀ v ∈ verticesMeeting H.cell (ball z r),
      ENNReal.ofReal p ≤ G.walkLaw v {ω | DiscEvent G H.cell z r (G.vertexPath ω)})
    (h331 : BoundaryEstimate G H.cell pt D (ε ^ β) C₁ ξ₁)
    {g : V → ℝ} {C' χ M : ℝ} (hC' : 0 ≤ C') (hχ : 0 < χ) (hM : 0 ≤ M)
    (hharm : ∀ v ∈ verticesMeeting H.cell D, v ∉ verticesMeeting H.cell (frontier D) → GMS3.lap G g v = 0)
    (hbdry : ∀ a ∈ verticesMeeting H.cell D, a ∈ verticesMeeting H.cell (frontier D) →
      ∀ b ∈ verticesMeeting H.cell D, b ∈ verticesMeeting H.cell (frontier D) →
        |g a - g b| ≤ C' * max ε (dist (pt a) (pt b)) ^ χ)
    (hbdM : ∀ a ∈ verticesMeeting H.cell D, a ∈ verticesMeeting H.cell (frontier D) → |g a| ≤ M) :
    ∀ x ∈ verticesMeeting H.cell D, ∀ y ∈ verticesMeeting H.cell D,
      |g x - g y| ≤ theorem15DiscreteConst p C₁ ξ₁ β q χ C' M *
        max ε (dist (pt x) (pt y)) ^ theorem15DiscreteExponent p ξ₁ β q χ := by
  intro x hx y hy
  unfold theorem15DiscreteConst theorem15DiscreteExponent
  have hq : 0 < q := lt_of_lt_of_le hβ hβq
  have hβ1 : β ≤ 1 := hβq.trans hq1
  set ξ := theorem15Exponent p ξ₁ β q χ
  have hξ : 0 < ξ := theorem15Exponent_pos hp hξ₁ hβ hq hχ
  set A₀ := theorem15Const p C₁ ξ₁ β q χ C' M
  set K := theorem15MainConst p C₁ ξ₁ χ C' M with hKdef
  set w := max ε (dist (pt x) (pt y))
  have hw0 : 0 < w := lt_of_lt_of_le hε0 (le_max_left _ _)
  set w₀ := theorem15Threshold β with hw₀def
  have hw₀0 : 0 < w₀ := Real.rpow_pos_of_pos (by norm_num) _
  have hw₀1 : w₀ ≤ 1 := Real.rpow_le_one (by norm_num) (by norm_num) (by positivity)
  have hgM := abs_le_of_discreteBoundary H hconn hDo hDb hharm hbdM
  have hdiff : |g x - g y| ≤ 2 * M := by
    have h1 := abs_le.mp (hgM x hx)
    have h2 := abs_le.mp (hgM y hy)
    rw [abs_le]
    constructor <;> linarith
  have hKA : K ≤ A₀ := le_max_left _ _
  have hwξ0 : 0 ≤ w ^ ξ := Real.rpow_nonneg hw0.le _
  rcases le_or_gt w₀ w with hww | hww
  · -- the trivial range `w ≥ w₀`
    have h1 : w₀ ^ ξ ≤ w ^ ξ := Real.rpow_le_rpow hw₀0.le hww hξ.le
    have h2 : 0 < w₀ ^ ξ := Real.rpow_pos_of_pos hw₀0 ξ
    have h3 : 2 * M / w₀ ^ ξ ≤ A₀ := le_max_right _ _
    calc |g x - g y| ≤ 2 * M := hdiff
      _ = (2 * M / w₀ ^ ξ) * w₀ ^ ξ := by field_simp
      _ ≤ (2 * M / w₀ ^ ξ) * w ^ ξ := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ A₀ * w ^ ξ := mul_le_mul_of_nonneg_right h3 hwξ0
  · -- the main range `w < w₀ ≤ 1`
    have hw1 : w < 1 := lt_of_lt_of_le hww hw₀1
    set τ := w ^ (β / 4) with hτdef
    have hτ0 : 0 < τ := Real.rpow_pos_of_pos hw0 _
    have hτ4 : τ ^ 4 = w ^ β := by
      rw [hτdef, ← Real.rpow_natCast, ← Real.rpow_mul hw0.le]
      norm_num
    have hτ1 : τ < 1 / 2 := by
      have h1 : τ < w₀ ^ (β / 4) := Real.rpow_lt_rpow hw0.le hww (by positivity)
      have h2 : w₀ ^ (β / 4) = 1 / 2 := by
        rw [hw₀def, theorem15Threshold, ← Real.rpow_mul (by norm_num),
          show (1 / β) * (β / 4) = (1 / 4 : ℝ) by field_simp,
          show (1 / 16 : ℝ) = (1 / 2) ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
        norm_num
      linarith
    have hdw : dist (pt x) (pt y) ≤ w ^ β :=
      calc dist (pt x) (pt y) ≤ w := le_max_right _ _
        _ = w ^ (1 : ℝ) := (Real.rpow_one w).symm
        _ ≤ w ^ β := Real.rpow_le_rpow_of_exponent_ge hw0 hw1.le hβ1
    have hδ : max (ε ^ β) (dist (pt x) (pt y)) ≤ τ ^ 4 := by
      rw [hτ4]
      exact max_le (Real.rpow_le_rpow hε0.le (le_max_left _ _) hβ.le) hdw
    have hεq : ε ^ q ≤ ε ^ β := Real.rpow_le_rpow_of_exponent_ge hε0 hε1 hβq
    have hεq1 : ε ≤ ε ^ q := by
      have h := Real.rpow_le_rpow_of_exponent_ge hε0 hε1 hq1
      rwa [Real.rpow_one] at h
    have hconv : ∀ e : ℝ, ξ ≤ e → w ^ e ≤ w ^ ξ := fun e he =>
      Real.rpow_le_rpow_of_exponent_ge hw0 hw1.le he
    -- the three powers of `τ`
    have hP1 : (τ ^ 2) ^ holderExponent p ≤ w ^ ξ := by
      have : (τ ^ 2) ^ holderExponent p = w ^ (β * holderExponent p / 2) := by
        rw [hτdef, ← Real.rpow_natCast, ← Real.rpow_mul hw0.le, ← Real.rpow_mul hw0.le]
        congr 1
        push_cast
        ring
      rw [this]
      exact hconv _ ((min_le_left _ _).trans (min_le_left _ _))
    have hP2 : (5 * τ) ^ χ ≤ 5 ^ χ * w ^ ξ := by
      rw [Real.mul_rpow (by norm_num) hτ0.le]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have : τ ^ χ = w ^ (β * χ / 4) := by
        rw [hτdef, ← Real.rpow_mul hw0.le]
        congr 1
        ring
      rw [this]
      exact hconv _ ((min_le_left _ _).trans (min_le_right _ _))
    have hP3 : τ ^ ξ₁ ≤ w ^ ξ := by
      have : τ ^ ξ₁ = w ^ (β * ξ₁ / 4) := by
        rw [hτdef, ← Real.rpow_mul hw0.le]
        congr 1
        ring
      rw [this]
      exact hconv _ ((min_le_right _ _).trans (min_le_left _ _))
    have hK0 : 0 ≤ 3 ^ χ * C' := mul_nonneg (by positivity) hC'
    have hA0 : 0 ≤ holderConst p * M := mul_nonneg (holderConst_pos p).le hM
    have hB0 : 0 ≤ 5 ^ χ * C' := mul_nonneg (by positivity) hC'
    have hC0 : 0 ≤ (1 + 2 ^ ξ₁) * (C₁ * M) := mul_nonneg (by positivity) (mul_nonneg hC₁ hM)
    -- the bound of an interior vertex, in terms of `w`
    have hint : holderConst p * M * (τ ^ 2) ^ holderExponent p + 2 * (C' * (5 * τ) ^ χ) +
        (1 + 2 ^ ξ₁) * (C₁ * M * τ ^ ξ₁) ≤ A₀ * w ^ ξ := by
      have e1 : holderConst p * M * (τ ^ 2) ^ holderExponent p ≤ holderConst p * M * w ^ ξ :=
        mul_le_mul_of_nonneg_left hP1 hA0
      have e2 : 2 * (C' * (5 * τ) ^ χ) ≤ 2 * (5 ^ χ * C') * w ^ ξ := by
        have h := mul_le_mul_of_nonneg_left hP2 hC'
        calc 2 * (C' * (5 * τ) ^ χ) ≤ 2 * (C' * (5 ^ χ * w ^ ξ)) := by linarith only [h]
          _ = 2 * (5 ^ χ * C') * w ^ ξ := by ring
      have e3 : (1 + 2 ^ ξ₁) * (C₁ * M * τ ^ ξ₁) ≤ (1 + 2 ^ ξ₁) * (C₁ * M) * w ^ ξ := by
        have h := mul_le_mul_of_nonneg_left hP3 (mul_nonneg hC₁ hM)
        have h2 : (0 : ℝ) ≤ 1 + 2 ^ ξ₁ := by positivity
        calc (1 + 2 ^ ξ₁) * (C₁ * M * τ ^ ξ₁) ≤ (1 + 2 ^ ξ₁) * (C₁ * M * w ^ ξ) :=
              mul_le_mul_of_nonneg_left h h2
          _ = (1 + 2 ^ ξ₁) * (C₁ * M) * w ^ ξ := by ring
      have e4 : 0 ≤ 3 ^ χ * C' * w ^ ξ := mul_nonneg hK0 hwξ0
      have eK : K * w ^ ξ = 3 ^ χ * C' * w ^ ξ + holderConst p * M * w ^ ξ +
          2 * (5 ^ χ * C') * w ^ ξ + (1 + 2 ^ ξ₁) * (C₁ * M) * w ^ ξ := by
        rw [hKdef, theorem15MainConst]; ring
      have eA := mul_le_mul_of_nonneg_right hKA hwξ0
      linarith only [e1, e2, e3, e4, eK, eA]
    by_cases hxA : x ∈ verticesMeeting H.cell (frontier D)
    · by_cases hyA : y ∈ verticesMeeting H.cell (frontier D)
      · -- case 1: two boundary vertices, the discrete Hölder data
        have h := abs_sub_le_of_discreteBdry H pt hpt hC' hχ hbdry hx hxA hy hyA (hsmall x hx)
          (hsmall y hy) hεq1 (hpt x) (hpt y)
        have h1 : 2 * ε ^ q + dist (pt x) (pt y) ≤ 3 * w ^ q := by
          have a1 : ε ^ q ≤ w ^ q := Real.rpow_le_rpow hε0.le (le_max_left _ _) hq.le
          have a2 : dist (pt x) (pt y) ≤ w ^ q :=
            calc dist (pt x) (pt y) ≤ w := le_max_right _ _
              _ = w ^ (1 : ℝ) := (Real.rpow_one w).symm
              _ ≤ w ^ q := Real.rpow_le_rpow_of_exponent_ge hw0 hw1.le hq1
          linarith
        have h2 : (2 * ε ^ q + dist (pt x) (pt y)) ^ χ ≤ 3 ^ χ * w ^ ξ := by
          calc (2 * ε ^ q + dist (pt x) (pt y)) ^ χ ≤ (3 * w ^ q) ^ χ :=
                Real.rpow_le_rpow (by positivity) h1 hχ.le
            _ = 3 ^ χ * w ^ (q * χ) := by
                rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hw0.le]
            _ ≤ 3 ^ χ * w ^ ξ :=
                mul_le_mul_of_nonneg_left (hconv _ ((min_le_right _ _).trans (min_le_right _ _)))
                  (by positivity)
        have h3 : |g x - g y| ≤ 3 ^ χ * C' * w ^ ξ := by
          calc |g x - g y| ≤ C' * (2 * ε ^ q + dist (pt x) (pt y)) ^ χ := h
            _ ≤ C' * (3 ^ χ * w ^ ξ) := mul_le_mul_of_nonneg_left h2 hC'
            _ = 3 ^ χ * C' * w ^ ξ := by ring
        have h4 : 3 ^ χ * C' * w ^ ξ ≤ K * w ^ ξ := by
          refine mul_le_mul_of_nonneg_right ?_ hwξ0
          rw [hKdef, theorem15MainConst]
          linarith only [hA0, hB0, hC0]
        linarith only [h3, h4, mul_le_mul_of_nonneg_right hKA hwξ0]
      · -- case 4: `x` boundary, `y` interior — exchange the roles
        have hδ' : max (ε ^ β) (dist (pt y) (pt x)) ≤ τ ^ 4 := by rwa [dist_comm]
        have h := abs_sub_le_of_interior_discreteBoundary H hconn pt hpt hDo hDb hε0 hεq1 hεq hp hC₁ hξ₁
          hsmall h335 h331 hC' hχ hM hharm hbdry hbdM hy hyA hx hτ0 hτ1 hδ'
        rw [abs_sub_comm] at h
        linarith only [h, hint]
    · -- cases 2–3: `x` interior
      have h := abs_sub_le_of_interior_discreteBoundary H hconn pt hpt hDo hDb hε0 hεq1 hεq hp hC₁ hξ₁
        hsmall h335 h331 hC' hχ hM hharm hbdry hbdM hx hxA hy hτ0 hτ1 hδ
      linarith only [h, hint]

/-- **[18] Theorem 1.5 / (3.33) with discrete boundary data, with the constant `max C₀ (A₀ M)`**: under the
hypotheses of `theorem15_deterministic_discreteBoundary`, for all `x, y ∈ V(D)`,
`|g(x) − g(y)| ≤ max C₀ (A₀ M) (ε ∨ |pt x − pt y|)^ξ'` with `C₀ = theorem15DiscreteBdryConst χ C'` and
`A₀ = theorem15DiscreteMassConst p C₁ ξ₁`. -/
theorem theorem15_deterministic_discreteBoundary_max (hconn : G.adj.Connected) (pt : V → ℂ)
    (hpt : ∀ v, pt v ∈ H.cell v) {D : Set ℂ} (hDo : IsOpen D) (hDb : Bornology.IsBounded D)
    {ε β q p C₁ ξ₁ : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hβ : 0 < β) (hβq : β ≤ q) (hq1 : q ≤ 1)
    (hp : 0 < p) (hC₁ : 0 ≤ C₁) (hξ₁ : 0 < ξ₁)
    (hsmall : ∀ v ∈ verticesMeeting H.cell D, diam (H.cell v) ≤ ε ^ q)
    (h335 : ∀ (z : ℂ) (r : ℝ), ε ^ β ≤ r → ball z (2 * r) ⊆ D → ∀ v ∈ verticesMeeting H.cell (ball z r),
      ENNReal.ofReal p ≤ G.walkLaw v {ω | DiscEvent G H.cell z r (G.vertexPath ω)})
    (h331 : BoundaryEstimate G H.cell pt D (ε ^ β) C₁ ξ₁)
    {g : V → ℝ} {C' χ M : ℝ} (hC' : 0 ≤ C') (hχ : 0 < χ) (hM : 0 ≤ M)
    (hharm : ∀ v ∈ verticesMeeting H.cell D, v ∉ verticesMeeting H.cell (frontier D) → GMS3.lap G g v = 0)
    (hbdry : ∀ a ∈ verticesMeeting H.cell D, a ∈ verticesMeeting H.cell (frontier D) →
      ∀ b ∈ verticesMeeting H.cell D, b ∈ verticesMeeting H.cell (frontier D) →
        |g a - g b| ≤ C' * max ε (dist (pt a) (pt b)) ^ χ)
    (hbdM : ∀ a ∈ verticesMeeting H.cell D, a ∈ verticesMeeting H.cell (frontier D) → |g a| ≤ M) :
    ∀ x ∈ verticesMeeting H.cell D, ∀ y ∈ verticesMeeting H.cell D,
      |g x - g y| ≤ max (theorem15DiscreteBdryConst χ C') (theorem15DiscreteMassConst p C₁ ξ₁ * M) *
        max ε (dist (pt x) (pt y)) ^ theorem15DiscreteExponent p ξ₁ β q χ := by
  intro x hx y hy
  refine (theorem15_deterministic_discreteBoundary H hconn pt hpt hDo hDb hε0 hε1 hβ hβq hq1 hp hC₁ hξ₁
    hsmall h335 h331 hC' hχ hM hharm hbdry hbdM x hx y hy).trans ?_
  exact mul_le_mul_of_nonneg_right (theorem15DiscreteConst_le hβ hC₁ hM)
    (Real.rpow_nonneg (le_max_of_le_left hε0.le) _)

end MatedCRTHarmonic.GMSMain.T15B
