/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Shortcut2Out at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Shortcut2Eq541

/-!
# GM §5.5, proof of Lemma 5.14: `P̄^φ` and its length bound (5.40)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`
(task P2-M2M2, WP-M2m, row 16 of `blueprint/M2.md`).

GM l. 3426–3431: "Since `φ` is supported on `B_{3r}(0)`, the definitions of `σ_r`, `σ̂_r`,
`𝓑_{σ_r}(𝕫; D_h)`, `𝓑_{σ̂_r}(𝕨; D_h)` are unaffected if we replace `h` by `h − φ`. Since `P̄^φ` is
the `D_{h−φ}`-shortest path between these metric balls, Lemma 5.13 implies (5.40)."
Here `σ = D_h(𝕫, 𝕩')`, `σ̂ = D_h(𝕨, 𝕪')` (hitting points), `P̄^φ` = the times `t` with
`D_h(𝕫, P^φ(t)) ≥ σ` and `D_h(𝕨, P^φ(t)) ≥ σ̂`.
* `weyl_ge_min_m2m2`: `(e^{ξ f}·D)(z, b) ≥ e^a min(D(z, b), D(z, Vᶜ))` if `ξ f ≥ a` on open `V`.
* `weyl_le_self_m2m2`: `e^{ξ f}·D ≤ D` if `ξ f ≤ 0` (`D` a length metric).
* `gm_out_close`: two times of `P̄^φ` are at `D_{h−φ}`-distance at most `D_{h−φ}(𝕩', 𝕪')`
  (the content of (5.40) used in GM's proof of Lemma 5.14).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric EMetric
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint MetricGeometry

/-- Weyl scaling locality: `(e^{ξ f}·D)(z,b) ≥ e^a min(D(z,b), D(z, Vᶜ))` if `ξ f ≥ a` on `V` -/
lemma weyl_ge_min_m2m2 {D D' : ContMetric} {ξ : ℝ} {f : C(ℂ, ℝ)}
    (hD' : ∀ x y : ℂ, ENNReal.ofReal (D'.1 (x, y)) = weylScale ξ f D x y) {V : Set ℂ}
    (hV : IsOpen V) {a : ℝ} (ha : ∀ x ∈ V, a ≤ ξ * f x) (z b : ℂ) :
    ENNReal.ofReal (Real.exp a) *
        min (ENNReal.ofReal (D.1 (z, b))) (infEDist (D.pt z) (D.pt '' Vᶜ)) ≤
      ENNReal.ofReal (D'.1 (z, b)) := by
  rw [hD']
  by_cases hlt : weylScale ξ f D z b < ENNReal.ofReal (Real.exp a) * infEDist (D.pt z) (D.pt '' Vᶜ)
  · have h1 := weylScaleOn_le_weylScale_of_lt (U := V) hV subset_rfl ha hlt
    have h2 : ENNReal.ofReal (Real.exp a) * D.internal V z b ≤ weylScaleOn ξ f D V z b :=
      le_weylScaleOn_of_le ha
    have h3 := ofReal_le_internal_m2m D V z b
    calc ENNReal.ofReal (Real.exp a) *
          min (ENNReal.ofReal (D.1 (z, b))) (infEDist (D.pt z) (D.pt '' Vᶜ))
        ≤ ENNReal.ofReal (Real.exp a) * D.internal V z b := by
          gcongr; exact (min_le_left _ _).trans h3
      _ ≤ _ := h2.trans h1
  · push_neg at hlt
    exact (mul_le_mul_of_nonneg_left (min_le_right _ _) zero_le).trans hlt

/-- `e^{ξ f}·D ≤ D` when `ξ f ≤ 0` and `D` is a length metric -/
lemma weyl_le_self_m2m2 {D D' : ContMetric} {ξ : ℝ} {f : C(ℂ, ℝ)}
    (hD' : ∀ x y : ℂ, ENNReal.ofReal (D'.1 (x, y)) = weylScale ξ f D x y) (hlen : D.IsLength)
    (hf : ∀ x, ξ * f x ≤ 0) (a b : ℂ) : D'.1 (a, b) ≤ D.1 (a, b) := by
  have h := weylScaleOn_le_of_le (U := univ) (b := 0) (ξ := ξ) (f := f) (D := D) (z := a) (w := b)
    (fun x _ => hf x)
  rw [weylScaleOn_univ, ← hD', Real.exp_zero, ENNReal.ofReal_one, one_mul] at h
  have hu : D.internal univ a b = ENNReal.ofReal (D.1 (a, b)) := by
    unfold ContMetric.internal
    rw [image_univ_of_surjective (f := D.pt) (fun x => ⟨x, rfl⟩),
      internalEDist_univ_of_isLengthSpace hlen,
      edist_dist]
    rfl
  rw [hu] at h
  exact (ENNReal.ofReal_le_ofReal_iff (nonneg_m2m D a b)).1 h

/-- the hitting point gives `D(𝕫, cl B_{3r}(0)) = σ`: `σ ≤ D(𝕫, ·)` on `cl B_{3r}(0)` -/
lemma hit_le_infEDist_m2m2 {D : ContMetric} {z x' : ℂ} {r : ℝ} (hx : IsHitPt D z x' r) :
    ENNReal.ofReal (D.1 (z, x')) ≤ infEDist (D.pt z) (D.pt '' (closedBall (0 : ℂ) (3 * r))) := by
  refine le_infEDist.2 ?_
  rintro _ ⟨c, hc, rfl⟩
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal (hx.2 c hc)

/-- locality of the hitting balls: if `ξ f = 0` off `cl B_{3r}(0)` (`φ` is supported in
`B_{3r}(0)`), then `D_{h−φ}(𝕫, b) ≥ σ` whenever `D_h(𝕫, b) ≥ σ` -/
lemma hit_ball_local_m2m2 {D D' : ContMetric} {ξ : ℝ} {f : C(ℂ, ℝ)}
    (hD' : ∀ x y : ℂ, ENNReal.ofReal (D'.1 (x, y)) = weylScale ξ f D x y) {r : ℝ}
    (hf0 : ∀ x ∉ closedBall (0 : ℂ) (3 * r), ξ * f x = 0) {z x' b : ℂ} (hx : IsHitPt D z x' r)
    (hb : D.1 (z, x') ≤ D.1 (z, b)) : D.1 (z, x') ≤ D'.1 (z, b) := by
  have h := weyl_ge_min_m2m2 hD' (isClosed_closedBall.isOpen_compl) (a := 0)
    (fun x hx => (hf0 x hx).ge) z b
  rw [Real.exp_zero, ENNReal.ofReal_one, one_mul, compl_compl] at h
  have h2 : ENNReal.ofReal (D.1 (z, x')) ≤
      min (ENNReal.ofReal (D.1 (z, b))) (infEDist (D.pt z) (D.pt '' closedBall 0 (3 * r))) :=
    le_min (ENNReal.ofReal_le_ofReal hb) (hit_le_infEDist_m2m2 hx)
  exact (ENNReal.ofReal_le_ofReal_iff (nonneg_m2m D' z b)).1 (h2.trans h)

/-- **GM (5.40)** (l. 3426–3431), in the form used in the proof of Lemma 5.14: for two times
`s, t` of `P̄^φ` (outside both hitting balls), `D_{h−φ}(P^φ(s), P^φ(t)) ≤ D_{h−φ}(𝕩', 𝕪')`. -/
theorem gm_out_close {D D' : ContMetric} {ξ : ℝ} {f : C(ℂ, ℝ)}
    (hD' : ∀ x y : ℂ, ENNReal.ofReal (D'.1 (x, y)) = weylScale ξ f D x y) (hlen : D.IsLength)
    (hf : ∀ x, ξ * f x ≤ 0) {r : ℝ} (hf0 : ∀ x ∉ closedBall (0 : ℂ) (3 * r), ξ * f x = 0)
    {z w x' y' : ℂ} (hx : IsHitPt D z x' r) (hy : IsHitPt D w y' r) {Qφ : C(unitInterval, ℂ)}
    (hQ : IsGeod01 D' z w Qφ) {s t : unitInterval}
    (hs : D.1 (z, x') ≤ D.1 (z, Qφ s) ∧ D.1 (w, y') ≤ D.1 (w, Qφ s))
    (ht : D.1 (z, x') ≤ D.1 (z, Qφ t) ∧ D.1 (w, y') ≤ D.1 (w, Qφ t)) :
    D'.1 (Qφ s, Qφ t) ≤ D'.1 (x', y') := by
  set L := D'.1 (z, w)
  have hz : ∀ τ : unitInterval, D'.1 (z, Qφ τ) = τ * L := fun τ => by
    have := hQ.2.2 0 τ
    rw [hQ.1] at this
    rw [this, Set.Icc.coe_zero, sub_zero, abs_of_nonneg τ.2.1]
  have hw : ∀ τ : unitInterval, D'.1 (w, Qφ τ) = (1 - τ) * L := fun τ => by
    have := hQ.2.2 τ 1
    rw [hQ.2.1, dist_comm_m2m] at this
    rw [this, Set.Icc.coe_one, abs_of_nonneg (sub_nonneg.2 τ.2.2)]
  -- the length bound `L ≤ σ + D'(x', y') + σ̂`
  have hL : L ≤ D.1 (z, x') + D'.1 (x', y') + D.1 (w, y') := by
    have t1 := dist_triangle_m2m D' z x' w
    have t2 := dist_triangle_m2m D' x' y' w
    have t3 := weyl_le_self_m2m2 hD' hlen hf z x'
    have t4 := weyl_le_self_m2m2 hD' hlen hf y' w
    have t5 := dist_comm_m2m D w y'
    linarith
  have hs1 := hit_ball_local_m2m2 hD' hf0 hx hs.1
  have hs2 := hit_ball_local_m2m2 hD' hf0 hy hs.2
  have ht1 := hit_ball_local_m2m2 hD' hf0 hx ht.1
  have ht2 := hit_ball_local_m2m2 hD' hf0 hy ht.2
  rw [hz] at hs1 ht1
  rw [hw] at hs2 ht2
  rw [hQ.2.2 s t]
  rcases le_total (s : ℝ) t with h | h
  · rw [abs_of_nonneg (sub_nonneg.2 h)]; nlinarith
  · rw [abs_of_nonpos (sub_nonpos.2 h)]; nlinarith

end LQGMetric.GM
