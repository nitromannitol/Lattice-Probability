/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.RegularityCond2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.RegularityCond2Det
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.RegularityCond4
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.RegularityCond5b
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightBlueprint
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.Subseq

/-!
# GM Lemma 4.11, condition 2 (comparison of `D_h`-balls and Euclidean balls)

Source: GM (arXiv:1905.00383v3) `uniqueness-final.tex`, proof of Lemma 4.11, l. 1984: "Again using
Axiom V, we can find a small enough `a ∈ (0,1)`, depending on `ℓ, V, p`, such that condition 2
(comparison of balls) holds with probability at least `1 − (1−p)/6`."

GM give no details. Own covering argument (P2-M2H item 1), with only the Axiom V consequences
`GMS2_4a` (distances across annuli, proved: `GM.Tight.blueprint_GMS2_4a`) and `GMS2_4b` (uniform
modulus of continuity, `GM.Tight.blueprint_GMS2_4b`) at the points `w` of the grid
`(ℓ𝕣/8)ℤ² ∩ cl B_{𝕣ρ₁}(0)` (a number of points independent of `𝕣`), and the continuity of the
circle-average process (condition 4 at the scales `𝕣` and `ℓ𝕣`, `gm_regC4_prob`):
for `z ∈ B_{4ℓ𝕣}(𝕣V)` and a grid point `w` with `|z − w| < ℓ𝕣/4`,
* `B_{a𝕣}(z) ⊂ B_{ℓ𝕣/2}(w)` has `D_h`-diameter `≤ (s₁/2) 𝔠_{ℓ𝕣}e^{ξh_{ℓ𝕣}(w)}`, while
  `τ_{ℓ𝕣}(z) ≥ D_h(across A_{ℓ𝕣/4, 3ℓ𝕣/4}(w)) ≥ s₁ 𝔠_{ℓ𝕣}e^{ξh_{ℓ𝕣}(w)}`;
* `τ_{2ℓ𝕣}(z) − τ_{ℓ𝕣}(z) ≥ D_h(across A_{5ℓ𝕣/4, 7ℓ𝕣/4}(w))` and
  `τ_{3ℓ𝕣}(z) − τ_{2ℓ𝕣}(z) ≥ D_h(across A_{9ℓ𝕣/4, 11ℓ𝕣/4}(w))`, each `≥ S 𝔠_r e^{ξh_r(w)}` for
  `r ∈ {𝕣, ℓ𝕣}`;
* `|h_r(z) − h_r(w)| ≤ 2M` for `r ∈ {𝕣, ℓ𝕣}` (continuous version `H`, D60).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- a lower bound for `D(scaleSet r w (cl B_κ), scaleSet r w ∂B_{κ'})` bounds the distance across
`A_{rκ, rκ'}(w)` -/
theorem gm_c2_cross {d : ContMetric} {w : ℂ} {r κ κ' t : ℝ} (hr : 0 < r) (hκ' : 0 < κ')
    (hS : ENNReal.ofReal t ≤ setDist d (scaleSet r w (closedBall 0 κ))
      (scaleSet r w (frontier (ball 0 κ')))) :
    ∀ u ∈ sphere w (r * κ), ∀ v ∈ sphere w (r * κ'), t ≤ d.1 (u, v) := by
  intro u hu v hv
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  have hmem : ∀ x : ℂ, x = (r : ℂ) * ((x - w) / r) + w := fun x => by field_simp; ring
  have hn : ∀ x : ℂ, ‖(x - w) / r‖ = ‖x - w‖ / r := fun x => by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  rw [mem_sphere, dist_eq_norm] at hu hv
  have hu' : u ∈ scaleSet r w (closedBall 0 κ) := ⟨(u - w) / r, by
    rw [mem_closedBall_zero_iff, hn, hu, mul_div_cancel_left₀ _ hr.ne'], (hmem u).symm⟩
  have hv' : v ∈ scaleSet r w (frontier (ball 0 κ')) := ⟨(v - w) / r, by
    rw [frontier_ball _ hκ'.ne', mem_sphere_zero_iff_norm, hn, hv,
      mul_div_cancel_left₀ _ hr.ne'], (hmem v).symm⟩
  have h1 := hS.trans ((MetricGeometry.setEDist_le_edist (mem_image_of_mem _ hu')
    (mem_image_of_mem _ hv')).trans (le_of_eq (edist_dist _ _)))
  exact (ENNReal.ofReal_le_ofReal_iff (dist_nonneg (x := d.pt u) (y := d.pt v))).1 h1

theorem gm_mem_scaleSet_closedBall {L κ : ℝ} (hL : 0 < L) {w u : ℂ} (hu : ‖u - w‖ ≤ L * κ) :
    u ∈ scaleSet L w (closedBall 0 κ) := by
  have hrc : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hL.ne'
  refine ⟨(u - w) / L, ?_, by field_simp; ring⟩
  rw [mem_closedBall_zero_iff, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL,
    div_le_iff₀ hL]
  linarith

/-- a point of `σℤ²` within `2σ` of `z` -/
theorem gm_exists_gridPt_near {σ : ℝ} (hσ : 0 < σ) (z : ℂ) :
    ∃ w ∈ gridPts σ, ‖z - w‖ < 2 * σ := by
  refine ⟨⟨⌊z.re / σ⌋ * σ, ⌊z.im / σ⌋ * σ⟩, ⟨⌊z.re / σ⌋, ⌊z.im / σ⌋, rfl⟩, ?_⟩
  have b1 := Int.floor_le (z.re / σ); have b2 := Int.lt_floor_add_one (z.re / σ)
  have b3 := Int.floor_le (z.im / σ); have b4 := Int.lt_floor_add_one (z.im / σ)
  rw [le_div_iff₀ hσ] at b1 b3
  rw [div_lt_iff₀ hσ] at b2 b4
  refine lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _) ?_
  simp only [Complex.sub_re, Complex.sub_im]
  rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
  linarith

section Det
variable {Ω : Type} {D : DistC → ContMetric} {h : Ω → DistC}

/-- `τ_r(z) ≥ t` if `t` bounds the distance across `A_{a',b'}(w)` and `|z − w| ≤ a'`,
`b' + |z − w| ≤ r` -/
theorem gm_c2_tau_cross {ω : Ω} (hlen : (D (h ω)).IsLength) {z w : ℂ} {r a' b' t : ℝ}
    (hr : 0 < r) (hz : ‖z - w‖ ≤ a') (hab : a' ≤ b') (hb : b' + ‖z - w‖ ≤ r)
    (hcross : ∀ u ∈ sphere w a', ∀ v ∈ sphere w b', t ≤ (D (h ω)).1 (u, v)) :
    t ≤ tauR D h z r ω := by
  refine gm_c2_tau_ge hr fun y hy => ?_
  have hyw : b' ≤ ‖y - w‖ := by
    have := norm_sub_le (y - w) (z - w)
    rw [show y - w - (z - w) = y - z by ring] at this; linarith
  exact Tight.le_of_forall_crossing hlen hab hz hyw hcross

/-- **the deterministic step of condition 2** at one centre `z` near a grid point `w` -/
theorem gm_c2_good {ω : Ω} (hlen : (D (h ω)).IsLength) {z w : ℂ} {L a b s₁ X Y : ℝ}
    (hL : 0 < L) (hzw : ‖z - w‖ < L / 4) (ha : a ≤ L / 4) (hab : a ≤ b * L) (hX : 0 < X)
    (hs₁ : 0 < s₁)
    (E1 : ∀ u ∈ sphere w (L * (1 / 4)), ∀ v ∈ sphere w (L * (3 / 4)), s₁ * X ≤ (D (h ω)).1 (u, v))
    (E2 : ∀ u ∈ scaleSet L w (closedBall 0 (1 / 2)), ∀ v ∈ scaleSet L w (closedBall 0 (1 / 2)),
      ‖u - v‖ ≤ b * L → (D (h ω)).1 (u, v) ≤ s₁ / 2 * X)
    (E3 : ∀ u ∈ sphere w (L * (5 / 4)), ∀ v ∈ sphere w (L * (7 / 4)), Y ≤ (D (h ω)).1 (u, v))
    (E5 : ∀ u ∈ sphere w (L * (9 / 4)), ∀ v ∈ sphere w (L * (11 / 4)), Y ≤ (D (h ω)).1 (u, v)) :
    ball z a ⊆ filledBall (D (h ω)) z (tauR D h z L ω) ∧
      Y ≤ min (tauR D h z (2 * L) ω - tauR D h z L ω)
        (tauR D h z (3 * L) ω - tauR D h z (2 * L) ω) := by
  have hzw0 := norm_nonneg (z - w)
  refine ⟨fun u hu => ?_, le_min ?_ ?_⟩
  · rw [mem_ball, dist_eq_norm] at hu
    have hτ := gm_c2_tau_cross hlen hL (le_of_lt (by linarith : ‖z - w‖ < L * (1 / 4)))
      (by nlinarith) (by linarith) E1
    have huw : ‖u - w‖ ≤ L * (1 / 2) := by
      have := norm_add_le (u - z) (z - w)
      rw [sub_add_sub_cancel] at this; linarith
    have hd := E2 z (gm_mem_scaleSet_closedBall hL (by linarith))
      u (gm_mem_scaleSet_closedBall hL huw) (by rw [norm_sub_rev]; linarith)
    have : (D (h ω)).1 (z, u) < tauR D h z L ω := by nlinarith
    exact Or.inl (subset_closure this)
  · have := gm_c2_incr hlen (z := z) (r₁ := L) (r₂ := 2 * L) hL (by linarith) (by linarith)
      (by nlinarith) E3
    linarith
  · have := gm_c2_incr hlen (z := z) (r₁ := 2 * L) (r₂ := 3 * L) (by linarith) (by linarith)
      (by linarith) (by nlinarith) E5
    linarith

end Det

end LQGMetric.GM
