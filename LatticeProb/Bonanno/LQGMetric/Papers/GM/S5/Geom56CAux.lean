/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Geom56CAux at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom56CIneq
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom56CBox
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.ShortcutDist

/-!
# GM Lemma 5.6: auxiliary planar facts for the tube assembly (task P2-M2L56b)

GM = Gwynne–Miller, arXiv:1905.00383, `uniqueness-final.tex`, proof of Lemma 5.6 (l. 2963–2989).
Elementary facts used to check the hypotheses of `sepDiscNear_of_layout` for GM's tube:
`closure H` lies in the closed annulus; points of a corridor are within `A + W` of its centre;
the far-end coordinates of corridor points outside `B_{19s}(u)`; segments with a moved end point
stay close to the original segment; a linear functional bound along a segment; points of squares
meeting `X` are within `2s` of `X`; `X ⊆ tubeOf s F` when `F` contains the squares meeting `X`.
Own elementary arguments.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric

namespace LQGMetric.GM
open Blueprint

lemma closure_halfAnnulus_subset {H : Set ℂ} {z : ℂ} {r₁ r₂ : ℝ} (hH : IsHalfAnnulus H z r₁ r₂) :
    closure H ⊆ {w : ℂ | r₁ ≤ ‖w - z‖ ∧ ‖w - z‖ ≤ r₂} := by
  obtain ⟨e, -, rfl⟩ := hH
  refine closure_minimal ?_ ?_
  · rintro w ⟨⟨h1, h2⟩, -⟩; exact ⟨h1.le, h2.le⟩
  · exact (isClosed_le continuous_const (continuous_id.sub continuous_const).norm).inter
      (isClosed_le (continuous_id.sub continuous_const).norm continuous_const)

lemma norm_le_rectC {c e w : ℂ} {A W : ℝ} (he : ‖e‖ = 1) (hw : w ∈ rectC c e A W) :
    ‖w - c‖ ≤ A + W := by
  rw [← norm_mul_conj_unit he]
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (add_le_add hw.1 hw.2)

/-- corridor points outside `B_{19 s}(u)` lie at depth `∈ [17 s, 100 s]` behind `u` -/
lemma rect_far_end {c e u x : ℂ} {s : ℝ} (hs : 0 < s) (he : ‖e‖ = 1)
    (hx : x ∈ rectC c e (50 * s) (2 * s))
    (hξ1 : 48.5 * s ≤ ((u - c) * (starRingEnd ℂ) e).re)
    (hξ2 : ((u - c) * (starRingEnd ℂ) e).re ≤ 49.5 * s)
    (hη : |((u - c) * (starRingEnd ℂ) e).im| ≤ s / 2) (hxu : 19 * s ≤ ‖x - u‖) :
    17 * s ≤ ((u - c) * (starRingEnd ℂ) e).re - ((x - c) * (starRingEnd ℂ) e).re ∧
      ((u - c) * (starRingEnd ℂ) e).re - ((x - c) * (starRingEnd ℂ) e).re ≤ 100 * s ∧
      |((u - c) * (starRingEnd ℂ) e).im - ((x - c) * (starRingEnd ℂ) e).im| ≤ 3 * s := by
  obtain ⟨hx1, hx2⟩ := hx
  rw [abs_le] at hx1 hx2 hη
  set ξ := ((u - c) * (starRingEnd ℂ) e).re
  set η := ((u - c) * (starRingEnd ℂ) e).im
  set t := ((x - c) * (starRingEnd ℂ) e).re
  set σ := ((x - c) * (starRingEnd ℂ) e).im
  have hd : ‖x - u‖ ^ 2 = (t - ξ) ^ 2 + (σ - η) ^ 2 := by
    have : (x - u) * (starRingEnd ℂ) e = (x - c) * (starRingEnd ℂ) e - (u - c) * (starRingEnd ℂ) e := by
      ring
    rw [← norm_mul_conj_unit he, norm_sq_re_im, this]
    simp only [Complex.sub_re, Complex.sub_im, t, ξ, σ, η]
  have hδ : |η - σ| ≤ 3 * s := abs_le.2 ⟨by linarith, by linarith⟩
  refine ⟨?_, by linarith, hδ⟩
  have h19 : (19 * s) ^ 2 ≤ ‖x - u‖ ^ 2 := pow_le_pow_left₀ (by positivity) hxu 2
  have hσ2 : (σ - η) ^ 2 ≤ (3 * s) ^ 2 := by
    rw [← sq_abs, abs_sub_comm]; exact pow_le_pow_left₀ (abs_nonneg _) hδ 2
  by_contra hc
  rw [not_le] at hc
  have h1 : (t - ξ) ^ 2 < (17 * s) ^ 2 := by
    apply sq_lt_sq' <;> linarith
  nlinarith

/-- moving one end point of a segment moves the segment by at most that much -/
lemma segment_near {a a' b q : ℂ} (hq : q ∈ segment ℝ a b) :
    ∃ q' ∈ segment ℝ a' b, dist q q' ≤ dist a a' := by
  obtain ⟨t₁, t₂, h1, h2, h12, rfl⟩ := hq
  refine ⟨t₁ • a' + t₂ • b, ⟨t₁, t₂, h1, h2, h12, rfl⟩, ?_⟩
  rw [dist_eq_norm, dist_eq_norm]
  have : t₁ • a + t₂ • b - (t₁ • a' + t₂ • b) = t₁ • (a - a') := by
    simp only [smul_sub]; abel
  rw [this, norm_smul, Real.norm_of_nonneg h1]
  have : t₁ ≤ 1 := by linarith
  exact mul_le_of_le_one_left (norm_nonneg _) this

/-- a lower bound for a real-affine functional along a segment -/
lemma segment_re_ge {a b q w : ℂ} {M : ℝ} (hq : q ∈ segment ℝ a b) (ha : M ≤ (a * w).re)
    (hb : M ≤ (b * w).re) : M ≤ (q * w).re := by
  obtain ⟨t₁, t₂, h1, h2, h12, rfl⟩ := hq
  have : ((t₁ • a + t₂ • b) * w).re = t₁ * (a * w).re + t₂ * (b * w).re := by
    simp only [Complex.real_smul, add_mul, mul_assoc, Complex.add_re, Complex.re_ofReal_mul]
  rw [this]
  have := mul_le_mul_of_nonneg_left ha h1
  have := mul_le_mul_of_nonneg_left hb h2
  have hM : M = t₁ * M + t₂ * M := by rw [← add_mul, h12, one_mul]
  linarith

/-- `Re (q conj w) ≤ ‖q‖ ‖w‖` -/
lemma re_mul_conj_le (q w : ℂ) : (q * (starRingEnd ℂ) w).re ≤ ‖q‖ * ‖w‖ := by
  refine (Complex.re_le_norm _).trans ?_
  rw [norm_mul, Complex.norm_conj]

/-- points of a square meeting `X` are within `3 s` of `X` -/
lemma exists_near_of_mem_sq {s : ℝ} (hs : 0 < s) {X : Set ℂ} {m : ℤ × ℤ} (hm : m ∈ squareSet s X)
    {x : ℂ} (hx : x ∈ gridSquare s m) : ∃ p ∈ X, dist x p ≤ 3 * s := by
  obtain ⟨p, hpS, hpX⟩ := hm
  exact ⟨p, hpX, (mem_ball.1 (gridSquare_subset_ball hs hpS hx)).le⟩

lemma mem_sqF {s r : ℝ} (hs : 0 < s) (hr : 0 < r) {z : ℂ} {X : Set ℂ}
    (hX : X ⊆ closedBall z (2 * r)) {m : ℤ × ℤ} : m ∈ sqF s r z X ↔ m ∈ squareSet s X := by
  rw [← Finset.mem_coe, coe_sqF hs hr hX]

/-- `X` lies in the tube of any `F` containing the squares meeting `X` -/
lemma subset_tubeOf_of_sqF {s r : ℝ} (hs : 0 < s) (hr : 0 < r) {z : ℂ} {X : Set ℂ}
    (hX : X ⊆ closedBall z (2 * r)) {F : Finset (ℤ × ℤ)} (hF : sqF s r z X ⊆ F) :
    X ⊆ tubeOf s F := by
  refine (subset_interior_squares_m2m hs X).trans (interior_mono ?_)
  intro w hw
  rw [mem_iUnion₂] at hw ⊢
  obtain ⟨m, hm, hwm⟩ := hw
  exact ⟨m, hF ((mem_sqF hs hr hX).2 hm), hwm⟩

/-- `X` is covered by the squares meeting it -/
lemma subset_iUnion_sqF {s r : ℝ} (hs : 0 < s) (hr : 0 < r) {z : ℂ} {X : Set ℂ}
    (hX : X ⊆ closedBall z (2 * r)) : X ⊆ ⋃ m ∈ sqF s r z X, gridSquare s m := by
  intro x hx
  rw [mem_iUnion₂]
  exact ⟨gridIdx s x, (mem_sqF hs hr hX).2 ⟨x, mem_gridSquare_gridIdx hs x, hx⟩,
    mem_gridSquare_gridIdx hs x⟩

/-- an axis within `45°` of a nonzero vector -/
lemma exists_axis' {X : ℂ} (hX : X ≠ 0) : ∃ e : ℂ, (e = 1 ∨ e = -1 ∨ e = Complex.I ∨
    e = -Complex.I) ∧ 7 / 10 * ‖X‖ ≤ (X * (starRingEnd ℂ) e).re := by
  have hn : 0 < ‖X‖ := norm_pos_iff.2 hX
  obtain ⟨e, he, h⟩ := exists_axis (ω := X / (‖X‖ : ℂ)) (by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hn.le, div_self hn.ne'])
  refine ⟨e, he, ?_⟩
  have : (X / (‖X‖ : ℂ) * (starRingEnd ℂ) e).re = (X * (starRingEnd ℂ) e).re / ‖X‖ := by
    rw [div_mul_eq_mul_div, Complex.div_ofReal_re]
  rw [this, le_div_iff₀ hn] at h
  linarith

lemma norm_axis {e : ℂ} (he : e = 1 ∨ e = -1 ∨ e = Complex.I ∨ e = -Complex.I) : ‖e‖ = 1 := by
  rcases he with rfl | rfl | rfl | rfl <;> simp

end LQGMetric.GM
