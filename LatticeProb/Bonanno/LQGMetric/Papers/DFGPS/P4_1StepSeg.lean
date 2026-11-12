/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.P4_1StepSeg at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P4_1StepAnn

/-!
# DFGPS Proposition 4.1, Steps 2–3: the tube geometry for a line segment

DFGPS (arXiv:1905.00380), proof of Proposition 4.1, Step 2 (T:2486–2490) and the choice of the
intervals `[k₁, k₂]` in Step 3 (T:2502), for `L` a line segment `{a + σe : σ ∈ [0, ℓ]}`.
Centres at spacing `9ε` along the line (DFGPS: `6ε`; we use annuli `2ε𝕣 → 4ε𝕣`, DEV-P41-6);
blocks are the centres in a window `[(j−2)b/8, (j−1)b/8]` of the line parameter; "each path from
`u` to `v` in `B_{ε𝕣}(𝕣L)` must enter `B_{2ε𝕣}(z_k)`" is the intermediate value theorem for the
(1-Lipschitz) coordinate `q(y) = Re((y − 𝕣a) ē)/𝕣` along the path. Own elementary write-up of the
geometric facts DFGPS state without proof.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric

namespace LQGMetric.DFGPS.P41

open Blueprint

lemma dN_cast (i j : ℕ) : (dN i j : ℝ) = |(i : ℝ) - j| := by
  unfold dN
  rcases le_total i j with h | h
  · rw [Nat.sub_eq_zero_of_le h, zero_add, Nat.cast_sub h, abs_of_nonpos (by
      have : (i : ℝ) ≤ j := by exact_mod_cast h
      linarith)]
    ring
  · rw [Nat.sub_eq_zero_of_le h, add_zero, Nat.cast_sub h, abs_of_nonneg (by
      have : (j : ℝ) ≤ i := by exact_mod_cast h
      linarith)]

/-- the line coordinate at scale `r` -/
def lineCoord (a e : ℂ) (r : ℝ) (y : ℂ) : ℝ := ((y - r * a) * (starRingEnd ℂ) e).re / r

lemma lineCoord_lip {a e : ℂ} (he : ‖e‖ = 1) {r : ℝ} (hr : 0 < r) (y y' : ℂ) :
    |lineCoord a e r y - lineCoord a e r y'| ≤ ‖y - y'‖ / r := by
  unfold lineCoord
  rw [← sub_div, abs_div, abs_of_pos hr]
  refine div_le_div_of_nonneg_right ?_ hr.le
  rw [← Complex.sub_re, ← sub_mul, show y - r * a - (y' - r * a) = y - y' by ring]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, Complex.norm_conj, he, mul_one]

lemma lineCoord_pt {a e : ℂ} (he : ‖e‖ = 1) {r : ℝ} (hr : 0 < r) (s : ℝ) :
    lineCoord a e r (r * (a + s * e)) = s := by
  unfold lineCoord
  have : (r * (a + s * e) - r * a) * (starRingEnd ℂ) e = ((r * s : ℝ) : ℂ) * (‖e‖ ^ 2 : ℝ) := by
    rw [Complex.ofReal_pow, ← Complex.mul_conj', Complex.ofReal_mul]; ring
  rw [this, he, ← Complex.ofReal_mul, Complex.ofReal_re]
  field_simp

lemma norm_sub_pt {a e : ℂ} (he : ‖e‖ = 1) {r : ℝ} (hr : 0 < r) (s t : ℝ) :
    ‖(r : ℂ) * (a + s * e) - r * (a + t * e)‖ = r * |s - t| := by
  rw [show (r : ℂ) * (a + s * e) - r * (a + t * e) = ((r * (s - t) : ℝ) : ℂ) * e by
    push_cast; ring, norm_mul, he, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos hr]

/-- points of the tube are within `εr` of a point `r(a + σe)` with `σ ∈ [0, ℓ]` -/
lemma tube_near {a e : ℂ} {ℓ : ℝ} {L : Set ℂ} (hL : ∀ x ∈ L, ∃ σ ∈ Icc 0 ℓ, x = a + σ * e)
    {r ε : ℝ} {y : ℂ} (hy : y ∈ thickening (ε * r) (scaleSet r 0 L)) :
    ∃ σ ∈ Icc 0 ℓ, ‖y - r * (a + σ * e)‖ < ε * r := by
  rw [mem_thickening_iff] at hy
  obtain ⟨_, ⟨x, hx, rfl⟩, hd⟩ := hy
  obtain ⟨σ, hσ, rfl⟩ := hL x hx
  refine ⟨σ, hσ, ?_⟩
  rw [dist_eq_norm] at hd
  simpa only [add_zero] using hd

/-- a tube point with line coordinate `s` is within `2εr` of `r(a + se)` -/
lemma tube_coord_close {a e : ℂ} (he : ‖e‖ = 1) {ℓ : ℝ} {L : Set ℂ}
    (hL : ∀ x ∈ L, ∃ σ ∈ Icc 0 ℓ, x = a + σ * e) {r ε : ℝ} (hr : 0 < r) {y : ℂ}
    (hy : y ∈ thickening (ε * r) (scaleSet r 0 L)) {s : ℝ} (hs : lineCoord a e r y = s) :
    ‖y - r * (a + s * e)‖ < 2 * (ε * r) := by
  obtain ⟨σ, -, hσ⟩ := tube_near hL hy
  have h1 := lineCoord_lip (a := a) he hr y (r * (a + σ * e))
  rw [hs, lineCoord_pt he hr, le_div_iff₀ hr] at h1
  have h2 := norm_sub_pt (a := a) he hr σ s
  calc ‖y - r * (a + s * e)‖ ≤ ‖y - r * (a + σ * e)‖ + ‖(r : ℂ) * (a + σ * e) - r * (a + s * e)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε * r + ε * r := by
        rw [h2]
        have : r * |σ - s| = |s - σ| * r := by rw [abs_sub_comm]; ring
        linarith
    _ = 2 * (ε * r) := by ring

/-- `|u − v| ≤ r |q(u) − q(v)| + 4εr` for tube points -/
lemma tube_dist_le {a e : ℂ} (he : ‖e‖ = 1) {ℓ : ℝ} {L : Set ℂ}
    (hL : ∀ x ∈ L, ∃ σ ∈ Icc 0 ℓ, x = a + σ * e) {r ε : ℝ} (hr : 0 < r) {u v : ℂ}
    (hu : u ∈ thickening (ε * r) (scaleSet r 0 L)) (hv : v ∈ thickening (ε * r) (scaleSet r 0 L)) :
    ‖u - v‖ ≤ r * |lineCoord a e r u - lineCoord a e r v| + 4 * (ε * r) := by
  have h1 := tube_coord_close he hL hr hu rfl
  have h2 := tube_coord_close he hL hr hv rfl
  have h3 := norm_sub_pt (a := a) he hr (lineCoord a e r u) (lineCoord a e r v)
  calc ‖u - v‖ ≤ ‖u - r * (a + lineCoord a e r u * e)‖ +
        ‖(r : ℂ) * (a + lineCoord a e r u * e) - r * (a + lineCoord a e r v * e)‖ +
        ‖v - r * (a + lineCoord a e r v * e)‖ := by
        have := norm_sub_le_norm_sub_add_norm_sub u (r * (a + lineCoord a e r u * e)) v
        have h4 := norm_sub_le_norm_sub_add_norm_sub ((r : ℂ) * (a + lineCoord a e r u * e))
          (r * (a + lineCoord a e r v * e)) v
        rw [norm_sub_rev ((r : ℂ) * (a + lineCoord a e r v * e)) v] at h4
        linarith
    _ ≤ r * |lineCoord a e r u - lineCoord a e r v| + 4 * (ε * r) := by
        rw [h3]; linarith

end LQGMetric.DFGPS.P41
