import Mathlib

/-!
# Crossing data at an interior point of an edge

Let a set `γ ⊆ ℂ` agree, inside a disk `B(e, r)`, with a segment `[c, d]` through `e`, where `e` lies in the open
segment `(c, d)` and `r ≤ min ‖c - e‖ ‖d - e‖`. The diameter of the disk along `[c, d]` cuts it into two open
half-disks. They are convex, they cover `B(e, r) \ γ`, and both accumulate at every point of `γ ∩ B(e, r)`. A short
segment `[p, q]` through `e` perpendicular to `[c, d]` joins the two half-disks, meets `γ` only at `e`, and crosses a
short open subsegment `(c', d') ⊆ γ` transversally.

This is the local crossing configuration used for crosscuts that are polygonal near an interior point (Whyburn,
*Analytic Topology*, Chapter VI; Newman, *Elements of the topology of plane sets of points*, Chapter V).

* `transverseCoord e w z = Im (conj w * (z - e))`: `‖w‖` times the signed distance from `z` to the line `e + ℝ w`.
* `exists_crossing_data_of_inter_ball_eq_segment`: the two half-disks and the transverse segment.
-/

open Set Metric Complex ComplexConjugate

namespace LatticeProb.Topology

/-- The coordinate of `z` transverse to the line through `e` with direction `w`, namely `Im (conj w * (z - e))`;
it equals `‖w‖` times the signed distance from `z` to that line. -/
noncomputable def transverseCoord (e w z : ℂ) : ℝ := (conj w * (z - e)).im

theorem transverseCoord_self (e w : ℂ) : transverseCoord e w e = 0 := by
  simp [transverseCoord]

/-- Moving along the direction `w` does not change the transverse coordinate. -/
theorem transverseCoord_add_smul (e w z : ℂ) (t : ℝ) :
    transverseCoord e w (z + t • w) = transverseCoord e w z := by
  unfold transverseCoord
  have h : conj w * (z + t • w - e) = conj w * (z - e) + ((t * ‖w‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.real_smul]
    push_cast
    linear_combination (t : ℂ) * conj_mul' w
  rw [h, add_im, ofReal_im, add_zero]

/-- Moving along the normal direction `I * w` changes the transverse coordinate by `t ‖w‖ ^ 2`. -/
theorem transverseCoord_add_smul_I_mul (e w z : ℂ) (t : ℝ) :
    transverseCoord e w (z + t • (I * w)) = transverseCoord e w z + t * ‖w‖ ^ 2 := by
  unfold transverseCoord
  have h : conj w * (z + t • (I * w) - e) = conj w * (z - e) + ((t * ‖w‖ ^ 2 : ℝ) : ℂ) * I := by
    rw [Complex.real_smul]
    push_cast
    linear_combination ((t : ℂ) * I) * conj_mul' w
  rw [h, add_im]
  congr 1
  simp only [mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_one, mul_zero, add_zero]

/-- The transverse coordinate is affine. -/
theorem transverseCoord_affine (e w x y : ℂ) {a b : ℝ} (hab : a + b = 1) :
    transverseCoord e w (a • x + b • y) = a * transverseCoord e w x + b * transverseCoord e w y := by
  unfold transverseCoord
  have hab' : (a : ℂ) + b = 1 := by exact_mod_cast hab
  have h : conj w * (a • x + b • y - e) = (a : ℂ) * (conj w * (x - e)) + (b : ℂ) * (conj w * (y - e)) := by
    rw [Complex.real_smul, Complex.real_smul]
    linear_combination (conj w * e) * hab'
  rw [h, add_im, im_ofReal_mul, im_ofReal_mul]

/-- A point with vanishing transverse coordinate lies on the line `e + ℝ w`. -/
theorem exists_eq_add_smul_of_transverseCoord_eq_zero {e w z : ℂ} (hw : w ≠ 0)
    (h : transverseCoord e w z = 0) : ∃ t : ℝ, z = e + t • w := by
  unfold transverseCoord at h
  set ζ := conj w * (z - e) with hζ
  have hre : ζ = (ζ.re : ℂ) := Complex.ext (by simp) (by simp [h])
  have hn : (‖w‖ : ℂ) ^ 2 ≠ 0 := by
    have : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
    exact_mod_cast pow_ne_zero 2 this
  refine ⟨ζ.re / ‖w‖ ^ 2, ?_⟩
  have key : ζ * w = (z - e) * (‖w‖ : ℂ) ^ 2 := by
    rw [hζ, ← conj_mul']
    ring
  rw [Complex.real_smul]
  push_cast
  rw [← hre]
  calc z = e + (z - e) * (‖w‖ : ℂ) ^ 2 / (‖w‖ : ℂ) ^ 2 := by
        rw [mul_div_assoc, div_self hn, mul_one]
        ring
    _ = e + ζ / (‖w‖ : ℂ) ^ 2 * w := by
        rw [← key]
        ring

/-- **Crossing data at an interior point of an edge.** Let `γ` agree inside `B(e, r)` with a segment `[c, d]`, where
`e ∈ (c, d)` and `0 < r ≤ min ‖c - e‖ ‖d - e‖`. Then `B(e, r) \ γ` is the union of two preconnected sets (the open
half-disks) whose closures both contain `γ ∩ B(e, r)`, and there are points `q` in the first and `p` in the second
such that `[p, q] ⊆ B(e, r)`, `e ∈ (p, q)`, `[p, q] ∩ γ ⊆ {e}`, and `[p, q]` crosses an open segment `(c', d') ⊆ γ`
through `e` transversally. -/
theorem exists_crossing_data_of_inter_ball_eq_segment {γ : Set ℂ} {e c d : ℂ}
    (he : e ∈ openSegment ℝ c d) {r : ℝ} (hr : 0 < r) (hrc : r ≤ ‖c - e‖) (hrd : r ≤ ‖d - e‖)
    (hγ : γ ∩ ball e r = segment ℝ c d ∩ ball e r) :
    ∃ P₁ P₂ : Set ℂ, ∃ p q c' d' : ℂ, IsPreconnected P₁ ∧ IsPreconnected P₂ ∧
      ball e r \ γ = P₁ ∪ P₂ ∧ γ ∩ ball e r ⊆ closure P₁ ∩ closure P₂ ∧ q ∈ P₁ ∧ p ∈ P₂ ∧
      segment ℝ p q ⊆ ball e r ∧ e ∈ openSegment ℝ p q ∧ segment ℝ p q ∩ γ ⊆ {e} ∧
      e ∈ openSegment ℝ c' d' ∧ openSegment ℝ c' d' ⊆ γ ∧ (conj (q - p) * (d' - c')).im ≠ 0 := by
  rw [openSegment_eq_image'] at he
  obtain ⟨l, ⟨hl0, hl1⟩, hle⟩ := he
  obtain ⟨w, hw_def⟩ : ∃ w, d - c = w := ⟨_, rfl⟩
  rw [hw_def] at hle
  simp only at hle
  have hd : d = c + w := by rw [← hw_def]; ring
  have hce : c - e = (-l) • w := by
    rw [← hle]; simp only [Complex.real_smul]; push_cast; ring
  have hde : d - e = (1 - l) • w := by
    rw [← hle, hd]; simp only [Complex.real_smul]; push_cast; ring
  rw [hce, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hl0] at hrc
  rw [hde, norm_smul, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hl1)] at hrd
  have hw : w ≠ 0 := by
    rintro rfl
    rw [norm_zero, mul_zero] at hrc
    linarith
  have hnw : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hnw0 : ‖w‖ ≠ 0 := hnw.ne'
  -- norms of displacements along `w` and along `I * w`
  have hnormI : ∀ t : ℝ, ‖t • (I * w)‖ = |t| * ‖w‖ := by
    intro t
    rw [norm_smul, Real.norm_eq_abs, norm_mul, norm_I, one_mul]
  have hnorm : ∀ t : ℝ, ‖t • w‖ = |t| * ‖w‖ := by
    intro t
    rw [norm_smul, Real.norm_eq_abs]
  -- the segment lies on the line `transverseCoord e w = 0`
  have hKS : ∀ z ∈ segment ℝ c d, transverseCoord e w z = 0 := by
    intro z hz
    rw [segment_eq_image', hw_def] at hz
    obtain ⟨θ, -, rfl⟩ := hz
    have : c + θ • w = e + (θ - l) • w := by
      rw [← hle]; simp only [Complex.real_smul]; push_cast; ring
    show transverseCoord e w (c + θ • w) = 0
    rw [this, transverseCoord_add_smul, transverseCoord_self]
  -- inside `B(e, r)` that line lies in the segment
  have hKL : ∀ z ∈ ball e r, transverseCoord e w z = 0 → z ∈ segment ℝ c d := by
    intro z hz hz0
    obtain ⟨t, rfl⟩ := exists_eq_add_smul_of_transverseCoord_eq_zero hw hz0
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, hnorm] at hz
    have ht₁ : |t| < l := by
      have : |t| * ‖w‖ < l * ‖w‖ := by linarith
      exact lt_of_mul_lt_mul_right this hnw.le
    have ht₂ : |t| < 1 - l := by
      have : |t| * ‖w‖ < (1 - l) * ‖w‖ := by linarith
      exact lt_of_mul_lt_mul_right this hnw.le
    rw [segment_eq_image', hw_def]
    refine ⟨l + t, ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩, ?_⟩
    show c + (l + t) • w = e + t • w
    rw [← hle]; simp only [Complex.real_smul]; push_cast; ring
  have hγseg : ∀ z ∈ γ, z ∈ ball e r → z ∈ segment ℝ c d := by
    intro z hzγ hzb
    have : z ∈ segment ℝ c d ∩ ball e r := by rw [← hγ]; exact ⟨hzγ, hzb⟩
    exact this.1
  have hsegγ : ∀ z ∈ segment ℝ c d, z ∈ ball e r → z ∈ γ := by
    intro z hzs hzb
    have : z ∈ γ ∩ ball e r := by rw [hγ]; exact ⟨hzs, hzb⟩
    exact this.1
  -- the two open half-disks
  have hconv₁ : Convex ℝ (ball e r ∩ {z | 0 < transverseCoord e w z}) := by
    intro x hx y hy a b ha hb hab
    refine ⟨convex_ball e r hx.1 hy.1 ha hb hab, ?_⟩
    show 0 < transverseCoord e w (a • x + b • y)
    rw [transverseCoord_affine e w x y hab]
    have hx2 : 0 < transverseCoord e w x := hx.2
    have hy2 : 0 < transverseCoord e w y := hy.2
    rcases ha.lt_or_eq with ha' | ha'
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' hx2) (mul_nonneg hb hy2.le)
    · have hb' : 0 < b := by linarith
      exact add_pos_of_nonneg_of_pos (mul_nonneg ha hx2.le) (mul_pos hb' hy2)
  have hconv₂ : Convex ℝ (ball e r ∩ {z | transverseCoord e w z < 0}) := by
    intro x hx y hy a b ha hb hab
    refine ⟨convex_ball e r hx.1 hy.1 ha hb hab, ?_⟩
    show transverseCoord e w (a • x + b • y) < 0
    rw [transverseCoord_affine e w x y hab]
    have hx2 : 0 < -transverseCoord e w x := neg_pos.mpr hx.2
    have hy2 : 0 < -transverseCoord e w y := neg_pos.mpr hy.2
    have key : 0 < a * -transverseCoord e w x + b * -transverseCoord e w y := by
      rcases ha.lt_or_eq with ha' | ha'
      · exact add_pos_of_pos_of_nonneg (mul_pos ha' hx2) (mul_nonneg hb hy2.le)
      · have hb' : 0 < b := by linarith
        exact add_pos_of_nonneg_of_pos (mul_nonneg ha hx2.le) (mul_pos hb' hy2)
    linarith
  -- crossing points
  set s₀ := r / (2 * ‖w‖) with hs₀_def
  have hs₀ : 0 < s₀ := div_pos hr (by positivity)
  have hs₀w : s₀ * ‖w‖ = r / 2 := by rw [hs₀_def]; field_simp
  have hk : 0 < s₀ * ‖w‖ ^ 2 := mul_pos hs₀ (pow_pos hnw 2)
  have hballI : ∀ t : ℝ, |t| ≤ s₀ → e + t • (I * w) ∈ ball e r := by
    intro t ht
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, hnormI]
    have : |t| * ‖w‖ ≤ s₀ * ‖w‖ := mul_le_mul_of_nonneg_right ht hnw.le
    linarith
  have hball : ∀ t : ℝ, |t| ≤ s₀ → e + t • w ∈ ball e r := by
    intro t ht
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, hnorm]
    have : |t| * ‖w‖ ≤ s₀ * ‖w‖ := mul_le_mul_of_nonneg_right ht hnw.le
    linarith
  have hpb := hballI (-s₀) (by rw [abs_neg, abs_of_pos hs₀])
  have hqb := hballI s₀ (by rw [abs_of_pos hs₀])
  have hc'b := hball (-s₀) (by rw [abs_neg, abs_of_pos hs₀])
  have hd'b := hball s₀ (by rw [abs_of_pos hs₀])
  have htp : transverseCoord e w (e + (-s₀) • (I * w)) = -(s₀ * ‖w‖ ^ 2) := by
    rw [transverseCoord_add_smul_I_mul, transverseCoord_self]
    ring
  have htq : transverseCoord e w (e + s₀ • (I * w)) = s₀ * ‖w‖ ^ 2 := by
    rw [transverseCoord_add_smul_I_mul, transverseCoord_self, zero_add]
  have hmid : ∀ v : ℂ, (1 / 2 : ℝ) • (e + (-s₀) • v) + (1 / 2 : ℝ) • (e + s₀ • v) = e := by
    intro v
    simp only [Complex.real_smul]
    push_cast
    ring
  have hpq_sub : segment ℝ (e + (-s₀) • (I * w)) (e + s₀ • (I * w)) ⊆ ball e r :=
    (convex_ball e r).segment_subset hpb hqb
  refine ⟨ball e r ∩ {z | 0 < transverseCoord e w z}, ball e r ∩ {z | transverseCoord e w z < 0},
    e + (-s₀) • (I * w), e + s₀ • (I * w), e + (-s₀) • w, e + s₀ • w,
    hconv₁.isPreconnected, hconv₂.isPreconnected, ?_, ?_, ⟨hqb, by rw [mem_ofPred_eq, htq]; exact hk⟩,
    ⟨hpb, by rw [mem_ofPred_eq, htp]; linarith⟩, hpq_sub,
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, hmid _⟩, ?_,
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, hmid _⟩, ?_, ?_⟩
  · -- `B(e, r) \ γ` is the union of the two half-disks
    ext z
    constructor
    · rintro ⟨hzb, hzγ⟩
      have h0 : transverseCoord e w z ≠ 0 := fun h0 => hzγ (hsegγ z (hKL z hzb h0) hzb)
      rcases lt_or_gt_of_ne h0 with h | h
      · exact Or.inr ⟨hzb, h⟩
      · exact Or.inl ⟨hzb, h⟩
    · rintro (⟨hzb, hz⟩ | ⟨hzb, hz⟩)
      · refine ⟨hzb, fun hzγ => ?_⟩
        have := hKS z (hγseg z hzγ hzb)
        have hz' : 0 < transverseCoord e w z := hz
        linarith
      · refine ⟨hzb, fun hzγ => ?_⟩
        have := hKS z (hγseg z hzγ hzb)
        have hz' : transverseCoord e w z < 0 := hz
        linarith
  · -- both half-disks accumulate at every point of `γ ∩ B(e, r)`
    rintro z ⟨hzγ, hzb⟩
    have hz0 : transverseCoord e w z = 0 := hKS z (hγseg z hzγ hzb)
    have hzr : ‖z - e‖ < r := by rwa [mem_ball, dist_eq_norm] at hzb
    set s := (r - ‖z - e‖) / (2 * ‖w‖) with hs_def
    have hs : 0 < s := div_pos (by linarith) (by positivity)
    have hsw : s * ‖w‖ = (r - ‖z - e‖) / 2 := by rw [hs_def]; field_simp
    have hzI : ∀ t : ℝ, |t| ≤ s → z + t • (I * w) ∈ ball e r := by
      intro t ht
      rw [mem_ball, dist_eq_norm, add_sub_right_comm]
      have h1 : |t| * ‖w‖ ≤ s * ‖w‖ := mul_le_mul_of_nonneg_right ht hnw.le
      calc ‖z - e + t • (I * w)‖ ≤ ‖z - e‖ + ‖t • (I * w)‖ := norm_add_le _ _
        _ = ‖z - e‖ + |t| * ‖w‖ := by rw [hnormI]
        _ < r := by linarith
    have hz₁ := hzI s (by rw [abs_of_pos hs])
    have hz₂ := hzI (-s) (by rw [abs_neg, abs_of_pos hs])
    have ht₁ : transverseCoord e w (z + s • (I * w)) = s * ‖w‖ ^ 2 := by
      rw [transverseCoord_add_smul_I_mul, hz0, zero_add]
    have ht₂ : transverseCoord e w (z + (-s) • (I * w)) = -(s * ‖w‖ ^ 2) := by
      rw [transverseCoord_add_smul_I_mul, hz0]
      ring
    have hks : 0 < s * ‖w‖ ^ 2 := mul_pos hs (pow_pos hnw 2)
    constructor
    · have hsub : openSegment ℝ z (z + s • (I * w)) ⊆ ball e r ∩ {z | 0 < transverseCoord e w z} := by
        rintro x ⟨a, b, ha, hb, hab, rfl⟩
        refine ⟨(convex_ball e r).openSegment_subset hzb hz₁ ⟨a, b, ha, hb, hab, rfl⟩, ?_⟩
        show 0 < transverseCoord e w (a • z + b • (z + s • (I * w)))
        rw [transverseCoord_affine e w _ _ hab, hz0, ht₁, mul_zero, zero_add]
        exact mul_pos hb hks
      exact closure_mono hsub (segment_subset_closure_openSegment (left_mem_segment ℝ _ _))
    · have hsub : openSegment ℝ z (z + (-s) • (I * w)) ⊆ ball e r ∩ {z | transverseCoord e w z < 0} := by
        rintro x ⟨a, b, ha, hb, hab, rfl⟩
        refine ⟨(convex_ball e r).openSegment_subset hzb hz₂ ⟨a, b, ha, hb, hab, rfl⟩, ?_⟩
        show transverseCoord e w (a • z + b • (z + (-s) • (I * w))) < 0
        rw [transverseCoord_affine e w _ _ hab, hz0, ht₂, mul_zero, zero_add]
        have := mul_pos hb hks
        linarith
      exact closure_mono hsub (segment_subset_closure_openSegment (left_mem_segment ℝ _ _))
  · -- `[p, q]` meets `γ` only at `e`
    rintro x ⟨hx, hxγ⟩
    have hxb := hpq_sub hx
    have hx0 := hKS x (hγseg x hxγ hxb)
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hx
    rw [transverseCoord_affine e w _ _ hab, htp, htq] at hx0
    have h1 : (b - a) * (s₀ * ‖w‖ ^ 2) = 0 := by linarith
    have h2 : b - a = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact h
      · exact absurd h hk.ne'
    have ha2 : a = 1 / 2 := by linarith
    have hb2 : b = 1 / 2 := by linarith
    subst ha2 hb2
    exact hmid _
  · -- `(c', d') ⊆ γ`
    rintro x ⟨a, b, ha, hb, hab, rfl⟩
    have hxb := (convex_ball e r).openSegment_subset hc'b hd'b ⟨a, b, ha, hb, hab, rfl⟩
    have hx0 : transverseCoord e w (a • (e + (-s₀) • w) + b • (e + s₀ • w)) = 0 := by
      rw [transverseCoord_affine e w _ _ hab, transverseCoord_add_smul, transverseCoord_add_smul,
        transverseCoord_self]
      ring
    exact hsegγ _ (hKL _ hxb hx0) hxb
  · -- transversality
    have h1 : e + s₀ • (I * w) - (e + (-s₀) • (I * w)) = ((2 * s₀ : ℝ) : ℂ) * (I * w) := by
      simp only [Complex.real_smul]
      push_cast
      ring
    have h2 : e + s₀ • w - (e + (-s₀) • w) = ((2 * s₀ : ℝ) : ℂ) * w := by
      simp only [Complex.real_smul]
      push_cast
      ring
    rw [h1, h2, map_mul, map_mul, conj_ofReal, conj_I]
    have h3 : ((2 * s₀ : ℝ) : ℂ) * (-I * conj w) * (((2 * s₀ : ℝ) : ℂ) * w) =
        ((-(2 * s₀) * (2 * s₀) * ‖w‖ ^ 2 : ℝ) : ℂ) * I := by
      push_cast
      linear_combination (-(2 * (s₀ : ℂ)) * (2 * s₀) * I) * conj_mul' w
    rw [h3, mul_im, ofReal_re, ofReal_im, I_re, I_im]
    have h4 : 0 < (2 * s₀) * (2 * s₀) * ‖w‖ ^ 2 := mul_pos (mul_pos (by linarith) (by linarith)) (pow_pos hnw 2)
    intro h
    linarith

end LatticeProb.Topology
