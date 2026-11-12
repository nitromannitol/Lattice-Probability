import Mathlib

/-!
# Local sides of two rays and of two segments from a point

Two closed rays `y + [0, ∞) u` and `y + [0, ∞) v` with distinct directions cut every open disk centred at `y` into
two open circular sectors. Each sector is preconnected, being the image of a product of two open intervals under
polar coordinates centred at `y`, and the closure of each sector contains the two radii. The same holds for two
segments `[y, a]`, `[y, b]` with distinct directions inside a disk of radius at most `min ‖a - y‖ ‖b - y‖`.

This is the local two-sidedness of a polygonal arc at an interior point (Whyburn, *Analytic Topology*, Chapter VI):
near a point of an open edge both segments point in opposite directions, near an interior vertex they point in
different directions.

* `exists_sides_of_two_rays`: the two sides of two rays in a disk centred at their common origin.
* `exists_sides_of_two_segments`: the same for two segments in a small disk centred at their common endpoint.
* `exists_sides_of_inter_ball_eq_two_segments`: the same for any set agreeing with two such segments in the disk.
-/

open Set Metric Complex

namespace LatticeProb.Topology

/-- Polar coordinates centred at `y`: `(ρ, θ) ↦ y + ρ e^{iθ}`. -/
noncomputable def polarAt (y : ℂ) (p : ℝ × ℝ) : ℂ := y + (p.1 : ℂ) * exp (p.2 * I)

theorem continuous_polarAt (y : ℂ) : Continuous (polarAt y) := by
  unfold polarAt
  fun_prop

/-- `e^{iθ} = e^{iθ'}` if and only if `θ - θ'` is an integer multiple of `2π`. -/
theorem exp_mul_I_eq_exp_mul_I_iff {θ θ' : ℝ} :
    exp (θ * I) = exp (θ' * I) ↔ ∃ n : ℤ, θ = θ' + n * (2 * Real.pi) := by
  rw [exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h := congrArg Complex.im hn
    simp at h
    linarith
  · rintro ⟨n, rfl⟩
    exact ⟨n, by push_cast; ring⟩

/-- An angle within `2π` of `a` and different from `a` is not congruent to `a` modulo `2π`. -/
theorem ne_add_int_mul_two_pi {a θ : ℝ} (h₁ : a - 2 * Real.pi < θ) (h₂ : θ < a + 2 * Real.pi) (h₃ : θ ≠ a)
    (n : ℤ) : θ ≠ a + n * (2 * Real.pi) := by
  rintro rfl
  have hpi := Real.pi_pos
  have hn₁ : (-1 : ℝ) < n := by
    by_contra hn
    rw [not_lt] at hn
    nlinarith
  have hn₂ : (n : ℝ) < 1 := by
    by_contra hn
    rw [not_lt] at hn
    nlinarith
  have h₁' : (-1 : ℤ) < n := by exact_mod_cast hn₁
  have h₂' : n < 1 := by exact_mod_cast hn₂
  have hn : n = 0 := by omega
  subst hn
  simp at h₃

/-- If `ρ e^{iθ} = s e^{iα}` with `ρ > 0` and `s ≥ 0`, then `e^{iθ} = e^{iα}`. -/
theorem exp_mul_I_eq_of_mul_eq {ρ s θ α : ℝ} (hρ : 0 < ρ) (hs : 0 ≤ s)
    (h : (ρ : ℂ) * exp (θ * I) = s * exp (α * I)) : exp (θ * I) = exp (α * I) := by
  have hn := congrArg norm h
  simp only [norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hρ, abs_of_nonneg hs] at hn
  rw [hn] at h
  have hs0 : (s : ℂ) ≠ 0 := by
    rw [← hn]
    exact_mod_cast hρ.ne'
  exact mul_left_cancel₀ hs0 h

/-- A point `y + ρ e^{iα}` with `ρ ≥ 0` and `e^{iα} = u / ‖u‖` lies on the ray `y + [0, ∞) u`. -/
theorem mem_ray_of_exp_eq {y u : ℂ} (hu : u ≠ 0) {ρ θ : ℝ} (hρ : 0 ≤ ρ)
    (hθ : exp (θ * I) = exp (arg u * I)) :
    y + (ρ : ℂ) * exp (θ * I) ∈ (fun t : ℝ => y + t • u) '' Ici 0 := by
  have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hnu0 : (‖u‖ : ℂ) ≠ 0 := by exact_mod_cast hnu.ne'
  refine ⟨ρ / ‖u‖, div_nonneg hρ hnu.le, ?_⟩
  show y + (ρ / ‖u‖) • u = y + ρ * exp (θ * I)
  rw [hθ, Complex.real_smul]
  congr 1
  calc ((ρ / ‖u‖ : ℝ) : ℂ) * u = ((ρ / ‖u‖ : ℝ) : ℂ) * (‖u‖ * exp (arg u * I)) := by
        rw [norm_mul_exp_arg_mul_I]
    _ = ρ * exp (arg u * I) := by rw [ofReal_div, ← mul_assoc, div_mul_cancel₀ _ hnu0]

/-- A point `y + ρ e^{iθ}` with `ρ > 0` on the ray `y + [0, ∞) u` has `e^{iθ} = u / ‖u‖`. -/
theorem exp_eq_of_mem_ray {y u : ℂ} {ρ θ : ℝ} (hρ : 0 < ρ)
    (h : y + (ρ : ℂ) * exp (θ * I) ∈ (fun t : ℝ => y + t • u) '' Ici 0) :
    exp (θ * I) = exp (arg u * I) := by
  obtain ⟨t, ht, hteq⟩ := h
  simp only [Complex.real_smul] at hteq
  refine exp_mul_I_eq_of_mul_eq (s := t * ‖u‖) hρ (mul_nonneg ht (norm_nonneg u)) ?_
  have h' := add_left_cancel hteq
  rw [← h']
  conv_lhs => rw [← norm_mul_exp_arg_mul_I u]
  push_cast
  ring

/-- The image under polar coordinates of a closed box is in the closure of the image of the open box. -/
theorem polarAt_image_Icc_subset_closure {y : ℂ} {r a b : ℝ} (hr : 0 < r) (hab : a < b) :
    polarAt y '' (Icc 0 r ×ˢ Icc a b) ⊆ closure (polarAt y '' (Ioo 0 r ×ˢ Ioo a b)) := by
  have hcl : closure (Ioo 0 r ×ˢ Ioo a b) = Icc 0 r ×ˢ Icc a b := by
    rw [closure_prod_eq, closure_Ioo hr.ne, closure_Ioo hab.ne]
  rw [← hcl]
  exact image_closure_subset_closure_image (continuous_polarAt y)

/-- **Local sides of two rays.** Two closed rays `y + [0, ∞) u`, `y + [0, ∞) v` with distinct directions cut the
open disk `B(y, r)` into two preconnected sets (open circular sectors) whose closures both contain the two radii
`(y + [0, ∞) u ∪ y + [0, ∞) v) ∩ B(y, r)`. -/
theorem exists_sides_of_two_rays {y u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0)
    (huv : ∀ t : ℝ, 0 < t → v ≠ t • u) {r : ℝ} (hr : 0 < r) :
    ∃ P₁ P₂ : Set ℂ, IsPreconnected P₁ ∧ IsPreconnected P₂ ∧
      ball y r \ ((fun t : ℝ => y + t • u) '' Ici 0 ∪ (fun t : ℝ => y + t • v) '' Ici 0) = P₁ ∪ P₂ ∧
      ((fun t : ℝ => y + t • u) '' Ici 0 ∪ (fun t : ℝ => y + t • v) '' Ici 0) ∩ ball y r ⊆
        closure P₁ ∩ closure P₂ := by
  set Lu := (fun t : ℝ => y + t • u) '' Ici 0 with hLu
  set Lv := (fun t : ℝ => y + t • v) '' Ici 0 with hLv
  have hpi := Real.pi_pos
  set α := arg u
  set β := arg v
  have hu' : (‖u‖ : ℂ) * exp (α * I) = u := norm_mul_exp_arg_mul_I u
  have hv' : (‖v‖ : ℂ) * exp (β * I) = v := norm_mul_exp_arg_mul_I v
  set δ := toIcoMod Real.two_pi_pos 0 (β - α) with hδdef
  have hδmem : δ ∈ Ico 0 (0 + 2 * Real.pi) := toIcoMod_mem_Ico _ _ _
  rw [zero_add] at hδmem
  -- `α + δ` is congruent to `β` modulo `2π`
  have hδβ : exp (((α + δ : ℝ) : ℂ) * I) = exp (β * I) := by
    rw [exp_mul_I_eq_exp_mul_I_iff]
    refine ⟨-toIcoDiv Real.two_pi_pos 0 (β - α), ?_⟩
    have h := self_sub_toIcoMod Real.two_pi_pos 0 (β - α)
    rw [zsmul_eq_mul] at h
    push_cast
    linarith
  have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hδ0 : δ ≠ 0 := by
    intro h0
    rw [h0, add_zero] at hδβ
    apply huv (‖v‖ / ‖u‖) (div_pos hnv hnu)
    have hnu0 : (‖u‖ : ℂ) ≠ 0 := by exact_mod_cast hnu.ne'
    calc v = ‖v‖ * exp (β * I) := hv'.symm
      _ = ‖v‖ * exp (α * I) := by rw [hδβ]
      _ = ((‖v‖ / ‖u‖ : ℝ) : ℂ) * (‖u‖ * exp (α * I)) := by
          rw [ofReal_div, ← mul_assoc, div_mul_cancel₀ _ hnu0]
      _ = (‖v‖ / ‖u‖ : ℝ) • u := by rw [hu', Complex.real_smul]
  have hδpos : 0 < δ := lt_of_le_of_ne hδmem.1 (Ne.symm hδ0)
  have hδlt : δ < 2 * Real.pi := hδmem.2
  have hexp2pi : exp (((α + 2 * Real.pi : ℝ) : ℂ) * I) = exp (α * I) :=
    exp_mul_I_eq_exp_mul_I_iff.mpr ⟨1, by push_cast; ring⟩
  -- a point of a sector of angle `< 2π` is on neither ray
  have hnotL : ∀ ρ θ : ℝ, 0 < ρ → α - 2 * Real.pi < θ → θ < α + 2 * Real.pi → θ ≠ α →
      α + δ - 2 * Real.pi < θ → θ < α + δ + 2 * Real.pi → θ ≠ α + δ →
      polarAt y (ρ, θ) ∉ Lu ∪ Lv := by
    intro ρ θ hρ h₁ h₂ h₃ h₄ h₅ h₆ hL
    rcases hL with hL | hL
    · have he := exp_eq_of_mem_ray hρ hL
      obtain ⟨n, hn⟩ := exp_mul_I_eq_exp_mul_I_iff.mp he
      exact ne_add_int_mul_two_pi h₁ h₂ h₃ n hn
    · have he := exp_eq_of_mem_ray hρ hL
      rw [← hδβ] at he
      obtain ⟨n, hn⟩ := exp_mul_I_eq_exp_mul_I_iff.mp he
      exact ne_add_int_mul_two_pi h₄ h₅ h₆ n hn
  have hball : ∀ ρ θ : ℝ, 0 ≤ ρ → ρ < r → polarAt y (ρ, θ) ∈ ball y r := by
    intro ρ θ hρ hρr
    rw [mem_ball, dist_eq_norm]
    simp only [polarAt, add_sub_cancel_left, norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hρ]
    exact hρr
  refine ⟨polarAt y '' (Ioo 0 r ×ˢ Ioo α (α + δ)), polarAt y '' (Ioo 0 r ×ˢ Ioo (α + δ) (α + 2 * Real.pi)),
    (isPreconnected_Ioo.prod isPreconnected_Ioo).image _ (continuous_polarAt y).continuousOn,
    (isPreconnected_Ioo.prod isPreconnected_Ioo).image _ (continuous_polarAt y).continuousOn, ?_, ?_⟩
  · apply Subset.antisymm
    · rintro z ⟨hzb, hzL⟩
      set w := z - y with hw
      have hw0 : w ≠ 0 := by
        intro h0
        apply hzL
        left
        refine ⟨0, mem_Ici.mpr le_rfl, ?_⟩
        simp only [zero_smul, add_zero]
        exact (sub_eq_zero.mp h0).symm
      have hwr : ‖w‖ < r := by rw [mem_ball, dist_eq_norm] at hzb; exact hzb
      have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
      set θ := α + toIcoMod Real.two_pi_pos 0 (arg w - α) with hθdef
      have hθmem : toIcoMod Real.two_pi_pos 0 (arg w - α) ∈ Ico 0 (0 + 2 * Real.pi) := toIcoMod_mem_Ico _ _ _
      rw [zero_add] at hθmem
      have hθw : exp ((θ : ℂ) * I) = exp (arg w * I) := by
        rw [exp_mul_I_eq_exp_mul_I_iff]
        refine ⟨-toIcoDiv Real.two_pi_pos 0 (arg w - α), ?_⟩
        have h := self_sub_toIcoMod Real.two_pi_pos 0 (arg w - α)
        rw [zsmul_eq_mul] at h
        push_cast
        linarith
      have hz : z = polarAt y (‖w‖, θ) := by
        simp only [polarAt]
        rw [hθw, norm_mul_exp_arg_mul_I, hw, add_sub_cancel]
      have hθα : θ ≠ α := by
        intro h
        apply hzL
        left
        rw [hz]
        exact mem_ray_of_exp_eq hu hwpos.le (by rw [h])
      have hθαδ : θ ≠ α + δ := by
        intro h
        apply hzL
        right
        rw [hz]
        exact mem_ray_of_exp_eq hv hwpos.le (by rw [h, hδβ])
      rcases lt_or_gt_of_ne hθαδ with hlt | hgt
      · left
        exact ⟨(‖w‖, θ), ⟨⟨hwpos, hwr⟩, lt_of_le_of_ne (by linarith [hθmem.1]) (Ne.symm hθα), hlt⟩, hz.symm⟩
      · right
        exact ⟨(‖w‖, θ), ⟨⟨hwpos, hwr⟩, hgt, by linarith [hθmem.2]⟩, hz.symm⟩
    · rintro z (⟨⟨ρ, θ⟩, ⟨⟨hρ, hρr⟩, hθ₁, hθ₂⟩, rfl⟩ | ⟨⟨ρ, θ⟩, ⟨⟨hρ, hρr⟩, hθ₁, hθ₂⟩, rfl⟩)
      · refine ⟨hball ρ θ hρ.le hρr, hnotL ρ θ hρ (by linarith) (by linarith) hθ₁.ne'
          (by linarith) (by linarith) hθ₂.ne⟩
      · refine ⟨hball ρ θ hρ.le hρr, hnotL ρ θ hρ (by linarith) hθ₂ (show α < θ by linarith).ne'
          (by linarith) (by linarith) hθ₁.ne'⟩
  · have hS₁ := polarAt_image_Icc_subset_closure (y := y) hr (show α < α + δ by linarith)
    have hS₂ := polarAt_image_Icc_subset_closure (y := y) hr
      (show α + δ < α + 2 * Real.pi by linarith [hδmem.2])
    rintro z ⟨hzL, hzb⟩
    rcases hzL with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
    · have hρr : t * ‖u‖ < r := by
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht] at hzb
        exact hzb
      have hρ : 0 ≤ t * ‖u‖ := mul_nonneg ht (norm_nonneg u)
      have hz : y + t • u = polarAt y (t * ‖u‖, α) := by
        simp only [polarAt, Complex.real_smul]
        conv_lhs => rw [← hu']
        push_cast
        ring
      have hz' : y + t • u = polarAt y (t * ‖u‖, α + 2 * Real.pi) := by
        rw [hz]
        simp only [polarAt]
        rw [hexp2pi]
      refine ⟨hS₁ ⟨_, ⟨⟨hρ, hρr.le⟩, le_refl α, by linarith⟩, hz.symm⟩,
        hS₂ ⟨_, ⟨⟨hρ, hρr.le⟩, by linarith [hδmem.2], le_refl _⟩, hz'.symm⟩⟩
    · have hρr : t * ‖v‖ < r := by
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht] at hzb
        exact hzb
      have hρ : 0 ≤ t * ‖v‖ := mul_nonneg ht (norm_nonneg v)
      have hz : y + t • v = polarAt y (t * ‖v‖, α + δ) := by
        simp only [polarAt, Complex.real_smul]
        rw [hδβ]
        conv_lhs => rw [← hv']
        push_cast
        ring
      refine ⟨hS₁ ⟨_, ⟨⟨hρ, hρr.le⟩, by linarith, le_refl _⟩, hz.symm⟩,
        hS₂ ⟨_, ⟨⟨hρ, hρr.le⟩, le_refl _, by linarith [hδmem.2]⟩, hz.symm⟩⟩

/-- Inside `B(y, r)` with `r ≤ ‖a - y‖`, the segment `[y, a]` agrees with the ray `y + [0, ∞) (a - y)`. -/
theorem segment_inter_ball_eq_ray_inter_ball {y a : ℂ} {r : ℝ} (hra : r ≤ ‖a - y‖) :
    segment ℝ y a ∩ ball y r = (fun t : ℝ => y + t • (a - y)) '' Ici 0 ∩ ball y r := by
  rw [segment_eq_image']
  ext z
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, hz⟩
    exact ⟨⟨t, ht.1, rfl⟩, hz⟩
  · rintro ⟨⟨t, ht, rfl⟩, hz⟩
    refine ⟨⟨t, ⟨ht, ?_⟩, rfl⟩, hz⟩
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht] at hz
    by_contra h
    rw [not_le] at h
    have : ‖a - y‖ ≤ t * ‖a - y‖ := le_mul_of_one_le_left (norm_nonneg _) h.le
    linarith

/-- **Local sides of two segments.** Two segments `[y, a]`, `[y, b]` with distinct directions cut the open disk
`B(y, r)`, `0 < r ≤ min ‖a - y‖ ‖b - y‖`, into two preconnected sets whose closures both contain
`([y, a] ∪ [y, b]) ∩ B(y, r)`. -/
theorem exists_sides_of_two_segments {y a b : ℂ} (ha : a ≠ y) (hb : b ≠ y)
    (hab : ∀ t : ℝ, 0 < t → b - y ≠ t • (a - y)) {r : ℝ} (hr : 0 < r) (hra : r ≤ ‖a - y‖)
    (hrb : r ≤ ‖b - y‖) :
    ∃ P₁ P₂ : Set ℂ, IsPreconnected P₁ ∧ IsPreconnected P₂ ∧
      ball y r \ (segment ℝ y a ∪ segment ℝ y b) = P₁ ∪ P₂ ∧
      (segment ℝ y a ∪ segment ℝ y b) ∩ ball y r ⊆ closure P₁ ∩ closure P₂ := by
  obtain ⟨P₁, P₂, h₁, h₂, hU, hcl⟩ :=
    exists_sides_of_two_rays (y := y) (sub_ne_zero.mpr ha) (sub_ne_zero.mpr hb) hab hr
  have hloc : (segment ℝ y a ∪ segment ℝ y b) ∩ ball y r =
      ((fun t : ℝ => y + t • (a - y)) '' Ici 0 ∪ (fun t : ℝ => y + t • (b - y)) '' Ici 0) ∩ ball y r := by
    rw [union_inter_distrib_right, union_inter_distrib_right, segment_inter_ball_eq_ray_inter_ball hra,
      segment_inter_ball_eq_ray_inter_ball hrb]
  refine ⟨P₁, P₂, h₁, h₂, ?_, hloc ▸ hcl⟩
  rw [← hU, ← sdiff_inter_self_eq_sdiff, hloc, sdiff_inter_self_eq_sdiff]

/-- **Local two-sidedness of a set that is two segments near a point.** If a set `γ` agrees inside `B(y, r)`,
`0 < r ≤ min ‖a - y‖ ‖b - y‖`, with two segments `[y, a]`, `[y, b]` of distinct directions, then `B(y, r) \ γ` is
the union of two preconnected sets whose closures both contain `γ ∩ B(y, r)`. -/
theorem exists_sides_of_inter_ball_eq_two_segments {γ : Set ℂ} {y a b : ℂ} (ha : a ≠ y) (hb : b ≠ y)
    (hab : ∀ t : ℝ, 0 < t → b - y ≠ t • (a - y)) {r : ℝ} (hr : 0 < r) (hra : r ≤ ‖a - y‖)
    (hrb : r ≤ ‖b - y‖) (hγ : γ ∩ ball y r = (segment ℝ y a ∪ segment ℝ y b) ∩ ball y r) :
    ∃ P₁ P₂ : Set ℂ, IsPreconnected P₁ ∧ IsPreconnected P₂ ∧ ball y r \ γ = P₁ ∪ P₂ ∧
      γ ∩ ball y r ⊆ closure P₁ ∩ closure P₂ := by
  obtain ⟨P₁, P₂, h₁, h₂, hU, hcl⟩ := exists_sides_of_two_segments ha hb hab hr hra hrb
  refine ⟨P₁, P₂, h₁, h₂, ?_, hγ ▸ hcl⟩
  rw [← hU, ← sdiff_inter_self_eq_sdiff, hγ, sdiff_inter_self_eq_sdiff]

end LatticeProb.Topology
