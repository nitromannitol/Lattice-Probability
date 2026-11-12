/-
# Alternation of continua in a closed complex disk

Transfer of `disk_alternation_impossible` (the closed unit disk of `ℝ × ℝ`) to an arbitrary closed
disk `closedBall x t` of `ℂ`, through the affine chart `z ↦ (z - x) / t`. As a consequence, in the
closed round annulus `closedBall x t \ ball x s`, a continuum disjoint from two crossing continua
cannot meet the outer circle at two points alternating with their outer points: the two crossing
continua, joined through the centre by two radii of the inner disk, form a continuum of the disk.
-/
import LatticeProb.Topology.DiskAlternation

open Set Metric Complex

namespace LatticeProb.Topology

/-- The affine chart `z ↦ (z - x) / t` of the plane, in the coordinates of `ℝ × ℝ`. -/
noncomputable def unitDiskChart (x : ℂ) (t : ℝ) (z : ℂ) : ℝ × ℝ :=
  (((z - x) / t).re, ((z - x) / t).im)

theorem continuous_unitDiskChart (x : ℂ) (t : ℝ) : Continuous (unitDiskChart x t) := by
  unfold unitDiskChart
  fun_prop

theorem injective_unitDiskChart {x : ℂ} {t : ℝ} (ht : t ≠ 0) :
    Function.Injective (unitDiskChart x t) := by
  intro z w h
  simp only [unitDiskChart, Prod.mk.injEq] at h
  have hzw : (z - x) / t = (w - x) / t := Complex.ext h.1 h.2
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  rw [div_left_inj' ht'] at hzw
  linear_combination hzw

theorem unitDiskChart_mem_unitDisk {x : ℂ} {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∈ closedBall x t) :
    unitDiskChart x t z ∈ {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ 1} := by
  show ((z - x) / t).re ^ 2 + ((z - x) / t).im ^ 2 ≤ 1
  have h1 : ‖(z - x) / t‖ ≤ 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht, div_le_one ht]
    rwa [mem_closedBall, dist_eq_norm] at hz
  have h2 : ((z - x) / t).re ^ 2 + ((z - x) / t).im ^ 2 = ‖(z - x) / t‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [h2]
  exact pow_le_one₀ (norm_nonneg _) h1

theorem unitDiskChart_circle (x : ℂ) {t : ℝ} (ht : t ≠ 0) (θ : ℝ) :
    unitDiskChart x t (x + t * exp (θ * I)) = (Real.cos θ, Real.sin θ) := by
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  have h : (x + t * exp (θ * I) - x) / t = exp (θ * I) := by
    rw [add_sub_cancel_left, mul_div_cancel_left₀ _ ht']
  simp only [unitDiskChart, h, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im]

/-- **Disk alternation in a closed complex disk.** Two continua of `closedBall x t` containing
alternating points of the circle `sphere x t` intersect. -/
theorem nonempty_inter_of_alternating_closedBall {x : ℂ} {t : ℝ} (ht : 0 < t)
    {θ₁ θ₂ θ₃ θ₄ : ℝ} (h₁₂ : θ₁ < θ₂) (h₂₃ : θ₂ < θ₃) (h₃₄ : θ₃ < θ₄)
    (h₄₁ : θ₄ < θ₁ + 2 * Real.pi) {H Γ : Set ℂ} (hH : IsCompact H) (hHc : IsConnected H)
    (hΓ : IsCompact Γ) (hΓc : IsConnected Γ) (hHD : H ⊆ closedBall x t)
    (hΓD : Γ ⊆ closedBall x t) (h₁ : x + t * exp (θ₁ * I) ∈ H)
    (h₃ : x + t * exp (θ₃ * I) ∈ H) (h₂ : x + t * exp (θ₂ * I) ∈ Γ)
    (h₄ : x + t * exp (θ₄ * I) ∈ Γ) : (H ∩ Γ).Nonempty := by
  by_contra hne
  rw [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty] at hne
  have hφ := continuous_unitDiskChart x t
  have hpt := unitDiskChart_circle x ht.ne'
  have hmem : ∀ {θ : ℝ} {E : Set ℂ}, x + t * exp (θ * I) ∈ E →
      (Real.cos θ, Real.sin θ) ∈ unitDiskChart x t '' E := fun {θ} {_} h =>
    hpt θ ▸ mem_image_of_mem _ h
  exact disk_alternation_impossible θ₁ θ₂ θ₃ θ₄ h₁₂ h₂₃ h₃₄ h₄₁
    (unitDiskChart x t '' H) (unitDiskChart x t '' Γ) (hH.image hφ)
    (hHc.image _ hφ.continuousOn) (hΓ.image hφ) (hΓc.image _ hφ.continuousOn)
    (image_subset_iff.2 fun _ hz => unitDiskChart_mem_unitDisk ht (hHD hz))
    (image_subset_iff.2 fun _ hz => unitDiskChart_mem_unitDisk ht (hΓD hz))
    ((disjoint_image_iff (injective_unitDiskChart ht.ne')).2 hne)
    (hmem h₁) (hmem h₃) (hmem h₂) (hmem h₄)

/-- A point of the radius `[a, x]` of the inner disk lying outside the open inner disk is its
endpoint `a`. -/
theorem eq_of_mem_segment_center_of_not_mem_ball {x a y : ℂ} {s : ℝ} (ha : a ∈ sphere x s)
    (hy : y ∈ segment ℝ a x) (hys : y ∉ ball x s) : y = a := by
  rw [segment_eq_image'] at hy
  obtain ⟨μ, ⟨hμ0, hμ1⟩, rfl⟩ := hy
  rw [mem_sphere, dist_eq_norm] at ha
  rw [mem_ball, dist_eq_norm, not_lt] at hys
  have h : a + μ • (x - a) - x = ((1 - μ : ℝ) : ℂ) * (a - x) := by
    rw [Complex.real_smul]; push_cast; ring
  rw [h, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - μ), ha] at hys
  rcases (norm_nonneg (a - x)).lt_or_eq with hpos | hzero
  · rw [ha] at hpos
    have hμ : μ = 0 := le_antisymm (by nlinarith) hμ0
    simp [hμ]
  · have hax : a = x := sub_eq_zero.1 (norm_eq_zero.1 hzero.symm)
    simp [hax]

/-- **Alternation for crossing continua of a round annulus.** Let `P`, `P'` be continua of the
closed annulus `closedBall x t \ ball x s` meeting the inner circle, and `H` a continuum of the
annulus disjoint from `P ∪ P'`. Then `H` cannot contain two points of the outer circle alternating
with a point of `P` and a point of `P'`. -/
theorem false_of_alternating_annulus_crossings {x : ℂ} {s t : ℝ} (hs : 0 ≤ s) (hst : s < t)
    {θ₁ θ₂ θ₃ θ₄ : ℝ} (h₁₂ : θ₁ < θ₂) (h₂₃ : θ₂ < θ₃) (h₃₄ : θ₃ < θ₄)
    (h₄₁ : θ₄ < θ₁ + 2 * Real.pi) {P P' H : Set ℂ} (hP : IsCompact P) (hPc : IsConnected P)
    (hP' : IsCompact P') (hP'c : IsConnected P') (hPA : P ⊆ closedBall x t \ ball x s)
    (hP'A : P' ⊆ closedBall x t \ ball x s) {a a' : ℂ} (haP : a ∈ P) (ha : a ∈ sphere x s)
    (ha'P : a' ∈ P') (ha' : a' ∈ sphere x s) (hH : IsCompact H) (hHc : IsConnected H)
    (hHA : H ⊆ closedBall x t \ ball x s) (hHP : Disjoint H (P ∪ P'))
    (h₁ : x + t * exp (θ₁ * I) ∈ H) (h₃ : x + t * exp (θ₃ * I) ∈ H)
    (h₂ : x + t * exp (θ₂ * I) ∈ P) (h₄ : x + t * exp (θ₄ * I) ∈ P') : False := by
  have ht : 0 < t := hs.trans_lt hst
  have hseg : ∀ {b : ℂ}, b ∈ sphere x s → segment ℝ b x ⊆ closedBall x t := fun {b} hb =>
    (convex_closedBall x t).segment_subset
      (closedBall_subset_closedBall hst.le (sphere_subset_closedBall hb))
      (mem_closedBall_self ht.le)
  have hsegc : ∀ b : ℂ, IsCompact (segment ℝ b x) ∧ IsConnected (segment ℝ b x) := fun b => by
    rw [segment_eq_image']
    have hc : Continuous fun μ : ℝ => b + μ • (x - b) := by fun_prop
    exact ⟨isCompact_Icc.image hc, (isConnected_Icc zero_le_one).image _ hc.continuousOn⟩
  set Γ := P ∪ segment ℝ a x ∪ segment ℝ a' x ∪ P' with hΓdef
  have hΓc : IsConnected Γ := by
    have h1 : IsConnected (P ∪ segment ℝ a x) :=
      hPc.union ⟨a, haP, left_mem_segment ℝ a x⟩ (hsegc a).2
    have h2 : IsConnected (P ∪ segment ℝ a x ∪ segment ℝ a' x) :=
      h1.union ⟨x, Or.inr (right_mem_segment ℝ a x), right_mem_segment ℝ a' x⟩ (hsegc a').2
    exact h2.union ⟨a', Or.inr (left_mem_segment ℝ a' x), ha'P⟩ hP'c
  have hΓ : IsCompact Γ := ((hP.union (hsegc a).1).union (hsegc a').1).union hP'
  have hΓD : Γ ⊆ closedBall x t :=
    union_subset (union_subset (union_subset (fun z hz => (hPA hz).1) (hseg ha)) (hseg ha'))
      fun z hz => (hP'A hz).1
  obtain ⟨y, hyH, hyΓ⟩ := nonempty_inter_of_alternating_closedBall ht h₁₂ h₂₃ h₃₄ h₄₁ hH hHc
    hΓ hΓc (fun z hz => (hHA hz).1) hΓD h₁ h₃ (Or.inl (Or.inl (Or.inl h₂))) (Or.inr h₄)
  have hyP : y ∈ P ∪ P' := by
    rcases hyΓ with ((hy | hy) | hy) | hy
    · exact Or.inl hy
    · exact Or.inl (eq_of_mem_segment_center_of_not_mem_ball ha hy (hHA hyH).2 ▸ haP)
    · exact Or.inr (eq_of_mem_segment_center_of_not_mem_ball ha' hy (hHA hyH).2 ▸ ha'P)
    · exact Or.inr hy
  exact hHP.ne_of_mem hyH hyP rfl

end LatticeProb.Topology
