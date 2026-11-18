import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTAffineReroot

/-! # Exit times and windows of a re-rooted, rescaled plane curve

For a plane curve `c`, a point `z` and a scale `s > 0`, the re-rooted curve
`affineReroot z s 0 c` is `t ↦ s⁻¹ (c (τ_z + s² t) - z)`, where `τ_z` is the first hitting time
of `z`. This file records the deterministic dictionary between the two curves:

* `exitTimeAfter c t₀ z r`, the first exit time of `c` from `ball z r` at or after `t₀`;
* `realWindowCurve t₀ T w`, the curve `w` observed on `[t₀, T]` and frozen outside it;
* exits of the re-rooted curve from `ball 0 R` after time `0` are the exits of `c` from
  `ball z (s * R)` after `τ_z`, in the rescaled clock (`exitTimeAfter_affineReroot`);
* a ball in a trace of the re-rooted curve gives a ball of `s` times the radius in the
  corresponding trace of `c` (`ball_subset_image_of_affineReroot`), and in particular in the
  trace between the exits of `c` from two concentric balls
  (`exists_ball_subset_exitWindow_of_affineReroot`);
* the windows of the re-rooted curves at scales `s` and `1` differ by the space-time scaling
  (`realWindowCurve_affineReroot_apply`).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology

namespace LatticeProb

open MatedCRTHarmonic.MatedCRT

section Defs

variable {E : Type*}

/-- The first exit time of `c` from `ball z r` at or after time `t₀`. -/
def exitTimeAfter [PseudoMetricSpace E] (c : ℝ → E) (t₀ : ℝ) (z : E) (r : ℝ) : ℝ :=
  sInf {t : ℝ | t₀ ≤ t ∧ c t ∉ ball z r}

/-- The curve `w` observed on the time window `[t₀, T]` and frozen outside it. -/
def realWindowCurve [TopologicalSpace E] (t₀ T : ℝ) (w : C(ℝ, E)) : C(ℝ, E) :=
  w.comp ⟨fun t => min (max t t₀) T, (continuous_id.max continuous_const).min continuous_const⟩

theorem realWindowCurve_apply [TopologicalSpace E] (t₀ T : ℝ) (w : C(ℝ, E)) (t : ℝ) :
    realWindowCurve t₀ T w t = w (min (max t t₀) T) := rfl

/-- Exit times after `t₀` increase with the radius, as soon as the larger ball is left. -/
theorem exitTimeAfter_mono_radius [PseudoMetricSpace E] (c : ℝ → E) (t₀ : ℝ) (z : E)
    {r r' : ℝ} (hr : r ≤ r') (hex : ∃ t, t₀ ≤ t ∧ c t ∉ ball z r') :
    exitTimeAfter c t₀ z r ≤ exitTimeAfter c t₀ z r' :=
  csInf_le_csInf ⟨t₀, fun _ ht => ht.1⟩ hex
    (fun _ ht => ⟨ht.1, fun h => ht.2 (ball_subset_ball hr h)⟩)

/-- A curve tending to infinity at infinity leaves every ball after every time. -/
theorem exists_exit_of_tendsto_cocompact [PseudoMetricSpace E] [ProperSpace E] {c : ℝ → E}
    (hc : Tendsto c (cocompact ℝ) (cocompact E)) (t₀ : ℝ) (z : E) (r : ℝ) :
    ∃ t, t₀ ≤ t ∧ c t ∉ ball z r := by
  have h1 : ∀ᶠ t in cocompact ℝ, c t ∉ closedBall z r :=
    hc.eventually (isCompact_closedBall z r).compl_mem_cocompact
  obtain ⟨t, ht⟩ := ((h1.filter_mono atTop_le_cocompact).and (eventually_ge_atTop t₀)).exists
  exact ⟨t, ht.2, fun hb => ht.1 (ball_subset_closedBall hb)⟩

end Defs

/-- Infimum of a set of times under an increasing affine change of clock. -/
theorem sInf_setOf_affine {P : ℝ → Prop} (a : ℝ) {l : ℝ} (hl : 0 < l) (hne : ∃ u, P u)
    (hbdd : BddBelow {u | P u}) :
    sInf {t : ℝ | P (a + l * t)} = (sInf {u : ℝ | P u} - a) / l := by
  have hmono : Monotone (fun u : ℝ => (u - a) / l) := fun x y hxy =>
    div_le_div_of_nonneg_right (sub_le_sub_right hxy a) hl.le
  have hcont : Continuous (fun u : ℝ => (u - a) / l) := by fun_prop
  have himg : (fun u : ℝ => (u - a) / l) '' {u | P u} = {t : ℝ | P (a + l * t)} := by
    ext t
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hu' : a + l * ((u - a) / l) = u := by
        rw [mul_div_cancel₀ _ hl.ne']
        ring
      simpa only [mem_ofPred_eq, hu'] using hu
    · intro ht
      refine ⟨a + l * t, ht, ?_⟩
      simp only
      rw [add_sub_cancel_left, mul_div_cancel_left₀ t hl.ne']
  rw [← himg, ← hmono.map_csInf_of_continuousAt (A := {u | P u}) hcont.continuousAt hne hbdd]

theorem affineReroot_zero_apply_eq (z : ℂ) (s : ℝ) (c : C(ℝ, ℂ)) (t : ℝ) :
    affineReroot z s 0 c t = (s : ℂ)⁻¹ * (c (firstHit c z + s ^ 2 * t) - z) := by
  simp [affineReroot]

/-- Exits of the re-rooted curve from `ball 0 R` after time `0` are the exits of `c` from
`ball z (s * R)` after the first hitting time of `z`, in the clock rescaled by `s ^ 2`. -/
theorem exitTimeAfter_affineReroot (c : C(ℝ, ℂ)) (z : ℂ) {s : ℝ} (hs : 0 < s) (R : ℝ)
    (hex : ∃ t, firstHit c z ≤ t ∧ c t ∉ ball z (s * R)) :
    exitTimeAfter (affineReroot z s 0 c) 0 0 R =
      (exitTimeAfter c (firstHit c z) z (s * R) - firstHit c z) / s ^ 2 := by
  have hs2 : (0 : ℝ) < s ^ 2 := pow_pos hs 2
  have hset : {t : ℝ | 0 ≤ t ∧ affineReroot z s 0 c t ∉ ball (0 : ℂ) R} =
      {t : ℝ | firstHit c z ≤ firstHit c z + s ^ 2 * t ∧
        c (firstHit c z + s ^ 2 * t) ∉ ball z (s * R)} := by
    ext t
    simp only [mem_ofPred_eq, mem_ball, dist_zero_right, not_lt, Complex.dist_eq,
      affineReroot_zero_apply_eq, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg hs.le, le_add_iff_nonneg_right, le_inv_mul_iff₀ hs]
    rw [mul_nonneg_iff_of_pos_left hs2]
  unfold exitTimeAfter
  rw [hset, sInf_setOf_affine (P := fun u => firstHit c z ≤ u ∧ c u ∉ ball z (s * R)) _ hs2 hex
    ⟨firstHit c z, fun _ hu => hu.1⟩]

/-- A ball in a trace of the re-rooted curve gives a ball of `s` times the radius in the
corresponding trace of `c`. -/
theorem ball_subset_image_of_affineReroot (c : C(ℝ, ℂ)) (z : ℂ) {s : ℝ} (hs : 0 < s)
    {w : ℂ} {ρ a b : ℝ} (h : ball w ρ ⊆ affineReroot z s 0 c '' Icc a b) :
    ball (z + s * w) (s * ρ) ⊆ c '' Icc (firstHit c z + s ^ 2 * a) (firstHit c z + s ^ 2 * b) := by
  have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
  intro y hy
  have hy' : (s : ℂ)⁻¹ * (y - z) ∈ ball w ρ := by
    rw [mem_ball, Complex.dist_eq] at hy ⊢
    have hrw : (s : ℂ)⁻¹ * (y - z) - w = (s : ℂ)⁻¹ * (y - (z + s * w)) := by
      field_simp
      ring
    rw [hrw, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hs.le,
      inv_mul_lt_iff₀ hs]
    exact hy
  obtain ⟨t, ht, hct⟩ := h hy'
  refine ⟨firstHit c z + s ^ 2 * t, ⟨?_, ?_⟩, ?_⟩
  · have := mul_le_mul_of_nonneg_left ht.1 (sq_nonneg s)
    linarith
  · have := mul_le_mul_of_nonneg_left ht.2 (sq_nonneg s)
    linarith
  · rw [affineReroot_zero_apply_eq] at hct
    have h1 := mul_left_cancel₀ (inv_ne_zero hs0) hct
    simpa using h1

/-- A ball in the trace of the re-rooted curve between its exits from `ball 0 1` and from
`ball 0 R` yields a ball of `s` times the radius in the trace of `c` between its exits, after
the first hit of `z`, from `ball z s` and from any `ball z r` with `s * R ≤ r`. -/
theorem exists_ball_subset_exitWindow_of_affineReroot (c : C(ℝ, ℂ)) (z : ℂ) {s : ℝ}
    (hs : 0 < s) {R r ρ : ℝ} (hR : s * R ≤ r)
    (hex : ∀ r' : ℝ, ∃ t, firstHit c z ≤ t ∧ c t ∉ ball z r')
    (h : ∃ w, ball w ρ ⊆ affineReroot z s 0 c ''
      Icc (exitTimeAfter (affineReroot z s 0 c) 0 0 1)
        (exitTimeAfter (affineReroot z s 0 c) 0 0 R)) :
    ∃ w, ball w (s * ρ) ⊆ c '' Icc (exitTimeAfter c (firstHit c z) z s)
      (exitTimeAfter c (firstHit c z) z r) := by
  obtain ⟨w, hw⟩ := h
  have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs.ne'
  rw [exitTimeAfter_affineReroot c z hs 1 (hex _), exitTimeAfter_affineReroot c z hs R (hex _),
    mul_one] at hw
  have hb := ball_subset_image_of_affineReroot c z hs hw
  rw [mul_div_cancel₀ _ hs2, mul_div_cancel₀ _ hs2, add_sub_cancel,
    add_sub_cancel] at hb
  refine ⟨z + s * w, hb.trans (image_mono (Icc_subset_Icc le_rfl ?_))⟩
  exact exitTimeAfter_mono_radius c _ z hR (hex r)

/-- The windows of the curves re-rooted at `z` at scales `s` and `1` differ by the
space-time scaling `(t, x) ↦ (s ^ 2 t, s x)`. -/
theorem realWindowCurve_affineReroot_apply (c : C(ℝ, ℂ)) (z : ℂ) {s : ℝ} (hs : 0 < s) (d t : ℝ) :
    realWindowCurve 0 (d / s ^ 2) (affineReroot z s 0 c) t =
      (s : ℂ)⁻¹ * realWindowCurve 0 d (affineReroot z 1 0 c) (s ^ 2 * t) := by
  have hs2 : (0 : ℝ) < s ^ 2 := pow_pos hs 2
  have htime : s ^ 2 * min (max t 0) (d / s ^ 2) = min (max (s ^ 2 * t) 0) d := by
    rw [mul_min_of_nonneg _ _ hs2.le, mul_max_of_nonneg _ _ hs2.le, mul_zero,
      mul_div_cancel₀ _ hs2.ne']
  simp only [realWindowCurve_apply, affineReroot_zero_apply_eq, Complex.ofReal_one, inv_one,
    one_mul, one_pow, htime]

end LatticeProb
