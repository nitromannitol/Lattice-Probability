import LatticeProb.Bonanno.MatedCRTHarmonic.Topology.PolarTemplate

/-!
# Arcs of the polar crossing template have diameter bounded below

The polar crossing template `T = polarTemplate` is parametrized by `t ∈ [0,1]`, through the
unnormalized time `u = 4t ∈ [0,4]`, as `T = r(u) exp(i θ(u))` with `r = polarRadius` and
`θ = polarAngle`. It has four phases with corners at `u = 1, 2, 3`:

* `u ∈ [0,1]`: `r = 1 - u/10`, `θ = 0`;
* `u ∈ [1,2]`: `r = 7/10 + u/5`, `θ = 0`;
* `u ∈ [2,3]`: `r = 13/10 - u/10` (a spiral);
* `u ∈ [3,4]`: `r = 1`, `θ = 2π - 1/10 + (u-3)/5` (a circular arc).

On each of the first three phases the radius moves with speed at least `1/10`; on the last one
the argument moves with speed `1/5` at radius `1`. A parameter window of `u`-length `2/25`
contains at most one corner, so it contains a sub-window of `u`-length `1/25` inside one phase.
Hence every arc `T([s, s'])` with `s' - s ≥ 1/50` has diameter at least `1/250`
(`one_div_le_diam_polarTemplate_image_Icc`). The template is not injective (the second phase
retraces part of the first), so this arc-diameter bound is the substitute for local injectivity.

## Main results

* `templateU`: the template in the unnormalized time `u`; `polarTemplate_mk`.
* `abs_polarRadius_sub_le_norm`: radius increments are bounded by chord lengths.
* `one_div_le_norm_templateU_sub_phase1` ... `_phase4`: chords of `u`-length `1/25` in one phase.
* `exists_far_pair`: a far pair inside every window of `u`-length `2/25`.
* `one_div_le_diam_polarTemplate_image_Icc`: the arc-diameter bound.
-/

set_option autoImplicit false

namespace LatticeProb.PolarTemplate

open Set Real MatedCRTHarmonic.Topology

/-- The polar crossing template in its unnormalized time `u ∈ [0,4]`. -/
noncomputable def templateU (u : ℝ) : ℂ :=
  ((polarRadius u : ℝ) : ℂ) * Complex.exp (((polarAngle u : ℝ) : ℂ) * Complex.I)

theorem polarTemplate_mk (x : ℝ) (hx : x ∈ unitInterval) :
    polarTemplate ⟨x, hx⟩ = templateU (4 * x) := rfl

/-- On the template's time interval the modulus is the radius coordinate. -/
theorem norm_templateU {u : ℝ} (hu0 : 0 ≤ u) (hu4 : u ≤ 4) :
    ‖templateU u‖ = polarRadius u := by
  rw [templateU, norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, Real.norm_eq_abs,
    mul_one, abs_of_nonneg (le_trans (by norm_num) (polarRadius_bounds hu0 hu4).1)]

/-- Radius increments are bounded by chord lengths of the template. -/
theorem abs_polarRadius_sub_le_norm {a b : ℝ} (ha0 : 0 ≤ a) (ha4 : a ≤ 4) (hb0 : 0 ≤ b)
    (hb4 : b ≤ 4) : |polarRadius a - polarRadius b| ≤ ‖templateU a - templateU b‖ := by
  rw [← norm_templateU ha0 ha4, ← norm_templateU hb0 hb4]
  exact abs_norm_sub_norm_le _ _

theorem polarRadius_phase1 {u : ℝ} (hu : u ≤ 1) : polarRadius u = 1 - u / 10 := by
  rw [polarRadius, max_eq_right (by linarith : u - 1 ≤ 0), max_eq_right (by linarith : u - 2 ≤ 0),
    max_eq_right (by linarith : u - 3 ≤ 0)]
  ring

theorem polarRadius_phase2 {u : ℝ} (hu1 : 1 ≤ u) (hu2 : u ≤ 2) :
    polarRadius u = 7 / 10 + u / 5 := by
  rw [polarRadius, max_eq_left (by linarith : 0 ≤ u - 1), max_eq_right (by linarith : u - 2 ≤ 0),
    max_eq_right (by linarith : u - 3 ≤ 0)]
  ring

theorem polarRadius_phase3 {u : ℝ} (hu2 : 2 ≤ u) (hu3 : u ≤ 3) :
    polarRadius u = 13 / 10 - u / 10 := by
  rw [polarRadius, max_eq_left (by linarith : 0 ≤ u - 1), max_eq_left (by linarith : 0 ≤ u - 2),
    max_eq_right (by linarith : u - 3 ≤ 0)]
  ring

theorem polarRadius_phase4 {u : ℝ} (hu3 : 3 ≤ u) : polarRadius u = 1 := by
  rw [polarRadius, max_eq_left (by linarith : 0 ≤ u - 1), max_eq_left (by linarith : 0 ≤ u - 2),
    max_eq_left (by linarith : 0 ≤ u - 3)]
  ring

theorem polarAngle_phase4 {u : ℝ} (hu3 : 3 ≤ u) :
    polarAngle u = 2 * π - 1 / 10 + (u - 3) / 5 := by
  rw [polarAngle, max_eq_left (by linarith : 0 ≤ u - 2), max_eq_left (by linarith : 0 ≤ u - 3)]
  ring

/-- On the final circular arc the template is `exp (i θ(u))`. -/
theorem templateU_phase4 {u : ℝ} (hu3 : 3 ≤ u) :
    templateU u = Complex.exp (((2 * π - 1 / 10 + (u - 3) / 5 : ℝ) : ℂ) * Complex.I) := by
  rw [templateU, polarRadius_phase4 hu3, polarAngle_phase4 hu3, Complex.ofReal_one, one_mul]

theorem one_div_le_norm_templateU_sub_phase1 {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1)
    (hab : a + 1 / 25 ≤ b) : 1 / 250 ≤ ‖templateU a - templateU b‖ := by
  refine le_trans ?_ (abs_polarRadius_sub_le_norm ha (by linarith) (by linarith) (by linarith))
  rw [polarRadius_phase1 (by linarith), polarRadius_phase1 hb]
  exact le_trans (by linarith) (le_abs_self _)

theorem one_div_le_norm_templateU_sub_phase2 {a b : ℝ} (ha : 1 ≤ a) (hb : b ≤ 2)
    (hab : a + 1 / 25 ≤ b) : 1 / 250 ≤ ‖templateU a - templateU b‖ := by
  refine le_trans ?_
    (abs_polarRadius_sub_le_norm (by linarith) (by linarith) (by linarith) (by linarith))
  rw [polarRadius_phase2 ha (by linarith), polarRadius_phase2 (by linarith) hb]
  exact le_trans (by linarith) (neg_le_abs _)

theorem one_div_le_norm_templateU_sub_phase3 {a b : ℝ} (ha : 2 ≤ a) (hb : b ≤ 3)
    (hab : a + 1 / 25 ≤ b) : 1 / 250 ≤ ‖templateU a - templateU b‖ := by
  refine le_trans ?_
    (abs_polarRadius_sub_le_norm (by linarith) (by linarith) (by linarith) (by linarith))
  rw [polarRadius_phase3 ha (by linarith), polarRadius_phase3 (by linarith) hb]
  exact le_trans (by linarith) (le_abs_self _)

/-- On the final arc, a chord of angular increment `x = (b - a)/5 ≥ 1/125` has length
`2 sin (x/2) ≥ 1/250`. -/
theorem one_div_le_norm_templateU_sub_phase4 {a b : ℝ} (ha : 3 ≤ a) (hb : b ≤ 4)
    (hab : a + 1 / 25 ≤ b) : 1 / 250 ≤ ‖templateU a - templateU b‖ := by
  have hsplit : templateU b = templateU a * Complex.exp (Complex.I * (((b - a) / 5 : ℝ) : ℂ)) := by
    rw [templateU_phase4 ha, templateU_phase4 (by linarith), ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hfactor : templateU a - templateU b =
      templateU a * (1 - Complex.exp (Complex.I * (((b - a) / 5 : ℝ) : ℂ))) := by
    rw [hsplit]
    ring
  rw [hfactor, norm_mul, norm_templateU (by linarith) (by linarith), polarRadius_phase4 ha,
    one_mul, norm_sub_rev, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs]
  have hx0 : 0 ≤ (b - a) / 5 / 2 := by
    have : 0 ≤ b - a := by linarith
    positivity
  have hxpi : (b - a) / 5 / 2 ≤ π / 2 := by
    have := Real.two_le_pi
    linarith
  have hsin := Real.mul_le_sin hx0 hxpi
  have hpi4 := Real.pi_le_four
  have h2pi : (1 : ℝ) / 2 ≤ 2 / π := by
    rw [le_div_iff₀ Real.pi_pos]
    linarith
  have hlow : 1 / 2 * ((b - a) / 5 / 2) ≤ 2 / π * ((b - a) / 5 / 2) :=
    mul_le_mul_of_nonneg_right h2pi hx0
  refine le_trans ?_ (le_abs_self _)
  linarith

/-- Every window `[u, v]` of `u`-length at least `2/25` inside `[0,4]` contains two parameters
whose template points are at distance at least `1/250`. -/
theorem exists_far_pair {u v : ℝ} (hu : 0 ≤ u) (hv : v ≤ 4) (huv : u + 2 / 25 ≤ v) :
    ∃ a b, u ≤ a ∧ a ≤ b ∧ b ≤ v ∧ 1 / 250 ≤ ‖templateU a - templateU b‖ := by
  rcases le_or_gt 3 u with h3 | h3
  · exact ⟨u, u + 2 / 25, le_rfl, by linarith, huv,
      one_div_le_norm_templateU_sub_phase4 h3 (by linarith) (by linarith)⟩
  rcases le_or_gt 2 u with h2 | h2
  · by_cases hw : u + 2 / 25 ≤ 3
    · exact ⟨u, u + 2 / 25, le_rfl, by linarith, huv,
        one_div_le_norm_templateU_sub_phase3 h2 hw (by linarith)⟩
    by_cases hc : u + 1 / 25 ≤ 3
    · exact ⟨u, 3, le_rfl, by linarith, by linarith,
        one_div_le_norm_templateU_sub_phase3 h2 le_rfl hc⟩
    · exact ⟨3, u + 2 / 25, by linarith, by linarith, huv,
        one_div_le_norm_templateU_sub_phase4 le_rfl (by linarith) (by linarith)⟩
  rcases le_or_gt 1 u with h1 | h1
  · by_cases hw : u + 2 / 25 ≤ 2
    · exact ⟨u, u + 2 / 25, le_rfl, by linarith, huv,
        one_div_le_norm_templateU_sub_phase2 h1 hw (by linarith)⟩
    by_cases hc : u + 1 / 25 ≤ 2
    · exact ⟨u, 2, le_rfl, by linarith, by linarith,
        one_div_le_norm_templateU_sub_phase2 h1 le_rfl hc⟩
    · exact ⟨2, u + 2 / 25, by linarith, by linarith, huv,
        one_div_le_norm_templateU_sub_phase3 le_rfl (by linarith) (by linarith)⟩
  by_cases hw : u + 2 / 25 ≤ 1
  · exact ⟨u, u + 2 / 25, le_rfl, by linarith, huv,
      one_div_le_norm_templateU_sub_phase1 hu hw (by linarith)⟩
  by_cases hc : u + 1 / 25 ≤ 1
  · exact ⟨u, 1, le_rfl, by linarith, by linarith,
      one_div_le_norm_templateU_sub_phase1 hu le_rfl hc⟩
  · exact ⟨1, u + 2 / 25, by linarith, by linarith, huv,
      one_div_le_norm_templateU_sub_phase2 le_rfl (by linarith) (by linarith)⟩

/-- **Template arc-diameter bound.** Every arc of the polar crossing template over a parameter
interval of length at least `1/50` has diameter at least `1/250`. -/
theorem one_div_le_diam_polarTemplate_image_Icc (s s' : unitInterval)
    (h : (1 / 50 : ℝ) ≤ (s' : ℝ) - s) :
    (1 / 250 : ℝ) ≤ Metric.diam (polarTemplate '' Icc s s') := by
  have hs0 : (0 : ℝ) ≤ s := s.2.1
  have hs1 : (s' : ℝ) ≤ 1 := s'.2.2
  obtain ⟨a, b, hua, hab, hbv, hfar⟩ :=
    exists_far_pair (u := 4 * (s : ℝ)) (v := 4 * (s' : ℝ)) (by linarith) (by linarith)
      (by linarith)
  have ha : a / 4 ∈ unitInterval := ⟨by linarith, by linarith⟩
  have hb : b / 4 ∈ unitInterval := ⟨by linarith, by linarith⟩
  have hbdd : Bornology.IsBounded (polarTemplate '' Icc s s') :=
    (isCompact_range polarTemplate.continuous).isBounded.subset (image_subset_range _ _)
  have hmemA : polarTemplate ⟨a / 4, ha⟩ ∈ polarTemplate '' Icc s s' :=
    mem_image_of_mem _ ⟨show (s : ℝ) ≤ a / 4 by linarith, show a / 4 ≤ (s' : ℝ) by linarith⟩
  have hmemB : polarTemplate ⟨b / 4, hb⟩ ∈ polarTemplate '' Icc s s' :=
    mem_image_of_mem _ ⟨show (s : ℝ) ≤ b / 4 by linarith, show b / 4 ≤ (s' : ℝ) by linarith⟩
  have hA : polarTemplate ⟨a / 4, ha⟩ = templateU a := by
    rw [polarTemplate_mk]
    congr 1
    ring
  have hB : polarTemplate ⟨b / 4, hb⟩ = templateU b := by
    rw [polarTemplate_mk]
    congr 1
    ring
  calc (1 / 250 : ℝ) ≤ ‖templateU a - templateU b‖ := hfar
    _ = dist (polarTemplate ⟨a / 4, ha⟩) (polarTemplate ⟨b / 4, hb⟩) := by
      rw [dist_eq_norm, hA, hB]
    _ ≤ Metric.diam (polarTemplate '' Icc s s') := Metric.dist_le_diam_of_mem hbdd hmemA hmemB

end LatticeProb.PolarTemplate
