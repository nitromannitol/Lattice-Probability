import LatticeProb.Analysis.AnnulusLogEnergy
import Mathlib.Geometry.Euclidean.Inversion.Basic

/-!
# Regularity of the capacitary potential of a round annulus

For `c ∈ ℂ`, `0 < s < r` and `L = log(r / s)`, let `u(z) = log(r / |z - c|) / L` on the annulus
`D = B_r(c) \ B̄_s(c)`. Its gradient is `∇u(z) = -L⁻¹ (z - c) / |z - c|²`, which is `L⁻¹` times the
inversion in the unit circle about `c`, so `|∇u(z) - ∇u(w)| = L⁻¹ |z - w| / (|z - c| |w - c|)`.

## Main results

* `LatticeProb.hasFDerivAt_log_div_norm_sub`: the gradient of `u` at `z ≠ c`, as `⟪-L⁻¹ |z - c|⁻² (z - c), ·⟫`.
* `LatticeProb.norm_fderiv_sub_fderiv_log_div_norm_sub`: `|∇u(z) - ∇u(w)| = |L|⁻¹ |z - w| / (|z - c| |w - c|)`.
* `LatticeProb.continuousOn_closure_annulus_log_div_norm_sub`: `u` is continuous on the closure of `D`.
* `LatticeProb.abs_log_div_norm_sub_le_one`, `LatticeProb.norm_fderiv_log_div_norm_sub_le`,
  `LatticeProb.norm_fderiv_sub_fderiv_log_div_norm_sub_le`: on `D`, `|u| ≤ 1`, `|∇u| ≤ (s L)⁻¹` and `∇u` is
  `(s² L)⁻¹`-Lipschitz.
* `LatticeProb.annulus_log_div_norm_sub_regular`: for every `K ≥ max(1, (s L)⁻¹, (s² L)⁻¹)`, `u` is differentiable
  on `D`, `|u|, |∇u| ≤ K` on `D`, `∇u` is `K`-Lipschitz on `D`, and `u` is continuous on `D̄`.
-/

open Metric Set

namespace LatticeProb

/-- The gradient of `u(w) = log(r / |w - c|) / L` at `z ≠ c` is `w ↦ ⟪-L⁻¹ |z - c|⁻² (z - c), w⟫`. -/
theorem hasFDerivAt_log_div_norm_sub (c : ℂ) {z : ℂ} (hz : z ≠ c) {r : ℝ} (hr : 0 < r) (L : ℝ) :
    HasFDerivAt (fun w : ℂ => Real.log (r / ‖w - c‖) / L)
      (innerSL ℝ ((-(L⁻¹ * (‖z - c‖ ^ 2)⁻¹)) • (z - c))) z := by
  have hzc : z - c ≠ 0 := sub_ne_zero.2 hz
  have hn : 0 < ‖z - c‖ := norm_pos_iff.2 hzc
  have h1 := HasFDerivAt.comp (g := fun x : ℂ => ‖x‖ ^ 2) (f := fun w : ℂ => w - c) z
    (hasStrictFDerivAt_norm_sq (z - c)).hasFDerivAt ((hasFDerivAt_id z).sub_const c)
  have h2 := h1.log (show ‖z - c‖ ^ 2 ≠ 0 from pow_ne_zero 2 hn.ne')
  have hv := ((h2.const_mul (1 / 2 : ℝ)).const_sub (Real.log r)).mul_const L⁻¹
  have hev : (fun w : ℂ => Real.log (r / ‖w - c‖) / L) =ᶠ[nhds z]
      fun w : ℂ => (Real.log r - (1 / 2 : ℝ) * Real.log (‖w - c‖ ^ 2)) * L⁻¹ := by
    filter_upwards [eventually_ne_nhds hz] with w hw
    rw [Real.log_div hr.ne' (norm_ne_zero_iff.2 (sub_ne_zero.2 hw)), Real.log_pow, div_eq_mul_inv]
    push_cast
    ring
  refine (hv.congr_of_eventuallyEq hev).congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  have h3 : ((‖z - c‖ : ℂ) ^ 2).re = ‖z - c‖ ^ 2 := by rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have h4 : ((‖z - c‖ : ℂ) ^ 2).im = 0 := by rw [← Complex.ofReal_pow, Complex.ofReal_im]
  simp [innerSL_apply_apply, h3, h4]
  field_simp
  ring

/-- The gradient of `u(w) = log(r / |w - c|) / L` at `z ≠ c`. -/
theorem fderiv_log_div_norm_sub (c : ℂ) {z : ℂ} (hz : z ≠ c) {r : ℝ} (hr : 0 < r) (L : ℝ) :
    fderiv ℝ (fun w : ℂ => Real.log (r / ‖w - c‖) / L) z =
      innerSL ℝ ((-(L⁻¹ * (‖z - c‖ ^ 2)⁻¹)) • (z - c)) :=
  (hasFDerivAt_log_div_norm_sub c hz hr L).fderiv

/-- `u(w) = log(r / |w - c|) / L` is differentiable at every `z ≠ c`. -/
theorem differentiableAt_log_div_norm_sub (c : ℂ) {z : ℂ} (hz : z ≠ c) {r : ℝ} (hr : 0 < r) (L : ℝ) :
    DifferentiableAt ℝ (fun w : ℂ => Real.log (r / ‖w - c‖) / L) z :=
  (hasFDerivAt_log_div_norm_sub c hz hr L).differentiableAt

/-- Gradient increments of `u(w) = log(r / |w - c|) / L`: `|∇u(z) - ∇u(w)| = |L|⁻¹ |z - w| / (|z - c| |w - c|)`
for `z, w ≠ c` (the gradient is `L⁻¹` times an inversion about `c`). -/
theorem norm_fderiv_sub_fderiv_log_div_norm_sub (c : ℂ) {z w : ℂ} (hz : z ≠ c) (hw : w ≠ c) {r : ℝ}
    (hr : 0 < r) (L : ℝ) :
    ‖fderiv ℝ (fun x : ℂ => Real.log (r / ‖x - c‖) / L) z -
        fderiv ℝ (fun x : ℂ => Real.log (r / ‖x - c‖) / L) w‖ =
      |L|⁻¹ * (dist z w / (‖z - c‖ * ‖w - c‖)) := by
  have key : ∀ x : ℂ, (-(L⁻¹ * (‖x - c‖ ^ 2)⁻¹)) • (x - c) =
      (-L⁻¹) • (EuclideanGeometry.inversion c 1 x - c) := by
    intro x
    simp only [EuclideanGeometry.inversion, vsub_eq_sub, vadd_eq_add, add_sub_cancel_right, dist_eq_norm,
      smul_smul]
    congr 1
    ring
  rw [fderiv_log_div_norm_sub c hz hr L, fderiv_log_div_norm_sub c hw hr L, ← map_sub, innerSL_apply_norm,
    key z, key w, ← smul_sub, sub_sub_sub_cancel_right, norm_smul, ← dist_eq_norm,
    EuclideanGeometry.dist_inversion_inversion hz hw, norm_neg, Real.norm_eq_abs, abs_inv, dist_eq_norm z c,
    dist_eq_norm w c, one_pow]
  ring

/-- A point of `B_r(c) \ B̄_s(c)` lies at distance in `(s, r)` from `c`. -/
theorem lt_norm_sub_and_lt_of_mem_annulus {c z : ℂ} {s r : ℝ} (hz : z ∈ ball c r \ closedBall c s) :
    s < ‖z - c‖ ∧ ‖z - c‖ < r := by
  rcases hz with ⟨hzr, hzs⟩
  rw [mem_ball, dist_eq_norm] at hzr
  rw [mem_closedBall, dist_eq_norm, not_le] at hzs
  exact ⟨hzs, hzr⟩

/-- `u(w) = log(r / |w - c|) / L` is differentiable on `B_r(c) \ B̄_s(c)` for `0 ≤ s` and `0 < r`. -/
theorem differentiableOn_annulus_log_div_norm_sub (c : ℂ) {s r : ℝ} (hs : 0 ≤ s) (hr : 0 < r) (L : ℝ) :
    DifferentiableOn ℝ (fun w : ℂ => Real.log (r / ‖w - c‖) / L) (ball c r \ closedBall c s) := by
  intro z hz
  have hzc : z ≠ c := by
    intro h
    have := (lt_norm_sub_and_lt_of_mem_annulus hz).1
    rw [h, sub_self, norm_zero] at this
    linarith
  exact (differentiableAt_log_div_norm_sub c hzc hr L).differentiableWithinAt

/-- `u(w) = log(r / |w - c|) / L` is continuous on the closure of `B_r(c) \ B̄_s(c)` for `0 < s` and `0 < r`. -/
theorem continuousOn_closure_annulus_log_div_norm_sub (c : ℂ) {s r : ℝ} (hs : 0 < s) (hr : 0 < r) (L : ℝ) :
    ContinuousOn (fun w : ℂ => Real.log (r / ‖w - c‖) / L) (closure (ball c r \ closedBall c s)) := by
  have hcl : closure (ball c r \ closedBall c s) ⊆ {w : ℂ | s ≤ dist w c} := by
    refine (isClosed_le continuous_const (continuous_id.dist continuous_const)).closure_subset_iff.2 ?_
    intro z hz
    rw [mem_ofPred_eq, dist_eq_norm]
    exact (lt_norm_sub_and_lt_of_mem_annulus hz).1.le
  intro z hz
  have hzc : z ≠ c := by
    intro h
    have := hcl hz
    rw [mem_ofPred_eq, h, dist_self] at this
    linarith
  exact (differentiableAt_log_div_norm_sub c hzc hr L).continuousAt.continuousWithinAt

/-- On `B_r(c) \ B̄_s(c)` with `0 < s < r`, the potential `u = log(r / |· - c|) / log(r / s)` takes values in
`[0, 1]`. -/
theorem log_div_norm_sub_mem_Icc (c : ℂ) {s r : ℝ} (hs : 0 < s) (hsr : s < r) {z : ℂ}
    (hz : z ∈ ball c r \ closedBall c s) :
    Real.log (r / ‖z - c‖) / Real.log (r / s) ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨h1, h2⟩ := lt_norm_sub_and_lt_of_mem_annulus hz
  have hn : 0 < ‖z - c‖ := hs.trans h1
  have hL : 0 < Real.log (r / s) := Real.log_pos ((one_lt_div hs).2 hsr)
  have ha : 0 ≤ Real.log (r / ‖z - c‖) := Real.log_nonneg ((one_le_div hn).2 h2.le)
  have hb : Real.log (r / ‖z - c‖) ≤ Real.log (r / s) :=
    Real.log_le_log (div_pos (hs.trans hsr) hn) (div_le_div_of_nonneg_left (hs.trans hsr).le hs h1.le)
  exact ⟨div_nonneg ha hL.le, (div_le_one hL).2 hb⟩

/-- On `B_r(c) \ B̄_s(c)` with `0 < s < r`, `|u| ≤ 1` for `u = log(r / |· - c|) / log(r / s)`. -/
theorem abs_log_div_norm_sub_le_one (c : ℂ) {s r : ℝ} (hs : 0 < s) (hsr : s < r) {z : ℂ}
    (hz : z ∈ ball c r \ closedBall c s) :
    |Real.log (r / ‖z - c‖) / Real.log (r / s)| ≤ 1 := by
  obtain ⟨h0, h1⟩ := log_div_norm_sub_mem_Icc c hs hsr hz
  rw [abs_of_nonneg h0]
  exact h1

/-- On `B_r(c) \ B̄_s(c)` with `0 < s < r`, the gradient of `u = log(r / |· - c|) / log(r / s)` has norm at most
`(s log(r / s))⁻¹`. -/
theorem norm_fderiv_log_div_norm_sub_le (c : ℂ) {s r : ℝ} (hs : 0 < s) (hsr : s < r) {z : ℂ}
    (hz : z ∈ ball c r \ closedBall c s) :
    ‖fderiv ℝ (fun w : ℂ => Real.log (r / ‖w - c‖) / Real.log (r / s)) z‖ ≤ (s * Real.log (r / s))⁻¹ := by
  obtain ⟨h1, -⟩ := lt_norm_sub_and_lt_of_mem_annulus hz
  have hn : 0 < ‖z - c‖ := hs.trans h1
  have hL : 0 < Real.log (r / s) := Real.log_pos ((one_lt_div hs).2 hsr)
  have hzc : z ≠ c := fun h => by rw [h, sub_self, norm_zero] at hn; exact lt_irrefl 0 hn
  rw [norm_fderiv_log_div_norm_sub c hzc (hs.trans hsr), abs_of_pos hL, mul_inv, mul_comm]
  exact mul_le_mul_of_nonneg_right (inv_anti₀ hs h1.le) (inv_nonneg.2 hL.le)

/-- On `B_r(c) \ B̄_s(c)` with `0 < s < r`, the gradient of `u = log(r / |· - c|) / log(r / s)` is
`(s² log(r / s))⁻¹`-Lipschitz. -/
theorem norm_fderiv_sub_fderiv_log_div_norm_sub_le (c : ℂ) {s r : ℝ} (hs : 0 < s) (hsr : s < r) {z w : ℂ}
    (hz : z ∈ ball c r \ closedBall c s) (hw : w ∈ ball c r \ closedBall c s) :
    ‖fderiv ℝ (fun x : ℂ => Real.log (r / ‖x - c‖) / Real.log (r / s)) z -
        fderiv ℝ (fun x : ℂ => Real.log (r / ‖x - c‖) / Real.log (r / s)) w‖ ≤
      (s ^ 2 * Real.log (r / s))⁻¹ * dist z w := by
  obtain ⟨hz1, -⟩ := lt_norm_sub_and_lt_of_mem_annulus hz
  obtain ⟨hw1, -⟩ := lt_norm_sub_and_lt_of_mem_annulus hw
  have hzn : 0 < ‖z - c‖ := hs.trans hz1
  have hwn : 0 < ‖w - c‖ := hs.trans hw1
  have hL : 0 < Real.log (r / s) := Real.log_pos ((one_lt_div hs).2 hsr)
  have hzc : z ≠ c := fun h => by rw [h, sub_self, norm_zero] at hzn; exact lt_irrefl 0 hzn
  have hwc : w ≠ c := fun h => by rw [h, sub_self, norm_zero] at hwn; exact lt_irrefl 0 hwn
  rw [norm_fderiv_sub_fderiv_log_div_norm_sub c hzc hwc (hs.trans hsr), abs_of_pos hL]
  have hss : s ^ 2 ≤ ‖z - c‖ * ‖w - c‖ := by
    rw [sq]
    exact mul_le_mul hz1.le hw1.le hs.le hzn.le
  have hd : 0 ≤ dist z w := dist_nonneg
  calc (Real.log (r / s))⁻¹ * (dist z w / (‖z - c‖ * ‖w - c‖))
      ≤ (Real.log (r / s))⁻¹ * (dist z w / s ^ 2) := by
        gcongr
    _ = (s ^ 2 * Real.log (r / s))⁻¹ * dist z w := by ring

/-- The regularity hypotheses of the energy comparison for mated-CRT maps (Gwynne-Miller-Sheffield 2019,
Theorem 3.2), for the capacitary potential `u = log(r / |· - c|) / log(r / s)` of the annulus
`D = B_r(c) \ B̄_s(c)`, `0 < s < r`: for every `K` with `1 ≤ K`, `(s log(r / s))⁻¹ ≤ K` and
`(s² log(r / s))⁻¹ ≤ K`, `u` is differentiable on `D` with `K`-Lipschitz gradient, `|u| ≤ K` and `|∇u| ≤ K` on
`D`, and `u` is continuous on `D̄`. -/
theorem annulus_log_div_norm_sub_regular (c : ℂ) {s r : ℝ} (hs : 0 < s) (hsr : s < r) {K : ℝ} (hK : 1 ≤ K)
    (hK1 : (s * Real.log (r / s))⁻¹ ≤ K) (hK2 : (s ^ 2 * Real.log (r / s))⁻¹ ≤ K) :
    DifferentiableOn ℝ (fun w : ℂ => Real.log (r / ‖w - c‖) / Real.log (r / s)) (ball c r \ closedBall c s) ∧
      (∀ z ∈ ball c r \ closedBall c s, ∀ w ∈ ball c r \ closedBall c s,
        ‖fderiv ℝ (fun x : ℂ => Real.log (r / ‖x - c‖) / Real.log (r / s)) z -
          fderiv ℝ (fun x : ℂ => Real.log (r / ‖x - c‖) / Real.log (r / s)) w‖ ≤ K * dist z w) ∧
      (∀ z ∈ ball c r \ closedBall c s, |Real.log (r / ‖z - c‖) / Real.log (r / s)| ≤ K) ∧
      (∀ z ∈ ball c r \ closedBall c s,
        ‖fderiv ℝ (fun w : ℂ => Real.log (r / ‖w - c‖) / Real.log (r / s)) z‖ ≤ K) ∧
      ContinuousOn (fun w : ℂ => Real.log (r / ‖w - c‖) / Real.log (r / s))
        (closure (ball c r \ closedBall c s)) := by
  refine ⟨differentiableOn_annulus_log_div_norm_sub c hs.le (hs.trans hsr) _, ?_, ?_, ?_,
    continuousOn_closure_annulus_log_div_norm_sub c hs (hs.trans hsr) _⟩
  · intro z hz w hw
    exact (norm_fderiv_sub_fderiv_log_div_norm_sub_le c hs hsr hz hw).trans
      (mul_le_mul_of_nonneg_right hK2 dist_nonneg)
  · intro z hz
    exact (abs_log_div_norm_sub_le_one c hs hsr hz).trans hK
  · intro z hz
    exact (norm_fderiv_log_div_norm_sub_le c hs hsr hz).trans hK1

end LatticeProb
