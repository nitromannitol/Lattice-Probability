import LatticeProb.LQG.WeylScalingLocalBound

/-!
# The Weyl scaling by a log weight away from the singular point

Let `D` be a Euclidean length metric on `ℂ` and `D_W = e^{ξ W} · D` its Weyl scaling (`weylScaling`, Gwynne-Miller,
arXiv:1905.00383, (1.8)) by the log weight `W = -α₀ log |·|`. Away from the origin the weight is bounded above on the
exterior `{|z| > r}` of every disc when `ξ α₀ ≥ 0`, and on every disc centred at `0` when `ξ α₀ ≤ 0`. Hence, for every
`α₀`, `D_W(u, v) < ∞` for `u, v ≠ 0` and `D_W(x, w) → 0` as `w → x` for `x ≠ 0`. The only remaining conditions for
`D_W` to be a finite Euclidean length metric concern the singular point `0`.

## Main results

* `isPreconnected_setOf_lt_norm`: the exterior `{z : ℂ | r < |z|}` of a disc is preconnected.
* `IsEuclideanLengthMetric.weylScaling_log_lt_top_of_ne`, `IsEuclideanLengthMetric.tendsto_weylScaling_log_of_ne`:
  finiteness and continuity on the diagonal away from `0`.
* `IsLQGMetric.ae_isEuclideanLengthMetric_weylScaling_log_of_zero`: for the γ-LQG metric `D_h` of the field
  `h = h^ℂ - α₀ log |·|`, the Euclidean length metric axiom follows from two almost sure statements at the origin:
  `D_h(u, 0) < ∞` for every `u`, and `D_h(0, w) → 0` as `w → 0`.
* `IsLQGMetric.ae_weylScaling_log_add_of_zero`: the Weyl scaling axiom for `D_h` (with `ξ > 0`) follows from the first.
-/

open MeasureTheory Set Filter Topology LatticeProb.Gauss
open scoped ENNReal

namespace LatticeProb.LQG

/-- The exterior `{z | r < |z|}` of a disc in `ℂ` is preconnected: it is the image of `(r, ∞) × ℝ` under the polar map
`(t, θ) ↦ t e^{iθ}`. -/
theorem isPreconnected_setOf_lt_norm (r : ℝ) : IsPreconnected {z : ℂ | r < ‖z‖} := by
  have e : {z : ℂ | r < ‖z‖} =
      (fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp (p.2 * Complex.I)) '' (Ioi r ×ˢ univ) := by
    ext z
    constructor
    · intro hz
      exact ⟨(‖z‖, Complex.arg z), ⟨hz, mem_univ _⟩, Complex.norm_mul_exp_arg_mul_I z⟩
    · rintro ⟨⟨t, θ⟩, ⟨ht, -⟩, rfl⟩
      show r < ‖(t : ℂ) * Complex.exp (θ * Complex.I)‖
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact lt_of_lt_of_le ht (le_abs_self t)
  rw [e]
  exact (isPreconnected_Ioi.prod isPreconnected_univ).image _ (by fun_prop : Continuous _).continuousOn

/-- The log weight `ξ (-α₀ log |z|)` is at most `-(ξ α₀) log r` for `|z| > r > 0` when `ξ α₀ ≥ 0`. -/
theorem mul_neg_mul_log_norm_le_of_lt_norm {ξ α₀ : ℝ} (hα : 0 ≤ ξ * α₀) {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : r < ‖z‖) : ξ * (-α₀ * Real.log ‖z‖) ≤ -(ξ * α₀) * Real.log r := by
  have hlog : Real.log r ≤ Real.log ‖z‖ := Real.log_le_log hr hz.le
  calc ξ * (-α₀ * Real.log ‖z‖) = -(ξ * α₀) * Real.log ‖z‖ := by ring
    _ ≤ -(ξ * α₀) * Real.log r := mul_le_mul_of_nonpos_left hlog (by linarith)

/-- **Finiteness away from the origin.** For a Euclidean length metric `D` and every `ξ, α₀`,
`e^{-ξ α₀ log |·|} · D (u, v) < ∞` for `u, v ≠ 0`. -/
theorem IsEuclideanLengthMetric.weylScaling_log_lt_top_of_ne {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (ξ α₀ : ℝ) {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0) :
    weylScaling D ξ (fun x => -α₀ * Real.log ‖x‖) u v < ∞ := by
  rcases le_total (ξ * α₀) 0 with hα | hα
  · exact (hD.weylScaling_log_lt_top_and_tendsto hα).1 u v
  · have hu' : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hv' : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hm : 0 < min ‖u‖ ‖v‖ := lt_min hu' hv'
    have hru : min ‖u‖ ‖v‖ / 2 < ‖u‖ := (half_lt_self hm).trans_le (min_le_left _ _)
    have hrv : min ‖u‖ ‖v‖ / 2 < ‖v‖ := (half_lt_self hm).trans_le (min_le_right _ _)
    exact hD.weylScaling_lt_top (U := {z : ℂ | min ‖u‖ ‖v‖ / 2 < ‖z‖})
      (isOpen_lt continuous_const continuous_norm) (isPreconnected_setOf_lt_norm _)
      (fun z hz => mul_neg_mul_log_norm_le_of_lt_norm hα (half_pos hm) hz) hru hrv

/-- **Continuity on the diagonal away from the origin.** For a Euclidean length metric `D`, every `ξ, α₀` and `x ≠ 0`,
`e^{-ξ α₀ log |·|} · D (x, w) → 0` as `w → x`. -/
theorem IsEuclideanLengthMetric.tendsto_weylScaling_log_of_ne {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (ξ α₀ : ℝ) {x : ℂ} (hx : x ≠ 0) :
    Tendsto (fun w => weylScaling D ξ (fun x => -α₀ * Real.log ‖x‖) x w) (𝓝 x) (𝓝 0) := by
  rcases le_total (ξ * α₀) 0 with hα | hα
  · exact (hD.weylScaling_log_lt_top_and_tendsto hα).2 x
  · have hx' : 0 < ‖x‖ := norm_pos_iff.mpr hx
    exact hD.tendsto_weylScaling_self (U := {z : ℂ | ‖x‖ / 2 < ‖z‖})
      (isOpen_lt continuous_const continuous_norm)
      (fun z hz => mul_neg_mul_log_norm_le_of_lt_norm hα (half_pos hx') hz) (half_lt_self hx')

/-- Finiteness of `e^{-ξ α₀ log |·|} · D` everywhere from finiteness of its distances to the origin. -/
theorem IsEuclideanLengthMetric.weylScaling_log_lt_top_of_zero {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (ξ α₀ : ℝ) (h0 : ∀ u, weylScaling D ξ (fun x => -α₀ * Real.log ‖x‖) u 0 < ∞) (u v : ℂ) :
    weylScaling D ξ (fun x => -α₀ * Real.log ‖x‖) u v < ∞ := by
  rcases eq_or_ne v 0 with rfl | hv
  · exact h0 u
  rcases eq_or_ne u 0 with rfl | hu
  · rw [hD.weylScaling_symm]
    exact h0 v
  exact hD.weylScaling_log_lt_top_of_ne ξ α₀ hu hv

variable {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Axiom I for the LQG metric of a field with a log singularity, reduced to the origin.** Let `𝔇` be a γ-LQG metric,
`h^ℂ` a whole-plane GFF and `D_h = e^{-ξ α₀ log |·|} · D_{h^ℂ}`. If almost surely `D_h(u, 0) < ∞` for every `u` and
`D_h(0, w) → 0` as `w → 0`, then almost surely `D_h` is finite and its real part is a Euclidean length metric. -/
theorem IsLQGMetric.ae_isEuclideanLengthMetric_weylScaling_log_of_zero (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hG : IsWholePlaneGFF P hC hcirc) (α₀ : ℝ)
    (hfin0 : ∀ᵐ ω ∂P, ∀ u, weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u 0 < ∞)
    (hcont0 : ∀ᵐ ω ∂P,
      Tendsto (fun w => weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) 0 w) (𝓝 0) (𝓝 0)) :
    ∀ᵐ ω ∂P, (∀ u v, weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v < ∞) ∧
      IsEuclideanLengthMetric fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal := by
  refine h𝔇.ae_isEuclideanLengthMetric_weylScaling_log hG α₀ ?_ ?_
  · filter_upwards [h𝔇.ae_isEuclideanLengthMetric_self hG, hfin0] with ω hD h0
    exact hD.weylScaling_log_lt_top_of_zero ξ α₀ h0
  · filter_upwards [h𝔇.ae_isEuclideanLengthMetric_self hG, hcont0] with ω hD h0 x
    rcases eq_or_ne x 0 with rfl | hx
    · exact h0
    · exact hD.tendsto_weylScaling_log_of_ne ξ α₀ hx

/-- **Axiom III for the LQG metric of a field with a log singularity, reduced to the origin.** For `ξ > 0`, if almost
surely `D_h(u, 0) < ∞` for every `u`, then almost surely, for every continuous `f`,
`e^{ξ (f - α₀ log |·|)} · D_{h^ℂ} = e^{ξ f} · D_h`. -/
theorem IsLQGMetric.ae_weylScaling_log_add_of_zero (h𝔇 : IsLQGMetric γ ξ 𝔇) (hG : IsWholePlaneGFF P hC hcirc)
    (hξ : 0 < ξ) (α₀ : ℝ)
    (hfin0 : ∀ᵐ ω ∂P, ∀ u, weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u 0 < ∞) :
    ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f → ∀ u v,
      weylScaling (𝔇 (hC ω)) ξ (fun x => f x - α₀ * Real.log ‖x‖) u v =
        weylScaling (fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal) ξ f u v := by
  refine h𝔇.ae_weylScaling_log_add hG hξ α₀ ?_
  filter_upwards [h𝔇.ae_isEuclideanLengthMetric_self hG, hfin0] with ω hD h0
  exact hD.weylScaling_log_lt_top_of_zero ξ α₀ h0

end LatticeProb.LQG
