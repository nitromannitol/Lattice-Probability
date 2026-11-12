import LatticeProb.LQG.WeylScalingSingularLengthMetric
import LatticeProb.LQG.InternalMetricCompactFinite

/-!
# Local upper bound for a Weyl scaling, and the log-singular field with a nonpositive exponent

Let `D` be a Euclidean length metric on `ℂ` and `e^{ξ f} · D` its Weyl scaling (`weylScaling`, Gwynne-Miller,
arXiv:1905.00383, (1.8)). If `ξ f ≤ K` on a set `U`, every path in `U` reparametrized by `D`-length is a competitor of
weighted cost at most `e^K` times its `D`-length, so `e^{ξ f} · D (x, y) ≤ e^K D(x, y; U)`. The weight is only required
to be bounded above on `U`; it may be unbounded below (for instance at a point singularity).

## Main results

* `IsEuclideanLengthMetric.weylScaling_le_exp_mul_internalMetric`: the local comparison above.
* `IsEuclideanLengthMetric.weylScaling_lt_top`: finiteness between points of an open preconnected set on which `ξ f` is
  bounded above.
* `IsEuclideanLengthMetric.tendsto_weylScaling_self`: `e^{ξ f} · D (x, w) → 0` as `w → x` when `ξ f` is bounded above
  on an open neighbourhood of `x`.
* `IsLQGMetric.ae_isEuclideanLengthMetric_weylScaling_log_of_mul_nonpos`: for a γ-LQG metric `𝔇` of a whole-plane GFF
  `h^ℂ` and `ξ α₀ ≤ 0`, almost surely `D_h = e^{-ξ α₀ log |·|} · D_{h^ℂ}` is finite and its real part is a Euclidean
  length metric (the weight `-ξ α₀ log |·|` is bounded above on bounded sets).
* `IsLQGMetric.ae_weylScaling_log_add_of_nonpos`: for `ξ > 0` and `α₀ ≤ 0`, almost surely, for every continuous `f`,
  `e^{ξ (f - α₀ log |·|)} · D_{h^ℂ} = e^{ξ f} · D_h`.
-/

open MeasureTheory Set Filter Topology LatticeProb.Gauss
open scoped ENNReal

namespace LatticeProb.LQG

/-- **Local Weyl comparison.** If `ξ f ≤ K` on `U`, then `e^{ξ f} · D (x, y) ≤ e^K D(x, y; U)` for a Euclidean length
metric `D`. Each path in `U` of finite `D`-length, reparametrized by `D`-length, stays in `U` and is a competitor in
`weylScaling` of cost at most `e^K` times its length. -/
theorem IsEuclideanLengthMetric.weylScaling_le_exp_mul_internalMetric {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) {ξ K : ℝ} {f : ℂ → ℝ} {U : Set ℂ} (hK : ∀ z ∈ U, ξ * f z ≤ K) (x y : ℂ) :
    weylScaling D ξ f x y ≤ ENNReal.ofReal (Real.exp K) * internalMetric D U x y := by
  have hc0 : ENNReal.ofReal (Real.exp K) ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos K)).ne'
  unfold internalMetric
  rw [ENNReal.mul_iInf_of_ne hc0 ENNReal.ofReal_ne_top]
  refine le_iInf fun P => ?_
  rw [ENNReal.mul_iInf_of_ne hc0 ENNReal.ofReal_ne_top]
  refine le_iInf fun hP => ?_
  rcases eq_or_ne (pathLength D P) ⊤ with htop | hfin
  · rw [htop, ENNReal.mul_top hc0]
    exact le_top
  · obtain ⟨q, hq, h0, hL, hqU⟩ := arcLength_param hD P hP hfin
    have hle := weylScaling_le_of_lengthParametrized D ξ f hq h0 hL (fun t ht => hK (q t) (hqU t ht))
    rwa [ENNReal.ofReal_toReal hfin] at hle

/-- **Finiteness.** If `U` is open and preconnected and `ξ f ≤ K` on `U`, then `e^{ξ f} · D (x, y) < ∞` for `x, y ∈ U`. -/
theorem IsEuclideanLengthMetric.weylScaling_lt_top {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {ξ K : ℝ}
    {f : ℂ → ℝ} {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U) (hK : ∀ z ∈ U, ξ * f z ≤ K) {x y : ℂ}
    (hx : x ∈ U) (hy : y ∈ U) : weylScaling D ξ f x y < ∞ :=
  (hD.weylScaling_le_exp_mul_internalMetric hK x y).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (hD.internalMetric_lt_top_of_isPreconnected hUc hUo Subset.rfl hx hy))

/-- **Continuity on the diagonal.** If `U` is an open neighbourhood of `x` and `ξ f ≤ K` on `U`, then
`e^{ξ f} · D (x, w) → 0` as `w → x`: it is at most `e^K D(x, w; U)`, which tends to `D(x, x; U) = 0`. -/
theorem IsEuclideanLengthMetric.tendsto_weylScaling_self {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {ξ K : ℝ} {f : ℂ → ℝ} {U : Set ℂ} (hUo : IsOpen U) (hK : ∀ z ∈ U, ξ * f z ≤ K) {x : ℂ} (hx : x ∈ U) :
    Tendsto (fun w => weylScaling D ξ f x w) (𝓝 x) (𝓝 0) := by
  have hnn : ∀ u v, 0 ≤ D u v := euclid_D_nonneg hD
  have h1 : Tendsto (fun w => internalMetric D U x w) (𝓝 x) (𝓝 0) := by
    have h := (hD.continuousAt_internalMetric_pair hnn hUo hx hx).tendsto.comp
      (tendsto_const_nhds.prodMk_nhds tendsto_id)
    rw [hD.internalMetric_self_of_mem_open hnn hUo hx] at h
    exact h
  have h2 : Tendsto (fun w => ENNReal.ofReal (Real.exp K) * internalMetric D U x w) (𝓝 x) (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul h1 (Or.inr ENNReal.ofReal_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun _ => bot_le)
    (fun w => hD.weylScaling_le_exp_mul_internalMetric hK x w)

/-- The log weight `ξ (-α₀ log |z|)` is at most `-(ξ α₀) R` for `|z| < R` when `ξ α₀ ≤ 0` (with `log 0 = 0`). -/
theorem mul_neg_mul_log_norm_le {ξ α₀ : ℝ} (hα : ξ * α₀ ≤ 0) {R : ℝ} {z : ℂ} (hz : ‖z‖ < R) :
    ξ * (-α₀ * Real.log ‖z‖) ≤ -(ξ * α₀) * R := by
  have hlog : Real.log ‖z‖ ≤ R := by
    rcases (norm_nonneg z).eq_or_lt with h | h
    · rw [← h, Real.log_zero]
      linarith [norm_nonneg z]
    · linarith [Real.log_le_sub_one_of_pos h]
  calc ξ * (-α₀ * Real.log ‖z‖) = -(ξ * α₀) * Real.log ‖z‖ := by ring
    _ ≤ -(ξ * α₀) * R := mul_le_mul_of_nonneg_left hlog (by linarith)

/-- For a Euclidean length metric `D` and `ξ α₀ ≤ 0`, the Weyl scaling `e^{-ξ α₀ log |·|} · D` is finite and tends to
`0` on the diagonal: the weight is bounded above on every ball centred at `0`. -/
theorem IsEuclideanLengthMetric.weylScaling_log_lt_top_and_tendsto {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) {ξ α₀ : ℝ} (hα : ξ * α₀ ≤ 0) :
    (∀ u v, weylScaling D ξ (fun x => -α₀ * Real.log ‖x‖) u v < ∞) ∧
      ∀ x, Tendsto (fun w => weylScaling D ξ (fun x => -α₀ * Real.log ‖x‖) x w) (𝓝 x) (𝓝 0) := by
  have hK : ∀ R : ℝ, ∀ z ∈ Metric.ball (0 : ℂ) R, ξ * (-α₀ * Real.log ‖z‖) ≤ -(ξ * α₀) * R :=
    fun R z hz => mul_neg_mul_log_norm_le hα (by simpa using hz)
  refine ⟨fun u v => ?_, fun x => ?_⟩
  · have hu : u ∈ Metric.ball (0 : ℂ) (‖u‖ + ‖v‖ + 1) := by
      rw [mem_ball_zero_iff]
      linarith [norm_nonneg v]
    have hv : v ∈ Metric.ball (0 : ℂ) (‖u‖ + ‖v‖ + 1) := by
      rw [mem_ball_zero_iff]
      linarith [norm_nonneg u]
    exact hD.weylScaling_lt_top Metric.isOpen_ball (convex_ball _ _).isPreconnected (hK _) hu hv
  · have hx : x ∈ Metric.ball (0 : ℂ) (‖x‖ + 1) := by
      rw [mem_ball_zero_iff]
      linarith
    exact hD.tendsto_weylScaling_self Metric.isOpen_ball (hK _) hx

variable {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Axiom I for the LQG metric of a field with a log singularity, `ξ α₀ ≤ 0`.** Let `𝔇` be a γ-LQG metric and `h^ℂ`
a whole-plane GFF. If `ξ α₀ ≤ 0`, then almost surely `D_h = e^{-ξ α₀ log |·|} · D_{h^ℂ}` is finite and its real part is a
Euclidean length metric. -/
theorem IsLQGMetric.ae_isEuclideanLengthMetric_weylScaling_log_of_mul_nonpos (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hG : IsWholePlaneGFF P hC hcirc) {α₀ : ℝ} (hα : ξ * α₀ ≤ 0) :
    ∀ᵐ ω ∂P, (∀ u v, weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v < ∞) ∧
      IsEuclideanLengthMetric fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal := by
  refine h𝔇.ae_isEuclideanLengthMetric_weylScaling_log hG α₀ ?_ ?_
  · filter_upwards [h𝔇.ae_isEuclideanLengthMetric_self hG] with ω hD
    exact (hD.weylScaling_log_lt_top_and_tendsto hα).1
  · filter_upwards [h𝔇.ae_isEuclideanLengthMetric_self hG] with ω hD
    exact (hD.weylScaling_log_lt_top_and_tendsto hα).2

/-- **Axiom III for the LQG metric of a field with a log singularity, `α₀ ≤ 0`.** For `ξ > 0` and `α₀ ≤ 0`, almost surely,
for every continuous `f`, `e^{ξ (f - α₀ log |·|)} · D_{h^ℂ} = e^{ξ f} · D_h`, where `D_h = e^{-ξ α₀ log |·|} · D_{h^ℂ}`. -/
theorem IsLQGMetric.ae_weylScaling_log_add_of_nonpos (h𝔇 : IsLQGMetric γ ξ 𝔇) (hG : IsWholePlaneGFF P hC hcirc)
    (hξ : 0 < ξ) {α₀ : ℝ} (hα : α₀ ≤ 0) :
    ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f → ∀ u v,
      weylScaling (𝔇 (hC ω)) ξ (fun x => f x - α₀ * Real.log ‖x‖) u v =
        weylScaling (fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal) ξ f u v := by
  refine h𝔇.ae_weylScaling_log_add hG hξ α₀ ?_
  filter_upwards [h𝔇.ae_isEuclideanLengthMetric_self hG] with ω hD
  exact (hD.weylScaling_log_lt_top_and_tendsto (mul_nonpos_of_nonneg_of_nonpos hξ.le hα)).1

end LatticeProb.LQG
