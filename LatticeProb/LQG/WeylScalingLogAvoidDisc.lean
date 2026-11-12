import LatticeProb.LQG.InternalMetricAvoidDisc
import LatticeProb.LQG.WeylChainBound
import LatticeProb.LQG.WeylScalingLogShellCriterion
import LatticeProb.LQG.ExpShellInternalDiamSummable
import LatticeProb.LQG.InternalMetricSquareTail

/-!
# Weyl scaling by a logarithmic weight: small circles about the origin have small internal diameters

Let `D` be a Euclidean length metric and `E = e^{ξ f} · D` its Weyl scaling by the logarithmic weight
`f(x) = -α₀ log |x|`, with `ξ ≥ 0`. On the `e^{-(k+2)}`-neighbourhood of the dyadic-exponential shell
`A_k = {e^{-(k+1)} ≤ |x| ≤ e^{-k}}` one has `ξ f ≤ ξ α₀ k + ξ |α₀| (2 + log 2)`, so the `E`-internal metric of that
neighbourhood is at most a constant times `e^{ξ α₀ k}` times the `D`-internal diameter of `A_k`. If these quantities are
summable in `k`, they tend to `0`, and the circles `|x| = e^{-k}` have arbitrarily small `E`-internal diameters inside
thin annuli avoiding the origin. This is the shell hypothesis of
`IsEuclideanLengthMetric.internalMetric_eq_iInf_diff_closedBall`; hence the internal metric of `E` on an open set,
between two nonzero points, is the infimum of its internal metrics on the set minus small closed discs about `0`.

For an LQG metric `𝔇` and a whole-plane GFF `h`, this holds almost surely for `D = 𝔇(h)` on the event where the
shell series is finite and `E` is a Euclidean length metric.

## Main results

* `IsEuclideanLengthMetric.exists_sphere_internalMetric_weylScaling_log_le`: the shell hypothesis for `E`.
* `IsEuclideanLengthMetric.internalMetric_weylScaling_log_eq_iInf_diff_closedBall`: the deterministic identity.
* `IsLQGMetric.ae_internalMetric_weylScaling_log_eq_iInf_diff_closedBall`: its almost sure form.
-/

open MeasureTheory Filter Set Metric LatticeProb.Gauss
open scoped ENNReal Topology

namespace LatticeProb.LQG

variable {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- On the `e^{-(k+2)}`-neighbourhood of the shell `A_k`, the logarithmic weight satisfies
`ξ (-α₀ log |x|) ≤ ξ α₀ k + ξ |α₀| (2 + log 2)`. -/
theorem weight_log_le_of_mem_thickening_expShell {ξ α₀ : ℝ} (hξ : 0 ≤ ξ) {k : ℕ} {z : ℂ}
    (hz : z ∈ Metric.thickening (Real.exp (-((k : ℝ) + 2))) (expShell k)) :
    ξ * (-α₀ * Real.log ‖z‖) ≤ ξ * α₀ * (k : ℝ) + ξ * |α₀| * (2 + Real.log 2) := by
  obtain ⟨h1, h2⟩ := norm_bounds_of_mem_thickening_expShell hz
  have hpos : 0 < ‖z‖ := lt_trans (Real.exp_pos _) h1
  have hl1 : -((k : ℝ) + 2) < Real.log ‖z‖ := (Real.lt_log_iff_exp_lt hpos).2 h1
  have hl2 : Real.log ‖z‖ < Real.log 2 + -(k : ℝ) := by
    rw [Real.log_lt_iff_lt_exp hpos, Real.exp_add, Real.exp_log two_pos]
    exact h2
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have habs : |Real.log ‖z‖ + k| ≤ 2 + Real.log 2 := abs_le.2 ⟨by linarith, by linarith⟩
  have key : -α₀ * (Real.log ‖z‖ + k) ≤ |α₀| * (2 + Real.log 2) :=
    calc -α₀ * (Real.log ‖z‖ + k) ≤ |-α₀ * (Real.log ‖z‖ + k)| := le_abs_self _
      _ = |α₀| * |Real.log ‖z‖ + k| := by rw [abs_mul, abs_neg]
      _ ≤ |α₀| * (2 + Real.log 2) := mul_le_mul_of_nonneg_left habs (abs_nonneg _)
  have key' := mul_le_mul_of_nonneg_left key hξ
  calc ξ * (-α₀ * Real.log ‖z‖) = ξ * α₀ * (k : ℝ) + ξ * (-α₀ * (Real.log ‖z‖ + k)) := by ring
    _ ≤ ξ * α₀ * (k : ℝ) + ξ * (|α₀| * (2 + Real.log 2)) := by linarith
    _ = ξ * α₀ * (k : ℝ) + ξ * |α₀| * (2 + Real.log 2) := by ring

/-- Shell hypothesis for the Weyl scaling `E = e^{ξ f} · D` by `f(x) = -α₀ log |x|`: if the series
`∑_k e^{ξ α₀ k} diam^{e^{-(k+2)}}_D(A_k)` is finite, then for every `ε > 0` and `R > 0` there are radii
`0 < ρ' < r < R` and a set `A` inside `ρ' < |x| < R` in which any two points of the circle `|x| = r` are at
`E`-internal distance at most `ε` (take `r = e^{-k}`, `ρ' = e^{-(k+2)}`, `A` the `e^{-(k+2)}`-neighbourhood of `A_k`). -/
theorem IsEuclideanLengthMetric.exists_sphere_internalMetric_weylScaling_log_le {D E : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) {ξ α₀ : ℝ} (hξ : 0 ≤ ξ)
    (hscale : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ (fun x => -α₀ * Real.log ‖x‖) x y)
    (hsum : ∑' k : ℕ, ENNReal.ofReal (Real.exp (ξ * α₀ * (k : ℝ))) *
      internalDiam D (Real.exp (-((k : ℝ) + 2))) (expShell k) ≠ ∞) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∀ R : ℝ, 0 < R → ∃ r ρ' : ℝ, 0 < ρ' ∧ ρ' < r ∧ r < R ∧
      ∃ A ⊆ ball (0 : ℂ) R \ closedBall 0 ρ',
        ∀ a ∈ sphere (0 : ℂ) r, ∀ b ∈ sphere (0 : ℂ) r, internalMetric E A a b ≤ ε := by
  intro ε hε R hR
  set C : ℝ := ξ * |α₀| * (2 + Real.log 2) with hC
  have hu := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hsum
  have hu' : Tendsto (fun k : ℕ => ENNReal.ofReal (Real.exp C) *
      (ENNReal.ofReal (Real.exp (ξ * α₀ * (k : ℝ))) *
        internalDiam D (Real.exp (-((k : ℝ) + 2))) (expShell k))) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hu (Or.inr ENNReal.ofReal_ne_top)
  have hexp : Tendsto (fun k : ℕ => 2 * Real.exp (-(k : ℝ))) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop).const_mul 2
  obtain ⟨k, hk1, hk2⟩ := ((hu'.eventually (gt_mem_nhds hε)).and (hexp.eventually (gt_mem_nhds hR))).exists
  have hek := Real.exp_pos (-(k : ℝ))
  refine ⟨Real.exp (-(k : ℝ)), Real.exp (-((k : ℝ) + 2)), Real.exp_pos _,
    Real.exp_lt_exp.2 (by linarith), by linarith,
    Metric.thickening (Real.exp (-((k : ℝ) + 2))) (expShell k), ?_, ?_⟩
  · intro x hx
    obtain ⟨h1, h2⟩ := norm_bounds_of_mem_thickening_expShell hx
    refine ⟨mem_ball_zero_iff.2 (by linarith), fun h => ?_⟩
    exact absurd (mem_closedBall_zero_iff.1 h) (not_le.2 h1)
  · have hsub : sphere (0 : ℂ) (Real.exp (-(k : ℝ))) ⊆ expShell k := fun a ha => by
      have ha' := mem_sphere_zero_iff_norm.1 ha
      exact ⟨by rw [ha']; exact Real.exp_le_exp.2 (by linarith), ha'.le⟩
    intro a ha b hb
    calc internalMetric E (Metric.thickening (Real.exp (-((k : ℝ) + 2))) (expShell k)) a b
        ≤ ENNReal.ofReal (Real.exp (ξ * α₀ * (k : ℝ) + C)) *
          internalMetric D (Metric.thickening (Real.exp (-((k : ℝ) + 2))) (expShell k)) a b :=
          internalMetric_le_of_weylScaling hD hscale
            (fun z hz => weight_log_le_of_mem_thickening_expShell hξ hz) a b
      _ ≤ ENNReal.ofReal (Real.exp (ξ * α₀ * (k : ℝ) + C)) *
          internalDiam D (Real.exp (-((k : ℝ) + 2))) (expShell k) := by
          gcongr
          exact le_iSup₂_of_le a (hsub ha) (le_iSup₂_of_le b (hsub hb) le_rfl)
      _ = ENNReal.ofReal (Real.exp C) * (ENNReal.ofReal (Real.exp (ξ * α₀ * (k : ℝ))) *
          internalDiam D (Real.exp (-((k : ℝ) + 2))) (expShell k)) := by
          rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
          ring
      _ ≤ ε := hk1.le

/-- Deterministic identity: if `E = e^{ξ f} · D` (`f(x) = -α₀ log |x|`, `ξ ≥ 0`) is a Euclidean length metric and the
shell series `∑_k e^{ξ α₀ k} diam^{e^{-(k+2)}}_D(A_k)` is finite, then for every open `U`, nonzero `z, w` and radii
`ρ_n → 0`, `E(z, w; U) = inf_n E(z, w; U \ closedBall 0 ρ_n)`. -/
theorem IsEuclideanLengthMetric.internalMetric_weylScaling_log_eq_iInf_diff_closedBall {D E : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) (hE : IsEuclideanLengthMetric E) {ξ α₀ : ℝ} (hξ : 0 ≤ ξ)
    (hscale : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ (fun x => -α₀ * Real.log ‖x‖) x y)
    (hsum : ∑' k : ℕ, ENNReal.ofReal (Real.exp (ξ * α₀ * (k : ℝ))) *
      internalDiam D (Real.exp (-((k : ℝ) + 2))) (expShell k) ≠ ∞)
    {U : Set ℂ} (hU : IsOpen U) {ρ : ℕ → ℝ} (hρ : Tendsto ρ atTop (𝓝 0)) {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) :
    internalMetric E U z w = ⨅ n, internalMetric E (U \ closedBall 0 (ρ n)) z w :=
  hE.internalMetric_eq_iInf_diff_closedBall hU hρ
    (hD.exists_sphere_internalMetric_weylScaling_log_le hξ hscale hsum) hz hw

/-- Almost sure form for an LQG metric `𝔇` and a whole-plane GFF `h`: on the event where the shell series of `𝔇(h)` is
finite and `E = e^{ξ f} · 𝔇(h)` (`f(x) = -α₀ log |x|`) is finite and a Euclidean length metric, for every open `U`,
nonzero `z, w` and radii `ρ_n → 0`, `E(z, w; U) = inf_n E(z, w; U \ closedBall 0 ρ_n)`. -/
theorem IsLQGMetric.ae_internalMetric_weylScaling_log_eq_iInf_diff_closedBall (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hG : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ2 : γ < 2) {α₀ : ℝ}
    (hsum : ∀ᵐ ω ∂P, ∑' k : ℕ, ENNReal.ofReal (Real.exp (ξ * α₀ * (k : ℝ))) *
      internalDiam (𝔇 (hC ω)) (Real.exp (-((k : ℝ) + 2))) (expShell k) ≠ ∞)
    (hI : ∀ᵐ ω ∂P, (∀ u v, weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v < ∞) ∧
      IsEuclideanLengthMetric fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal)
    {ρ : ℕ → ℝ} (hρ : Tendsto ρ atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → ∀ z w : ℂ, z ≠ 0 → w ≠ 0 →
      internalMetric (fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal) U z w =
        ⨅ n, internalMetric
          (fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal)
          (U \ closedBall 0 (ρ n)) z w := by
  have hξ := (h𝔇.xi_pos hγ hγ2).le
  filter_upwards [hsum, hI, h𝔇.ae_isEuclideanLengthMetric_self hG] with ω hs hω hD
  intro U hU z w hz hw
  exact hD.internalMetric_weylScaling_log_eq_iInf_diff_closedBall hω.2 hξ
    (fun x y => ENNReal.ofReal_toReal (hω.1 x y).ne) hs hU hρ hz hw

end LatticeProb.LQG
