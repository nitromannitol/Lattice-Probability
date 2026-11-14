import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Finite measures are determined by smooth compactly supported test functions

Let `E` be a finite-dimensional real normed space with its Borel σ-algebra. Two finite measures `μ`
and `ν` on `E` with `∫ g dμ = ∫ g dν` for every smooth compactly supported `g : E → ℝ` are equal
(`LatticeProb.measure_eq_of_forall_integral_contDiff_hasCompactSupport_eq`).

Proof. By `MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure` it suffices to test bounded
continuous `f`. Put `gₙ = χₙ · (φₙ ⋆ f)`, with `φₙ` the normalized bump of outer radius `1/(n+1)`
(convolution with respect to a Haar measure) and `χₙ` a bump equal to `1` on the closed ball of
radius `n + 1`. Each `gₙ` is smooth with compact support, `gₙ → f` pointwise, and
`|gₙ| ≤ 3 ‖f‖`; dominated convergence under `μ` and under `ν` gives `∫ f dμ = ∫ f dν`.
-/

open MeasureTheory Filter Metric Topology ContinuousLinearMap
open scoped ContDiff Convolution BoundedContinuousFunction

namespace LatticeProb

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The mollifying bump of inner radius `1/(n+2)` and outer radius `1/(n+1)`. -/
noncomputable def mollifierBump (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) :
    ContDiffBump (0 : E) :=
  ⟨1 / ((n : ℝ) + 2), 1 / ((n : ℝ) + 1), by positivity,
    one_div_lt_one_div_of_lt (by positivity) (by linarith)⟩

/-- The cut-off bump of inner radius `n + 1` and outer radius `n + 2`. -/
noncomputable def cutoffBump (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) :
    ContDiffBump (0 : E) :=
  ⟨(n : ℝ) + 1, (n : ℝ) + 2, by positivity, by linarith⟩

/-- The smooth compactly supported approximants `χₙ · (φₙ ⋆ f)` of a function `f`. -/
noncomputable def smoothCutoffApprox (f : E → ℝ) (n : ℕ) (x : E) : ℝ :=
  cutoffBump E n x *
    (((mollifierBump E n).normed (Measure.addHaar : Measure E)) ⋆[lsmul ℝ ℝ, Measure.addHaar] f) x

theorem contDiff_smoothCutoffApprox {f : E → ℝ} (hf : Continuous f) (n : ℕ) :
    ContDiff ℝ ∞ (smoothCutoffApprox f n) :=
  (cutoffBump E n).contDiff.mul
    ((mollifierBump E n).hasCompactSupport_normed.contDiff_convolution_left _
      (mollifierBump E n).contDiff_normed hf.locallyIntegrable)

theorem hasCompactSupport_smoothCutoffApprox (f : E → ℝ) (n : ℕ) :
    HasCompactSupport (smoothCutoffApprox f n) :=
  (cutoffBump E n).hasCompactSupport.mul_right

/-- The approximants of a bounded continuous function are bounded by `3 ‖f‖`. -/
theorem norm_smoothCutoffApprox_le (f : E →ᵇ ℝ) (n : ℕ) (x : E) :
    ‖smoothCutoffApprox (⇑f) n x‖ ≤ 3 * ‖f‖ := by
  have hd := (mollifierBump E n).dist_normed_convolution_le (μ := (Measure.addHaar : Measure E))
    (x₀ := x) f.continuous.aestronglyMeasurable (fun y _ => f.dist_le_two_norm y x)
  rw [dist_eq_norm] at hd
  have h1 : ‖(((mollifierBump E n).normed (Measure.addHaar : Measure E)) ⋆[lsmul ℝ ℝ,
      Measure.addHaar] ⇑f) x‖ ≤ 3 * ‖f‖ := by
    calc _ ≤ ‖f x‖ + ‖(((mollifierBump E n).normed (Measure.addHaar : Measure E)) ⋆[lsmul ℝ ℝ,
          Measure.addHaar] ⇑f) x - f x‖ := norm_le_norm_add_norm_sub' _ _
      _ ≤ ‖f‖ + 2 * ‖f‖ := add_le_add (f.norm_coe_le_norm x) hd
      _ = 3 * ‖f‖ := by ring
  have hχ : ‖cutoffBump E n x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (cutoffBump E n).nonneg]
    exact (cutoffBump E n).le_one
  unfold smoothCutoffApprox
  rw [norm_mul]
  calc _ ≤ 1 * (3 * ‖f‖) := mul_le_mul hχ h1 (norm_nonneg _) zero_le_one
    _ = 3 * ‖f‖ := one_mul _

/-- The approximants of a continuous function converge to it pointwise. -/
theorem tendsto_smoothCutoffApprox {f : E → ℝ} (hf : Continuous f) (x : E) :
    Tendsto (fun n => smoothCutoffApprox f n x) atTop (𝓝 (f x)) := by
  have h1 : Tendsto (fun n => cutoffBump E n x) atTop (𝓝 1) := by
    obtain ⟨N, hN⟩ := exists_nat_ge ‖x‖
    refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
    refine ((cutoffBump E n).one_of_mem_closedBall ?_).symm
    rw [mem_closedBall, dist_zero_right]
    have hn' : (N : ℝ) ≤ n := Nat.cast_le.2 hn
    change ‖x‖ ≤ (n : ℝ) + 1
    linarith
  have h2 := ContDiffBump.convolution_tendsto_right_of_continuous (μ := (Measure.addHaar : Measure E))
    (φ := mollifierBump E) (l := atTop) tendsto_one_div_add_atTop_nhds_zero_nat hf x
  have h3 := h1.mul h2
  rw [one_mul] at h3
  exact h3

/-- **Finite measures are determined by smooth compactly supported tests.** Two finite measures on a
finite-dimensional real normed space that integrate every smooth compactly supported real function
to the same value are equal. -/
theorem measure_eq_of_forall_integral_contDiff_hasCompactSupport_eq {μ ν : Measure E}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ g : E → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → ∫ x, g x ∂μ = ∫ x, g x ∂ν) :
    μ = ν := by
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  have hlim : ∀ ρ : Measure E, IsFiniteMeasure ρ →
      Tendsto (fun n => ∫ x, smoothCutoffApprox (⇑f) n x ∂ρ) atTop (𝓝 (∫ x, f x ∂ρ)) :=
    fun ρ _ => tendsto_integral_of_dominated_convergence (fun _ => 3 * ‖f‖)
      (fun n => (contDiff_smoothCutoffApprox f.continuous n).continuous.aestronglyMeasurable)
      (integrable_const _) (fun n => Eventually.of_forall (norm_smoothCutoffApprox_le f n))
      (Eventually.of_forall (tendsto_smoothCutoffApprox f.continuous))
  refine tendsto_nhds_unique (hlim μ inferInstance) ?_
  refine (hlim ν inferInstance).congr fun n => ?_
  exact (h _ (contDiff_smoothCutoffApprox f.continuous n)
    (hasCompactSupport_smoothCutoffApprox _ n)).symm

end LatticeProb
