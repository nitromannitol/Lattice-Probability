import LatticeProb.Analysis.HeatKernel
import LatticeProb.Analysis.HeatMollify

/-!
# The heat equation with a compactly supported source

For a smooth compactly supported function on space-time, the heat operator produces a smooth
compactly supported source.
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff
open LatticeProb.WhiteNoise

namespace LatticeProb.Heat

/-- The inhomogeneity of the heat equation. -/
noncomputable def heatSource (d : ℕ) (v : ℝ × (Fin d → ℝ) → ℝ)
    (q : ℝ × (Fin d → ℝ)) : ℝ :=
  deriv (fun s => v (s, q.2)) q.1 - contOp d (fun y => v (q.1, y)) q.2

theorem heatSource_eq {d : ℕ} {v : ℝ × (Fin d → ℝ) → ℝ}
    (hv : ContDiff ℝ ∞ v) (q : ℝ × (Fin d → ℝ)) :
    heatSource d v q = fderiv ℝ v q (timeDir d) - spaceOp d v q := by
  rw [heatSource, (hasDerivAt_slice_time (hv.differentiable (by simp)) q.1 q.2).deriv]
  unfold contOp spaceOp
  rw [lap_slice hv]

theorem contDiff_heatSource {d : ℕ} {v : ℝ × (Fin d → ℝ) → ℝ}
    (hv : ContDiff ℝ ∞ v) : ContDiff ℝ ∞ (heatSource d v) := by
  have heq : heatSource d v = fun q => fderiv ℝ v q (timeDir d) - spaceOp d v q :=
    funext (heatSource_eq hv)
  rw [heq]
  apply (contDiff_fderiv_apply hv _).sub
  unfold spaceOp
  exact (ContDiff.sum fun i _ => contDiff_fderiv_apply (contDiff_fderiv_apply hv _) _).div_const _

theorem hasCompactSupport_heatSource {d : ℕ} {v : ℝ × (Fin d → ℝ) → ℝ}
    (hv : ContDiff ℝ ∞ v) (hs : HasCompactSupport v) : HasCompactSupport (heatSource d v) := by
  have heq : heatSource d v = fun q => fderiv ℝ v q (timeDir d) - spaceOp d v q :=
    funext (heatSource_eq hv)
  rw [heq]
  apply HasCompactSupport.sub
  · exact hs.fderiv_apply (𝕜 := ℝ) _
  · unfold spaceOp
    have hsum : HasCompactSupport (fun q => ∑ i : Fin d,
        fderiv ℝ (fun z => fderiv ℝ v z (spaceDir d i)) q (spaceDir d i)) := by
      have h := HasCompactSupport.finset_sum (s := Finset.univ)
        (fun i _ => (hs.fderiv_apply (𝕜 := ℝ) (spaceDir d i)).fderiv_apply (𝕜 := ℝ) (spaceDir d i))
      convert h using 1
      ext q
      simp only [Finset.sum_apply]
    have h := hsum.mul_right (f' := fun _ => (2 * (d : ℝ))⁻¹)
    convert h using 1
    ext q
    simp only [Pi.mul_apply, div_eq_mul_inv]

/-- The heat kernel recovers a bounded continuous space-time function when both time and space
approach the evaluation point. -/
theorem tendsto_integral_heatKernel_time {d : ℕ} (hd : 1 ≤ d)
    {v : ℝ × (Fin d → ℝ) → ℝ} (hv : Continuous v)
    (hb : ∃ M, ∀ q, |v q| ≤ M) (t : ℝ) (x : Fin d → ℝ) :
    Tendsto (fun τ => ∫ y : Fin d → ℝ, heatKernel d τ y * v (t - τ, x - y))
      (𝓝[>] 0) (𝓝 (v (t, x))) := by
  obtain ⟨M, hM⟩ := hb
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hΨint : Integrable (heatKernel d (d : ℝ)) := integrable_heatKernel hd hd'
  have hΨ1 : ∫ z, heatKernel d (d : ℝ) z = 1 := integral_heatKernel hd hd'
  have hσ : Tendsto (fun τ : ℝ => Real.sqrt (τ / d)) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun τ : ℝ => Real.sqrt (τ / d)) (𝓝 0) (𝓝 (Real.sqrt (0 / d))) :=
      ((continuous_id.div_const _).sqrt).tendsto 0
    simpa using h.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun τ : ℝ => ∫ z : Fin d → ℝ,
      heatKernel d (d : ℝ) z * v (t - τ, x - Real.sqrt (τ / d) • z)) (𝓝[>] 0)
      (𝓝 (∫ z : Fin d → ℝ, heatKernel d (d : ℝ) z * v (t, x))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun z => heatKernel d (d : ℝ) z * M) ?_ ?_ (hΨint.mul_const M) ?_
    · exact Eventually.of_forall fun τ => (show Continuous (fun z : Fin d → ℝ =>
        heatKernel d (d : ℝ) z * v (t - τ, x - Real.sqrt (τ / d) • z)) from
        (continuous_heatKernel hd').mul (hv.comp (by fun_prop))).aestronglyMeasurable
    · refine Eventually.of_forall fun τ => Eventually.of_forall fun z => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernel_nonneg hd _ _)]
      exact mul_le_mul_of_nonneg_left (hM _) (heatKernel_nonneg hd _ _)
    · refine Eventually.of_forall fun z => ?_
      refine tendsto_const_nhds.mul ?_
      have htime : Tendsto (fun τ : ℝ => t - τ) (𝓝[>] 0) (𝓝 t) := by
        simpa using (tendsto_const_nhds.sub (show Tendsto (fun τ : ℝ => τ) (𝓝[>] 0) (𝓝 0) from tendsto_id.mono_left nhdsWithin_le_nhds))
      have hspace : Tendsto (fun τ : ℝ => x - Real.sqrt (τ / d) • z) (𝓝[>] 0) (𝓝 x) := by
        simpa using tendsto_const_nhds.sub (hσ.smul_const z)
      exact (hv.tendsto (t, x)).comp (htime.prodMk_nhds hspace)
  have hint : ∫ z : Fin d → ℝ, heatKernel d (d : ℝ) z * v (t, x) = v (t, x) := by
    rw [integral_mul_const, hΨ1, one_mul]
  rw [hint] at hlim
  refine Tendsto.congr' ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  exact (integral_heatKernel_mul_eq hd hτ (fun y => v (t - τ, x - y))).symm

/-- The boundary term in the truncated heat-kernel formula converges to the function value. -/
theorem tendsto_integral_heatKernel_reflect_time {d : ℕ} (hd : 1 ≤ d)
    {v : ℝ × (Fin d → ℝ) → ℝ} (hv : Continuous v)
    (hb : ∃ M, ∀ q, |v q| ≤ M) (t : ℝ) (x : Fin d → ℝ) :
    Tendsto (fun τ => ∫ y : Fin d → ℝ, heatKernel d τ (x - y) * v (t - τ, y))
      (𝓝[>] 0) (𝓝 (v (t, x))) := by
  refine Tendsto.congr' ?_ (tendsto_integral_heatKernel_time hd hv hb t x)
  apply Eventually.of_forall
  intro τ
  simpa only [sub_sub_cancel] using
    (integral_sub_left_eq_self (fun y : Fin d → ℝ =>
      heatKernel d τ (x - y) * v (t - τ, y)) volume x)

end LatticeProb.Heat
