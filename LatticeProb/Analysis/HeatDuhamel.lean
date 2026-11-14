import LatticeProb.Analysis.HeatKernel
import LatticeProb.Analysis.HeatMollify

/-!
# The heat equation with a compactly supported source

The heat operator maps smooth compactly supported functions to smooth compactly supported sources.
The reflected heat kernel solves the backward heat equation, and the spatial heat operator is
symmetric against compactly supported smooth functions. The heat-kernel boundary integral
converges to the original function as time tends to zero.
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

/-- The spatial heat operator commutes with reflection about a point. -/
theorem contOp_comp_sub_left {d : ℕ} {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (x y : Fin d → ℝ) :
    contOp d (fun z => f (x - z)) y = contOp d f (x - y) := by
  let F : ℝ × (Fin d → ℝ) → ℝ := fun q => f q.2
  have hF : ContDiff ℝ ∞ F := hf.comp contDiff_snd
  have hG : ContDiff ℝ ∞ (fun q : ℝ × (Fin d → ℝ) => F ((0, x) - q)) :=
    hF.comp (contDiff_const.sub contDiff_id)
  unfold contOp
  have h1 := lap_slice hG 0 y
  have h2 := lap_slice hF 0 (x - y)
  change lap (fun z => f (x - z)) y = _ at h1
  change lap f (x - y) = _ at h2
  rw [h1, h2]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simpa only [Prod.mk_sub_mk, sub_zero] using
    (fderiv_fderiv_comp_sub_left_apply hF (0, x) (0, y) (spaceDir d i) (spaceDir d i))

/-- At positive time the heat kernel is smooth as a function of the spatial variable. -/
theorem contDiff_heatKernel_space {d : ℕ} (hd : 1 ≤ d) {τ : ℝ} (hτ : 0 < τ) :
    ContDiff ℝ ∞ (heatKernel d τ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have hu : IsOpen {p : ℝ × (Fin d → ℝ) | 0 < p.1} :=
    isOpen_lt continuous_const continuous_fst
  have h := (contDiffOn_heatKernel hd).contDiffAt (hu.mem_nhds (show (τ, x) ∈ {p : ℝ × (Fin d → ℝ) | 0 < p.1} from hτ))
  exact h.comp x ((contDiffAt_const.prodMk contDiffAt_id))

/-- The reflected kernel satisfies the backward heat equation at positive time. -/
theorem hasDerivAt_heatKernel_backward {d : ℕ} (hd : 1 ≤ d)
    {s t : ℝ} (hst : s < t) (x y : Fin d → ℝ) :
    HasDerivAt (fun r => heatKernel d (t - r) (x - y))
      (-contOp d (fun z => heatKernel d (t - s) (x - z)) y) s := by
  have hp : 0 < t - s := sub_pos.mpr hst
  have h := (heatKernel_hasDerivAt hd (x - y) hp).comp s ((hasDerivAt_id s).const_sub t)
  rw [contOp_comp_sub_left (contDiff_heatKernel_space hd hp)]
  simpa only [Function.comp_def, mul_neg, mul_one] using h

/-- Coordinate second derivatives agree with the iterated Fréchet derivatives. -/
theorem lap_eq_sum_fderiv {d : ℕ} {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (x : Fin d → ℝ) :
    lap f x = ∑ i : Fin d, fderiv ℝ (fun z => fderiv ℝ f z (Pi.single i 1)) x (Pi.single i 1) := by
  unfold lap
  refine Finset.sum_congr rfl fun i _ => ?_
  have hslice (g : (Fin d → ℝ) → ℝ) (hg : Differentiable ℝ g) (t : ℝ) :
      HasDerivAt (fun t => g (Function.update x i t))
        (fderiv ℝ g (Function.update x i t) (Pi.single i 1)) t :=
    (hg _).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_update x i t)
  have h1 : (fun t => deriv (fun t' => f (Function.update x i t')) t) =
      fun t => fderiv ℝ f (Function.update x i t) (Pi.single i 1) := by
    funext t
    exact (hslice f (hf.differentiable (by simp)) t).deriv
  rw [h1]
  have h2 := hslice (fun z => fderiv ℝ f z (Pi.single i 1))
    ((contDiff_fderiv_apply hf _).differentiable (by simp)) (x i)
  rw [Function.update_eq_self] at h2
  exact h2.deriv

private theorem integral_mul_fderiv_eq_neg {d : ℕ} {f g : (Fin d → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (w : Fin d → ℝ) :
    ∫ y, f y * fderiv ℝ g y w = -∫ y, fderiv ℝ f y w * g y := by
  have hf' := (contDiff_fderiv_apply hf w).continuous
  have hg' := (contDiff_fderiv_apply hg w).continuous
  have hgc' := hgc.fderiv_apply ℝ w
  refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_
    (fun y _ => hf.differentiable (by simp) y) (fun y _ => hg.differentiable (by simp) y)
  · exact (hf'.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
  · exact (hf.continuous.mul hg').integrable_of_hasCompactSupport hgc'.mul_left
  · exact (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left

private theorem integral_mul_fderiv_fderiv_eq {d : ℕ} {f g : (Fin d → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (w : Fin d → ℝ) :
    ∫ y, f y * fderiv ℝ (fun z => fderiv ℝ g z w) y w =
      ∫ y, fderiv ℝ (fun z => fderiv ℝ f z w) y w * g y := by
  have h1 := integral_mul_fderiv_eq_neg hf (contDiff_fderiv_apply hg w) (hgc.fderiv_apply ℝ w) w
  have h2 := integral_mul_fderiv_eq_neg (contDiff_fderiv_apply hf w) hg hgc w
  rw [h1, h2, neg_neg]

/-- The spatial heat operator is symmetric against a compactly supported smooth function. -/
theorem integral_mul_contOp {d : ℕ} {f g : (Fin d → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    ∫ y, f y * contOp d g y = ∫ y, contOp d f y * g y := by
  unfold contOp
  simp_rw [lap_eq_sum_fderiv hg, lap_eq_sum_fderiv hf]
  have hi : ∀ i : Fin d, Integrable (fun y => f y *
      fderiv ℝ (fun z => fderiv ℝ g z (Pi.single i 1)) y (Pi.single i 1)) := fun i =>
    (hf.continuous.mul (contDiff_fderiv_apply (contDiff_fderiv_apply hg _) _).continuous)
      |>.integrable_of_hasCompactSupport (((hgc.fderiv_apply ℝ _).fderiv_apply ℝ _).mul_left)
  have hj : ∀ i : Fin d, Integrable (fun y =>
      fderiv ℝ (fun z => fderiv ℝ f z (Pi.single i 1)) y (Pi.single i 1) * g y) := fun i =>
    ((contDiff_fderiv_apply (contDiff_fderiv_apply hf _) _).continuous.mul hg.continuous)
      |>.integrable_of_hasCompactSupport hgc.mul_left
  have e1 : ∀ y, f y * ((∑ i : Fin d,
      fderiv ℝ (fun z => fderiv ℝ g z (Pi.single i 1)) y (Pi.single i 1)) / (2 * d)) =
      (∑ i : Fin d, f y * fderiv ℝ (fun z => fderiv ℝ g z (Pi.single i 1)) y (Pi.single i 1)) /
        (2 * d) := fun y => by rw [mul_div_assoc', Finset.mul_sum]
  have e2 : ∀ y, (∑ i : Fin d,
      fderiv ℝ (fun z => fderiv ℝ f z (Pi.single i 1)) y (Pi.single i 1)) / (2 * d) * g y =
      (∑ i : Fin d, fderiv ℝ (fun z => fderiv ℝ f z (Pi.single i 1)) y (Pi.single i 1) * g y) /
        (2 * d) := fun y => by rw [div_mul_eq_mul_div, Finset.sum_mul]
  simp_rw [e1, e2]
  rw [integral_div, integral_div, integral_finsetSum _ fun i _ => hi i,
    integral_finsetSum _ fun i _ => hj i]
  congr 1
  exact Finset.sum_congr rfl fun i _ => integral_mul_fderiv_fderiv_eq hf hg hgc _

/-- Every spatial slice of a compactly supported space-time function has compact support. -/
theorem hasCompactSupport_space_slice {d : ℕ} {v : ℝ × (Fin d → ℝ) → ℝ}
    (hv : HasCompactSupport v) (s : ℝ) : HasCompactSupport (fun y => v (s, y)) := by
  apply (hv.image continuous_snd).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ (hv.image continuous_snd).isClosed
  intro y hy
  have h : (s, y) ∈ tsupport v := subset_tsupport _ (by simpa using hy)
  exact ⟨(s, y), h, rfl⟩

/-- The spatial integration-by-parts identity for a positive-time heat kernel. -/
theorem integral_heatKernel_mul_contOp {d : ℕ} (hd : 1 ≤ d) {τ : ℝ} (hτ : 0 < τ)
    {v : ℝ × (Fin d → ℝ) → ℝ} (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v)
    (s : ℝ) (x : Fin d → ℝ) :
    ∫ y, heatKernel d τ (x - y) * contOp d (fun z => v (s, z)) y =
      ∫ y, contOp d (fun z => heatKernel d τ (x - z)) y * v (s, y) := by
  apply integral_mul_contOp
  · exact (contDiff_heatKernel_space hd hτ).comp (contDiff_const.sub contDiff_id)
  · exact hv.comp (contDiff_const.prodMk contDiff_id)
  · exact hasCompactSupport_space_slice hvc s

end LatticeProb.Heat
