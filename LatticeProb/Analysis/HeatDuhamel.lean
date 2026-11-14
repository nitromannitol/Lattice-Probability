import LatticeProb.Analysis.HeatKernel
import LatticeProb.Analysis.HeatMollify

/-!
# The heat equation with a compactly supported source

The heat operator maps smooth compactly supported functions to smooth compactly supported sources.
The reflected heat kernel solves the backward heat equation, and the spatial heat operator is
symmetric against compactly supported smooth functions. The resulting Duhamel formula expresses
a smooth compactly supported function as the heat convolution of its source.
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

/-- Time derivative of the kernel times a smooth function at positive time. -/
theorem hasDerivAt_heatKernel_mul {d : ℕ} (hd : 1 ≤ d)
    {v : ℝ × (Fin d → ℝ) → ℝ} (hv : ContDiff ℝ ∞ v)
    {s t : ℝ} (hst : s < t) (x y : Fin d → ℝ) :
    HasDerivAt (fun r => heatKernel d (t - r) (x - y) * v (r, y))
      ((-contOp d (fun z => heatKernel d (t - s) (x - z)) y) * v (s, y) +
        heatKernel d (t - s) (x - y) * deriv (fun r => v (r, y)) s) s := by
  have hv' := hasDerivAt_slice_time (hv.differentiable (by simp)) s y
  rw [hv'.deriv]
  exact (hasDerivAt_heatKernel_backward hd hst x y).mul hv'


/-- The source of a smooth function is supported where the function is supported. -/
theorem tsupport_heatSource_subset {d : ℕ} {v : ℝ × (Fin d → ℝ) → ℝ}
    (hv : ContDiff ℝ ∞ v) : tsupport (heatSource d v) ⊆ tsupport v := by
  apply closure_minimal _ (isClosed_tsupport v)
  intro q hq
  by_contra hqv
  have hzero : fderiv ℝ v q = 0 := fderiv_of_notMem_tsupport ℝ hqv
  have hzero₂ (i : Fin d) :
      fderiv ℝ (fun z => fderiv ℝ v z (spaceDir d i)) q = 0 :=
    fderiv_of_notMem_tsupport ℝ fun h => hqv ((tsupport_fderiv_apply_subset (ρ := v) _) h)
  have : heatSource d v q = 0 := by
    rw [heatSource_eq hv]
    simp [spaceOp, hzero, hzero₂]
  exact hq this


/-- A compactly supported function and its heat source vanish outside a bounded time interval. -/
theorem exists_heatSource_time_bound {d : ℕ} {v : ℝ × (Fin d → ℝ) → ℝ}
    (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) :
    ∃ R > 0, ∀ q, R < |q.1| → v q = 0 ∧ heatSource d v q = 0 := by
  obtain ⟨R, hR, hbound⟩ := (hvc.image continuous_fst).isBounded.exists_pos_norm_le
  refine ⟨R, hR, fun q hq => ?_⟩
  have hqv : q ∉ tsupport v := by
    intro hmem
    have h := hbound q.1 ⟨q, hmem, rfl⟩
    rw [Real.norm_eq_abs] at h
    exact (not_le_of_gt hq) h
  exact ⟨image_eq_zero_of_notMem_tsupport hqv, image_eq_zero_of_notMem_tsupport
    (fun h => hqv ((tsupport_heatSource_subset hv) h))⟩


/-- All time slices of a compactly supported function and its time derivative have a common
compact spatial support. -/
theorem exists_compact_space_support {d : ℕ} {v : ℝ × (Fin d → ℝ) → ℝ}
    (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) :
    ∃ K : Set (Fin d → ℝ), IsCompact K ∧ ∀ s y, y ∉ K →
      v (s, y) = 0 ∧ deriv (fun r => v (r, y)) s = 0 := by
  refine ⟨Prod.snd '' tsupport v, hvc.image continuous_snd, ?_⟩
  intro s y hy
  have hq : (s, y) ∉ tsupport v := fun h => hy ⟨(s, y), h, rfl⟩
  refine ⟨image_eq_zero_of_notMem_tsupport hq, ?_⟩
  rw [(hasDerivAt_slice_time (hv.differentiable (by simp)) s y).deriv,
    fderiv_of_notMem_tsupport ℝ hq]
  simp


/-- The spatial heat operator preserves smoothness. -/
theorem contDiff_contOp {d : ℕ} {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (contOp d f) := by
  have heq : contOp d f = fun y => (∑ i : Fin d,
      fderiv ℝ (fun z => fderiv ℝ f z (Pi.single i 1)) y (Pi.single i 1)) / (2 * d) := by
    funext y
    simp only [contOp, lap_eq_sum_fderiv hf]
  rw [heq]
  exact (ContDiff.sum fun i _ => contDiff_fderiv_apply (contDiff_fderiv_apply hf _) _).div_const _



/-- The spatial heat operator preserves compact support. -/
theorem hasCompactSupport_contOp {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) : HasCompactSupport (contOp d f) := by
  have hs : HasCompactSupport (fun y => ∑ i : Fin d,
      fderiv ℝ (fun z => fderiv ℝ f z (Pi.single i 1)) y (Pi.single i 1)) := by
    have h := HasCompactSupport.finset_sum (s := Finset.univ)
      (fun i _ => (hfc.fderiv_apply ℝ (Pi.single i 1)).fderiv_apply ℝ (Pi.single i 1))
    convert h using 1
    ext y
    simp only [Finset.sum_apply]
  have h := hs.mul_right (f' := fun _ => (2 * (d : ℝ))⁻¹)
  convert h using 1
  ext y
  simp only [Pi.mul_apply, contOp, lap_eq_sum_fderiv hf, div_eq_mul_inv]

/-- Spatial integration by parts identifies the integral of the kernel-product derivative with
the integral of the heat source. -/
theorem integral_heatKernel_mul_time_deriv_eq {d : ℕ} (hd : 1 ≤ d)
    {v : ℝ × (Fin d → ℝ) → ℝ} (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v)
    {s t : ℝ} (hst : s < t) (x : Fin d → ℝ) :
    (∫ y, (-contOp d (fun z => heatKernel d (t - s) (x - z)) y) * v (s, y) +
      heatKernel d (t - s) (x - y) * deriv (fun r => v (r, y)) s) =
    ∫ y, heatKernel d (t - s) (x - y) * heatSource d v (s, y) := by
  have hp : 0 < t - s := sub_pos.mpr hst
  have hk : ContDiff ℝ ∞ (fun y => heatKernel d (t - s) (x - y)) :=
    (contDiff_heatKernel_space hd hp).comp (contDiff_const.sub contDiff_id)
  have hvs : ContDiff ℝ ∞ (fun y => v (s, y)) := hv.comp (contDiff_const.prodMk contDiff_id)
  have hvsc : HasCompactSupport (fun y => v (s, y)) := hasCompactSupport_space_slice hvc s
  have hvt_eq : (fun y => deriv (fun r => v (r, y)) s) =
      fun y => fderiv ℝ v (s, y) (timeDir d) := by
    funext y
    exact (hasDerivAt_slice_time (hv.differentiable (by simp)) s y).deriv
  have hvt : ContDiff ℝ ∞ (fun y => deriv (fun r => v (r, y)) s) := by
    rw [hvt_eq]
    exact (contDiff_fderiv_apply hv _).comp (contDiff_const.prodMk contDiff_id)
  have hvtc : HasCompactSupport (fun y => deriv (fun r => v (r, y)) s) := by
    rw [hvt_eq]
    exact hasCompactSupport_space_slice (hvc.fderiv_apply ℝ _) s
  have hi₁ : Integrable (fun y => contOp d (fun z => heatKernel d (t - s) (x - z)) y * v (s, y)) :=
    ((contDiff_contOp hk).continuous.mul hvs.continuous).integrable_of_hasCompactSupport hvsc.mul_left
  have hi₂ : Integrable (fun y => heatKernel d (t - s) (x - y) * deriv (fun r => v (r, y)) s) :=
    (hk.continuous.mul hvt.continuous).integrable_of_hasCompactSupport hvtc.mul_left
  have hi₃ : Integrable (fun y => heatKernel d (t - s) (x - y) * contOp d (fun z => v (s, z)) y) :=
    (hk.continuous.mul (contDiff_contOp hvs).continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_contOp hvs hvsc).mul_left
  have hi₁n : Integrable (fun y => -(contOp d (fun z => heatKernel d (t - s) (x - z)) y * v (s, y))) := hi₁.neg
  simp_rw [neg_mul]
  rw [integral_add hi₁n hi₂, integral_neg,
    ← integral_heatKernel_mul_contOp hd hp hv hvc s x, neg_add_eq_sub, ← integral_sub hi₂ hi₃]
  apply integral_congr_ae
  filter_upwards with y
  simp only [heatSource, mul_sub]


/-- The derivative of the spatial heat-kernel integral, under a local integrable derivative bound. -/
theorem hasDerivAt_integral_heatKernel_mul_of_dominated {d : ℕ} (hd : 1 ≤ d)
    {v : ℝ × (Fin d → ℝ) → ℝ} (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v)
    {s t : ℝ} (hst : s < t) (x : Fin d → ℝ) {U : Set ℝ} (hU : U ∈ 𝓝 s)
    (hUt : U ⊆ Iio t) {bound : (Fin d → ℝ) → ℝ} (hbi : Integrable bound)
    (hb : ∀ᵐ y, ∀ r ∈ U, ‖(-contOp d (fun z => heatKernel d (t - r) (x - z)) y) * v (r, y) +
      heatKernel d (t - r) (x - y) * deriv (fun q => v (q, y)) r‖ ≤ bound y) :
    HasDerivAt (fun r => ∫ y, heatKernel d (t - r) (x - y) * v (r, y))
      (∫ y, heatKernel d (t - s) (x - y) * heatSource d v (s, y)) s := by
  have hcont (r : ℝ) (hrt : r < t) :
      ContDiff ℝ ∞ (fun y => heatKernel d (t - r) (x - y)) :=
    (contDiff_heatKernel_space hd (sub_pos.mpr hrt)).comp (contDiff_const.sub contDiff_id)
  have hslice (r : ℝ) : ContDiff ℝ ∞ (fun y => v (r, y)) :=
    hv.comp (contDiff_const.prodMk contDiff_id)
  have htime : Continuous (fun y => deriv (fun r => v (r, y)) s) := by
    have heq : (fun y => deriv (fun r => v (r, y)) s) =
        fun y => fderiv ℝ v (s, y) (timeDir d) := by
      funext y
      exact (hasDerivAt_slice_time (hv.differentiable (by simp)) s y).deriv
    rw [heq]
    exact ((contDiff_fderiv_apply hv _).comp (contDiff_const.prodMk contDiff_id)).continuous
  have hmeas : ∀ᶠ r in 𝓝 s, AEStronglyMeasurable
      (fun y => heatKernel d (t - r) (x - y) * v (r, y)) volume := by
    filter_upwards [hU] with r hr
    exact ((hcont r (hUt hr)).continuous.mul (hslice r).continuous).aestronglyMeasurable
  have hint : Integrable (fun y => heatKernel d (t - s) (x - y) * v (s, y)) :=
    ((hcont s hst).continuous.mul (hslice s).continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_space_slice hvc s).mul_left
  have hdmeas : AEStronglyMeasurable (fun y =>
      (-contOp d (fun z => heatKernel d (t - s) (x - z)) y) * v (s, y) +
        heatKernel d (t - s) (x - y) * deriv (fun r => v (r, y)) s) volume :=
    ((((contDiff_contOp (hcont s hst)).continuous.neg.mul (hslice s).continuous).add
      ((hcont s hst).continuous.mul htime))).aestronglyMeasurable
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ) (μ := volume)
    (F := fun r y => heatKernel d (t - r) (x - y) * v (r, y))
    (F' := fun r y => (-contOp d (fun z => heatKernel d (t - r) (x - z)) y) * v (r, y) +
      heatKernel d (t - r) (x - y) * deriv (fun q => v (q, y)) r)
    (x₀ := s) (s := U) (bound := bound) hU hmeas hint hdmeas hb hbi
    (ae_of_all _ fun y r hr => hasDerivAt_heatKernel_mul hd hv (hUt hr) x y)
  rw [integral_heatKernel_mul_time_deriv_eq hd hv hvc hst x] at h
  exact h.2


/-- The reflected kernel is smooth jointly in time and space before the terminal time. -/
theorem contDiffOn_heatKernel_reflected {d : ℕ} (hd : 1 ≤ d) (t : ℝ) (x : Fin d → ℝ) :
    ContDiffOn ℝ ∞ (fun q : ℝ × (Fin d → ℝ) => heatKernel d (t - q.1) (x - q.2))
      {q | q.1 < t} := by
  have hm : ContDiff ℝ ∞ (fun q : ℝ × (Fin d → ℝ) => (t - q.1, x - q.2)) :=
    (contDiff_const.sub contDiff_fst).prodMk (contDiff_const.sub contDiff_snd)
  apply (contDiffOn_heatKernel hd).comp hm.contDiffOn
  intro q hq
  change 0 < t - q.1
  exact sub_pos.mpr hq

/-- The time derivative of the reflected kernel is its backward heat operator. -/
theorem fderiv_heatKernel_reflected_time {d : ℕ} (hd : 1 ≤ d)
    {s t : ℝ} (hst : s < t) (x y : Fin d → ℝ) :
    fderiv ℝ (fun q : ℝ × (Fin d → ℝ) => heatKernel d (t - q.1) (x - q.2))
      (s, y) (timeDir d) = -contOp d (fun z => heatKernel d (t - s) (x - z)) y := by
  have hU : IsOpen {q : ℝ × (Fin d → ℝ) | q.1 < t} :=
    isOpen_lt continuous_fst continuous_const
  have hdiff : DifferentiableAt ℝ
      (fun q : ℝ × (Fin d → ℝ) => heatKernel d (t - q.1) (x - q.2)) (s, y) :=
    ((contDiffOn_heatKernel_reflected hd t x).differentiableOn (by simp)).differentiableAt
    (hU.mem_nhds (show (s, y) ∈ {q : ℝ × (Fin d → ℝ) | q.1 < t} from hst))
  have ht : HasDerivAt (fun r => heatKernel d (t - r) (x - y))
      (fderiv ℝ (fun q : ℝ × (Fin d → ℝ) => heatKernel d (t - q.1) (x - q.2))
        (s, y) (timeDir d)) s := by
    have htmp := hdiff.hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s y))
    simpa only [Function.comp_def, id_eq, timeDir] using htmp
  exact ht.unique (hasDerivAt_heatKernel_backward hd hst x y)


/-- The spatial heat-kernel integral differentiates to the integral of the heat source before
the terminal time. -/
theorem hasDerivAt_integral_heatKernel_mul {d : ℕ} (hd : 1 ≤ d)
    {v : ℝ × (Fin d → ℝ) → ℝ} (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v)
    {s t : ℝ} (hst : s < t) (x : Fin d → ℝ) :
    HasDerivAt (fun r => ∫ y, heatKernel d (t - r) (x - y) * v (r, y))
      (∫ y, heatKernel d (t - s) (x - y) * heatSource d v (s, y)) s := by
  let δ : ℝ := (t - s) / 2
  have hδ : 0 < δ := half_pos (sub_pos.mpr hst)
  have hδt : s + δ < t := by dsimp [δ]; linarith
  obtain ⟨K, hK, hsupport⟩ := exists_compact_space_support hv hvc
  let W : Set (ℝ × (Fin d → ℝ)) := {q | q.1 < t}
  let G : ℝ × (Fin d → ℝ) → ℝ := fun q => heatKernel d (t - q.1) (x - q.2)
  let D : ℝ × (Fin d → ℝ) → ℝ := fun q =>
    fderiv ℝ G q (timeDir d) * v q + G q * fderiv ℝ v q (timeDir d)
  have hW : IsOpen W := isOpen_lt continuous_fst continuous_const
  have hG : ContDiffOn ℝ ∞ G W := contDiffOn_heatKernel_reflected hd t x
  have hD : ContinuousOn D W := by
    have hG' : ContDiffOn ℝ ∞ (fun q => fderiv ℝ G q (timeDir d)) W :=
      (hG.fderiv_of_isOpen hW (by simp)).clm_apply contDiffOn_const
    exact ((hG'.mul hv.contDiffOn).add
      (hG.mul (contDiff_fderiv_apply hv _).contDiffOn)).continuousOn
  have hC : IsCompact (Icc (s - δ) (s + δ) ×ˢ K) := isCompact_Icc.prod hK
  have hCW : Icc (s - δ) (s + δ) ×ˢ K ⊆ W := by
    intro q hq
    exact lt_of_le_of_lt hq.1.2 hδt
  obtain ⟨M, hM, hbound⟩ := (hC.image_of_continuousOn (hD.mono hCW)).isBounded.exists_pos_norm_le
  have hbi : Integrable (K.indicator (fun _ => M)) :=
    (integrable_indicator_iff hK.isClosed.measurableSet).mpr (integrableOn_const hK.measure_lt_top.ne)
  have hU : Ioo (s - δ) (s + δ) ∈ 𝓝 s := Ioo_mem_nhds (by linarith) (by linarith)
  have hUt : Ioo (s - δ) (s + δ) ⊆ Iio t := fun r hr => lt_trans hr.2 hδt
  apply hasDerivAt_integral_heatKernel_mul_of_dominated hd hv hvc hst x hU hUt hbi
  filter_upwards with y
  intro r hr
  by_cases hy : y ∈ K
  · rw [indicator_of_mem hy]
    have hrt : r < t := hUt hr
    have hrewrite : (-contOp d (fun z => heatKernel d (t - r) (x - z)) y) * v (r, y) +
        heatKernel d (t - r) (x - y) * deriv (fun q => v (q, y)) r = D (r, y) := by
      dsimp [D, G]
      rw [fderiv_heatKernel_reflected_time hd hrt x y,
        (hasDerivAt_slice_time (hv.differentiable (by simp)) r y).deriv]
    rw [hrewrite]
    exact hbound (D (r, y)) ⟨(r, y), ⟨⟨hr.1.le, hr.2.le⟩, hy⟩, rfl⟩
  · obtain ⟨hv0, hvt0⟩ := hsupport r y hy
    simp [indicator_of_notMem hy, hv0, hvt0]


/-- The spatial integral of a heat source varies continuously before the terminal time. -/
theorem continuousOn_integral_heatKernel_mul_source {d : ℕ} (hd : 1 ≤ d)
    {v : ℝ × (Fin d → ℝ) → ℝ} (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v)
    (t : ℝ) (x : Fin d → ℝ) :
    ContinuousOn (fun r => ∫ y, heatKernel d (t - r) (x - y) * heatSource d v (r, y))
      (Iio t) := by
  let K : Set (Fin d → ℝ) := Prod.snd '' tsupport (heatSource d v)
  have hK : IsCompact K := (hasCompactSupport_heatSource hv hvc).image continuous_snd
  have hf : ContinuousOn (fun q : ℝ × (Fin d → ℝ) =>
      heatKernel d (t - q.1) (x - q.2) * heatSource d v q) (Iio t ×ˢ univ) := by
    have hh := (contDiffOn_heatKernel_reflected hd t x).continuousOn.mul
      (contDiff_heatSource hv).continuous.continuousOn
    exact hh.mono (fun q hq => hq.1)
  apply continuousOn_integral_of_compact_support (μ := volume) hK hf
  intro r y _ hy
  have hy' : (r, y) ∉ tsupport (heatSource d v) := fun h => hy ⟨(r, y), h, rfl⟩
  simp only [image_eq_zero_of_notMem_tsupport hy', mul_zero]

/-- The heat-kernel identity on a compact time interval before the terminal time. -/
theorem integral_heatKernel_source_interval {d : ℕ} (hd : 1 ≤ d)
    {v : ℝ × (Fin d → ℝ) → ℝ} (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v)
    {a b t : ℝ} (hab : a ≤ b) (hbt : b < t) (x : Fin d → ℝ) :
    (∫ r in a..b, ∫ y, heatKernel d (t - r) (x - y) * heatSource d v (r, y)) =
      (∫ y, heatKernel d (t - b) (x - y) * v (b, y)) -
        ∫ y, heatKernel d (t - a) (x - y) * v (a, y) := by
  have hsub : Icc a b ⊆ Iio t := fun r hr => lt_of_le_of_lt hr.2 hbt
  have hg := (continuousOn_integral_heatKernel_mul_source hd hv hvc t x).mono hsub
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
  · exact fun r hr => (hasDerivAt_integral_heatKernel_mul hd hv hvc (hsub hr) x).continuousAt.continuousWithinAt
  · exact fun r hr => hasDerivAt_integral_heatKernel_mul hd hv hvc (hsub (mem_Icc_of_Ioo hr)) x
  · exact hg.intervalIntegrable_of_Icc hab


/-- The reflected heat kernel is jointly measurable, including at the terminal time. -/
theorem measurable_heatKernel_reflected {d : ℕ} (hd : 1 ≤ d) (t : ℝ) (x : Fin d → ℝ) :
    Measurable (fun q : ℝ × (Fin d → ℝ) => heatKernel d (t - q.1) (x - q.2)) := by
  let G : ℝ × (Fin d → ℝ) → ℝ := fun q => heatKernel d (t - q.1) (x - q.2)
  let W : Set (ℝ × (Fin d → ℝ)) := {q | q.1 < t}
  have hW : IsOpen W := isOpen_lt continuous_fst continuous_const
  have hm : Measurable (W.piecewise G (fun _ => 0)) :=
    (contDiffOn_heatKernel_reflected hd t x).continuousOn.measurable_piecewise
      continuous_const.continuousOn hW.measurableSet
  have heq : W.piecewise G (fun _ => 0) = G := by
    funext q
    by_cases hq : q ∈ W
    · simp [hq]
    · have hq' : t - q.1 ≤ 0 := sub_nonpos.mpr (le_of_not_gt hq)
      simp [hq, G, heatKernel_of_nonpos hq']
  rwa [heq] at hm

/-- Every spatial section of the heat-kernel source integrand is integrable. -/
theorem integrable_heatKernel_mul_source_slice {d : ℕ} (hd : 1 ≤ d)
    {v : ℝ × (Fin d → ℝ) → ℝ} (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v)
    (t r : ℝ) (x : Fin d → ℝ) :
    Integrable (fun y => heatKernel d (t - r) (x - y) * heatSource d v (r, y)) := by
  by_cases hrt : r < t
  · have hk : ContDiff ℝ ∞ (fun y => heatKernel d (t - r) (x - y)) :=
      (contDiff_heatKernel_space hd (sub_pos.mpr hrt)).comp (contDiff_const.sub contDiff_id)
    have hv' : ContDiff ℝ ∞ (fun y => heatSource d v (r, y)) :=
      (contDiff_heatSource hv).comp (contDiff_const.prodMk contDiff_id)
    exact (hk.continuous.mul hv'.continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_space_slice (hasCompactSupport_heatSource hv hvc) r).mul_left
  · have ht : t - r ≤ 0 := sub_nonpos.mpr (le_of_not_gt hrt)
    simp only [heatKernel_of_nonpos ht, zero_mul]
    exact integrable_zero _ _ _


/-- The space-time heat-kernel source integrand is integrable. -/
theorem integrable_heatKernel_mul_source {d : ℕ} (hd : 1 ≤ d)
    {v : ℝ × (Fin d → ℝ) → ℝ} (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v)
    (t : ℝ) (x : Fin d → ℝ) :
    Integrable (fun q : ℝ × (Fin d → ℝ) =>
      heatKernel d (t - q.1) (x - q.2) * heatSource d v q) := by
  let F : ℝ × (Fin d → ℝ) → ℝ := fun q =>
    heatKernel d (t - q.1) (x - q.2) * heatSource d v q
  have hF : AEStronglyMeasurable F (volume.prod volume) :=
    ((measurable_heatKernel_reflected hd t x).mul (contDiff_heatSource hv).continuous.measurable).aestronglyMeasurable
  obtain ⟨M, hM⟩ := (hasCompactSupport_heatSource hv hvc).exists_bound_of_continuous
    (contDiff_heatSource hv).continuous
  have hM0 : 0 ≤ M := (norm_nonneg (heatSource d v (0, 0))).trans (hM (0, 0))
  obtain ⟨R, hR, htime⟩ := exists_heatSource_time_bound hv hvc
  have hmajor : Integrable ((Icc (-R) R).indicator (fun _ => M)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const measure_Icc_lt_top.ne)
  have hsec (r : ℝ) : Integrable (fun y => F (r, y)) :=
    integrable_heatKernel_mul_source_slice hd hv hvc t r x
  have hnorm (r : ℝ) : ∫ y, ‖F (r, y)‖ ≤ M := by
    by_cases hrt : r < t
    · have hp : 0 < t - r := sub_pos.mpr hrt
      have hk : Integrable (fun y => M * heatKernel d (t - r) (x - y)) :=
        ((integrable_heatKernel hd hp).comp_sub_left x).const_mul M
      calc
        (∫ y, ‖F (r, y)‖) ≤ ∫ y, M * heatKernel d (t - r) (x - y) := by
          apply integral_mono (hsec r).norm hk
          intro y
          dsimp [F]
          rw [abs_mul, abs_of_nonneg (heatKernel_nonneg hd _ _), ← Real.norm_eq_abs]
          calc
            heatKernel d (t - r) (x - y) * ‖heatSource d v (r, y)‖ ≤
                heatKernel d (t - r) (x - y) * M :=
              mul_le_mul_of_nonneg_left (hM (r, y)) (heatKernel_nonneg hd _ _)
            _ = M * heatKernel d (t - r) (x - y) := mul_comm _ _
        _ = M := by rw [integral_const_mul, integral_sub_left_eq_self, integral_heatKernel hd hp, mul_one]
    · have ht : t - r ≤ 0 := sub_nonpos.mpr (le_of_not_gt hrt)
      have hzero : (fun y => ‖F (r, y)‖) = fun _ => 0 := by
        funext y
        simp [F, heatKernel_of_nonpos ht]
      rw [hzero, integral_zero]
      exact hM0
  have htime0 (r : ℝ) (hr : r ∉ Icc (-R) R) (y : Fin d → ℝ) : heatSource d v (r, y) = 0 := by
    have hr' : R < |r| := by
      apply lt_of_not_ge
      intro hh
      have hh' := abs_le.mp hh
      exact hr ⟨hh'.1, hh'.2⟩
    exact (htime (r, y) hr').2
  have houter : Integrable (fun r => ∫ y, ‖F (r, y)‖) := by
    apply Integrable.mono' hmajor hF.norm.integral_prod_right'
    filter_upwards with r
    by_cases hr : r ∈ Icc (-R) R
    · rw [indicator_of_mem hr, Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
      exact hnorm r
    · rw [indicator_of_notMem hr]
      have heq : (fun y => |F (r, y)|) = fun _ => 0 := by
        funext y
        simp [F, htime0 r hr y]
      simp [heq]
  exact (integrable_prod_iff hF).mpr ⟨Filter.Eventually.of_forall hsec, houter⟩


/-- A smooth compactly supported function is the heat convolution of its heat source. -/
theorem heatDuhamel {d : ℕ} (hd : 1 ≤ d)
    {v : ℝ × (Fin d → ℝ) → ℝ} (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v)
    (t : ℝ) (x : Fin d → ℝ) :
    v (t, x) = ∫ q : ℝ × (Fin d → ℝ), heatKernel d (t - q.1) (x - q.2) *
      (deriv (fun s => v (s, q.2)) q.1 - contOp d (fun y => v (q.1, y)) q.2) := by
  let F : ℝ × (Fin d → ℝ) → ℝ := fun q =>
    heatKernel d (t - q.1) (x - q.2) * heatSource d v q
  let G : ℝ → ℝ := fun r => ∫ y, F (r, y)
  have hF : Integrable F := integrable_heatKernel_mul_source hd hv hvc t x
  have hG : Integrable G := hF.integral_prod_left
  obtain ⟨R, hR, htime⟩ := exists_heatSource_time_bound hv hvc
  let a : ℝ := min (t - 1) (-R - 1)
  have hat : a < t := by dsimp [a]; linarith [min_le_left (t - 1) (-R - 1)]
  have haR : a < -R := by dsimp [a]; linarith [min_le_right (t - 1) (-R - 1)]
  have hsmall (r : ℝ) (hr : r ≤ a) : R < |r| := by
    have := neg_le_abs r
    linarith
  have hVa : (∫ y, heatKernel d (t - a) (x - y) * v (a, y)) = 0 := by
    have hzero : ∀ y, v (a, y) = 0 := fun y => (htime (a, y) (hsmall a le_rfl)).1
    simp [hzero]
  have hsupp : Function.support G ⊆ Ioc a t := by
    intro r hr
    by_contra hn
    have hz : G r = 0 := by
      by_cases har : a < r
      · have htr : t < r := lt_of_not_ge (fun hrt => hn ⟨har, hrt⟩)
        have ht : t - r ≤ 0 := sub_nonpos.mpr htr.le
        simp [G, F, heatKernel_of_nonpos ht]
      · have hr' : r ≤ a := le_of_not_gt har
        have hzero : ∀ y, heatSource d v (r, y) = 0 := fun y =>
          (htime (r, y) (hsmall r hr')).2
        simp [G, F, hzero]
    exact hr hz
  have hprimitive : Continuous (fun b => ∫ r in a..b, G r) :=
    intervalIntegral.continuous_primitive (fun b c => hG.intervalIntegrable) a
  have htend : Tendsto (fun ε : ℝ => t - ε) (𝓝[>] 0) (𝓝 t) := by
    have hzero : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using tendsto_const_nhds.sub hzero
  have hlim : Tendsto (fun ε : ℝ => ∫ r in a..(t - ε), G r)
      (𝓝[>] 0) (𝓝 (∫ r in a..t, G r)) := (hprimitive.tendsto t).comp htend
  obtain ⟨M, hM⟩ := hvc.exists_bound_of_continuous hv.continuous
  have hvbound : ∃ M, ∀ q, |v q| ≤ M := ⟨M, fun q => by simpa [Real.norm_eq_abs] using hM q⟩
  have hboundary := tendsto_integral_heatKernel_reflect_time hd hv.continuous hvbound t x
  have hevent : (fun ε : ℝ => ∫ r in a..(t - ε), G r) =ᶠ[𝓝[>] 0]
      fun ε => ∫ y, heatKernel d ε (x - y) * v (t - ε, y) := by
    have heps : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < t - a :=
      (eventually_lt_nhds (sub_pos.mpr hat)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, heps] with ε hε hεa
    change 0 < ε at hε
    have ha : a ≤ t - ε := by linarith
    have hb : t - ε < t := by linarith
    have h := integral_heatKernel_source_interval hd hv hvc ha hb x
    simpa [G, F, hVa] using h
  have hlim' : Tendsto (fun ε : ℝ => ∫ r in a..(t - ε), G r) (𝓝[>] 0) (𝓝 (v (t, x))) :=
    hboundary.congr' hevent.symm
  have heq := tendsto_nhds_unique hlim hlim'
  have hfull : (∫ r in a..t, G r) = ∫ q, F q := by
    rw [intervalIntegral.integral_eq_integral_of_support_subset hsupp]
    exact (integral_prod F hF).symm
  rw [hfull] at heq
  simpa [F, heatSource] using heq.symm

end LatticeProb.Heat
