import LatticeProb.Prob.BrownianOpenHarmonicExit
import LatticeProb.Prob.BrownianExitTime

/-!
# Exit averages of the fundamental solutions over a ball

Let `B` be the Brownian motion of `LatticeProb.IsBrownianSpace` started at the centre `x` of a ball
of radius `s`, and let `τ = exitTime B x s` be its exit time. For `‖y - x‖ < s`:

* `LatticeProb.IsBrownianSpace.integral_log_norm_exit_ball`: in dimension two,
  `E log ‖B_τ - y‖ = log s`;
* `LatticeProb.IsBrownianSpace.integral_inv_norm_exit_ball`: in dimension three,
  `E ‖B_τ - y‖⁻¹ = s⁻¹`.

The functions `log ‖· - y‖` and `‖· - y‖⁻¹` are harmonic away from `y` but singular at `y`, inside
the ball. On the sphere `‖z - x‖ = s` they agree with harmonic functions that are regular on a
neighbourhood of the closed ball, by the Kelvin image `y* = x + (s / ‖y - x‖)² (y - x)` of `y`:
`‖y - x‖ ‖z - y*‖ = s ‖z - y‖` (`LatticeProb.norm_mul_norm_sub_kelvin`). The exit position lies on
the sphere almost surely, so the expectation is the value at `x` of the regular function
(`LatticeProb.integral_openExit_harmonicNearClosure`). For `y = x` both functions are constant
on the sphere.

The harmonicity of `log ‖· - c‖` on `ℝ²` and of `‖· - c‖⁻¹` on `ℝ³` away from `c` follows from
the formula `Δ φ (‖z - c‖²) = 4 ‖z - c‖² φ'' + 2 d φ'` of `LatticeProb.laplacian_comp_norm_sub_sq`.
The closed-ball exit time `exitTime B x s` is the exit time `openExitTime` of the open ball
(`LatticeProb.exitTime_eq_openExitTime_ball`).
-/

open MeasureTheory Filter Topology Set Metric InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Laplacian

noncomputable section

namespace LatticeProb

section Laplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The Laplacian of a function of the squared distance to a point `c`:
`Δ φ (‖z - c‖²) = 4 ‖z - c‖² φ'' (‖z - c‖²) + 2 d φ' (‖z - c‖²)`, where `d` is the dimension. -/
theorem laplacian_comp_norm_sub_sq {φ φ' : ℝ → ℝ} {φ'' : ℝ} {c x : E}
    (hF : ContDiffAt ℝ 2 (fun z => φ (‖z - c‖ ^ 2)) x)
    (h1 : ∀ᶠ u in 𝓝 (‖x - c‖ ^ 2), HasDerivAt φ (φ' u) u)
    (h2 : HasDerivAt φ' φ'' (‖x - c‖ ^ 2)) :
    Δ (fun z => φ (‖z - c‖ ^ 2)) x =
      4 * ‖x - c‖ ^ 2 * φ'' + 2 * Module.finrank ℝ E * φ' (‖x - c‖ ^ 2) := by
  set F : E → ℝ := fun z => φ (‖z - c‖ ^ 2) with hFdef
  have hq : ∀ z : E, HasFDerivAt (fun z : E => ‖z - c‖ ^ 2)
      (2 • (innerSL ℝ (z - c)).comp (ContinuousLinearMap.id ℝ E)) z :=
    fun z => ((hasFDerivAt_id z).sub_const c).norm_sq
  have hderiv : ∀ᶠ z in 𝓝 x, ∀ v, fderiv ℝ F z v = 2 * φ' (‖z - c‖ ^ 2) * ⟪z - c, v⟫ := by
    filter_upwards [((by fun_prop : Continuous fun z : E => ‖z - c‖ ^ 2).tendsto x).eventually h1]
      with z hz v
    have h3 : HasFDerivAt F (φ' (‖z - c‖ ^ 2) •
        (2 • (innerSL ℝ (z - c)).comp (ContinuousLinearMap.id ℝ E))) z :=
      hz.comp_hasFDerivAt z (hq z)
    rw [h3.fderiv]
    simp only [smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  have hdiff : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have key : ∀ v, fderiv ℝ (fderiv ℝ F) x v v =
      2 * φ' (‖x - c‖ ^ 2) * ⟪v, v⟫ + 4 * φ'' * ⟪x - c, v⟫ ^ 2 := by
    intro v
    have hg := (h2.comp_hasFDerivAt x (hq x)).const_mul 2
    have hh := ((hasFDerivAt_id x).sub_const c).inner ℝ (hasFDerivAt_const v x)
    have hψ := hg.mul hh
    have h4 : HasFDerivAt (fun z => fderiv ℝ F z v) _ x :=
      hψ.congr_of_eventuallyEq (hderiv.mono fun z hz => hz v)
    have h5 := (hdiff.hasFDerivAt.clm_apply (hasFDerivAt_const v x)).unique h4
    have h6 := congrArg (fun L : E →L[ℝ] ℝ => L v) h5
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      zero_apply, map_zero, ContinuousLinearMap.flip_apply, zero_add] at h6
    rw [h6]
    simp only [id_eq, smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, innerSL_apply_apply,
      smul_eq_mul, nsmul_eq_mul, fderivInnerCLM_apply, ContinuousLinearMap.prod_apply,
      zero_apply, inner_zero_right, Function.comp_apply]
    push_cast
    rw [real_inner_comm v (x - c)]
    ring
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one, key]
  set b := stdOrthonormalBasis ℝ E
  have hb1 : ∀ i, ⟪b i, b i⟫ = 1 := fun i => by
    rw [real_inner_self_eq_norm_sq, b.orthonormal.1 i, one_pow]
  have hsum : ∑ i, ⟪x - c, b i⟫ ^ 2 = ‖x - c‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner (x - c) (x - c)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_comm (b i) (x - c), sq]
  simp only [hb1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Finset.mul_sum, hsum, nsmul_eq_mul]
  ring

end Laplacian

/-- On the plane, `log ‖· - c‖` is harmonic away from `c`. -/
theorem harmonicOnNhd_log_norm_sub (c : EuclideanSpace ℝ (Fin 2)) :
    HarmonicOnNhd (fun z => Real.log ‖z - c‖) {c}ᶜ := by
  have hF : (fun z : EuclideanSpace ℝ (Fin 2) => Real.log ‖z - c‖) =
      fun z => Real.log (‖z - c‖ ^ 2) / 2 := by
    funext z
    rw [Real.log_pow]
    push_cast
    ring
  have hcd : ∀ z ∈ ({c}ᶜ : Set (EuclideanSpace ℝ (Fin 2))),
      ContDiffAt ℝ 2 (fun z => Real.log ‖z - c‖) z := fun z hz =>
    ((contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.2 hz)).log
      (norm_ne_zero_iff.2 (sub_ne_zero.2 hz))
  intro x hx
  refine ⟨hcd x hx, ?_⟩
  filter_upwards [isOpen_compl_singleton.mem_nhds hx] with z hz
  have hu : 0 < ‖z - c‖ ^ 2 := by
    have := norm_pos_iff.2 (sub_ne_zero.2 (show z ≠ c from hz))
    positivity
  rw [hF] at hcd ⊢
  rw [laplacian_comp_norm_sub_sq (φ' := fun u => u⁻¹ / 2) (hcd z hz)
    ((eventually_ne_nhds hu.ne').mono fun u hu => (Real.hasDerivAt_log hu).div_const 2)
    ((hasDerivAt_inv hu.ne').div_const 2), finrank_euclideanSpace_fin, Pi.zero_apply]
  field_simp
  ring

/-- On `ℝ³`, `‖· - c‖⁻¹` is harmonic away from `c`. -/
theorem harmonicOnNhd_inv_norm_sub (c : EuclideanSpace ℝ (Fin 3)) :
    HarmonicOnNhd (fun z => ‖z - c‖⁻¹) {c}ᶜ := by
  have hF : (fun z : EuclideanSpace ℝ (Fin 3) => ‖z - c‖⁻¹) =
      fun z => (‖z - c‖ ^ 2) ^ (-(1 / 2 : ℝ)) := by
    funext z
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    norm_num
    exact (Real.rpow_neg_one _).symm
  have hcd : ∀ z ∈ ({c}ᶜ : Set (EuclideanSpace ℝ (Fin 3))),
      ContDiffAt ℝ 2 (fun z => ‖z - c‖⁻¹) z := fun z hz =>
    ((contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.2 hz)).inv
      (norm_ne_zero_iff.2 (sub_ne_zero.2 hz))
  intro x hx
  refine ⟨hcd x hx, ?_⟩
  filter_upwards [isOpen_compl_singleton.mem_nhds hx] with z hz
  have hu : 0 < ‖z - c‖ ^ 2 := by
    have := norm_pos_iff.2 (sub_ne_zero.2 (show z ≠ c from hz))
    positivity
  rw [hF] at hcd ⊢
  rw [laplacian_comp_norm_sub_sq (φ' := fun u => -(1 / 2 : ℝ) * u ^ (-(1 / 2 : ℝ) - 1)) (hcd z hz)
    ((eventually_ne_nhds hu.ne').mono fun u hu => Real.hasDerivAt_rpow_const (Or.inl hu))
    ((Real.hasDerivAt_rpow_const (Or.inl hu.ne')).const_mul _), finrank_euclideanSpace_fin,
    Pi.zero_apply]
  have he : (‖z - c‖ ^ 2) ^ (-(1 / 2 : ℝ) - 1 - 1) * ‖z - c‖ ^ 2 =
      (‖z - c‖ ^ 2) ^ (-(1 / 2 : ℝ) - 1) := by
    rw [← Real.rpow_add_one hu.ne']
    norm_num
  linear_combination 3 * he

/-- The Kelvin image `x + (s / ‖y - x‖)² (y - x)` of `y ≠ x` in the sphere of radius `s` about `x`:
for `z` on that sphere, `‖y - x‖ ‖z - y*‖ = s ‖z - y‖`. -/
theorem norm_mul_norm_sub_kelvin {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x y z : E} {s : ℝ} (hs : 0 ≤ s) (hz : ‖z - x‖ = s) (hy : y ≠ x) :
    ‖y - x‖ * ‖z - (x + (s ^ 2 / ‖y - x‖ ^ 2) • (y - x))‖ = s * ‖z - y‖ := by
  have hρ : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hy)
  rw [show z - (x + (s ^ 2 / ‖y - x‖ ^ 2) • (y - x)) = (z - x) - (s ^ 2 / ‖y - x‖ ^ 2) • (y - x)
      by abel, show z - y = (z - x) - (y - x) by abel]
  generalize z - x = w at hz ⊢
  generalize y - x = v at hρ ⊢
  refine (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).1 ?_
  rw [mul_pow, mul_pow, norm_sub_sq_real (x := w) (y := (s ^ 2 / ‖v‖ ^ 2) • v),
    norm_sub_sq_real (x := w) (y := v), norm_smul, inner_smul_right, hz, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (sq_nonneg s) (sq_nonneg ‖v‖))]
  field_simp
  ring

/-- The exit time from the closed ball, `exitTime B u A`, is the exit time `openExitTime` from the
open ball of radius `A` about `u`: both are the first time at which `A ≤ ‖B t ω - u‖`. -/
theorem exitTime_eq_openExitTime_ball {Ω : Type*} {d : ℕ}
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (u : EuclideanSpace ℝ (Fin d)) (A : ℝ) (ω : Ω) :
    exitTime B u A ω = openExitTime B (ball u A) ω := by
  have hmem : ∀ t : ℝ≥0, B t ω ∉ ball u A ↔ A ≤ ‖B t ω - u‖ := fun t => by
    rw [mem_ball, dist_eq_norm, not_lt]
  unfold exitTime openExitTime
  split_ifs with h
  · rw [ENNReal.coe_sInf (show Set.Nonempty {s : ℝ≥0 | A ≤ ‖B s ω - u‖} from h)]
    refine le_antisymm (le_iInf fun t => iInf₂_le t.1 ((hmem t.1).1 t.2))
      (le_iInf₂ fun t ht => iInf_le_of_le ⟨t, (hmem t).2 ht⟩ le_rfl)
  · exact (iInf_eq_top.2 fun t => absurd ⟨t.1, (hmem t.1).1 t.2⟩ h).symm

/-- The exit position of a Brownian motion from a ball about its starting point lies on the
sphere almost surely. -/
theorem IsBrownianSpace.ae_mem_sphere_openExitTime_ball {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (hd : 1 ≤ d) {P : Measure Ω} {x : EuclideanSpace ℝ (Fin d)}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} (hB : IsBrownianSpace d x B P) {s : ℝ}
    (hs : 0 < s) :
    ∀ᵐ ω ∂P, B (openExitTime B (ball x s) ω).toNNReal ω ∈ sphere x s := by
  filter_upwards [hB.start, ae_openExitTime_ne_top hd hB isBounded_ball, hB.cont]
    with ω hstart hfin hcont
  have h := openExitTime_mem_frontier isOpen_ball hcont (by rw [hstart]; exact mem_ball_self hs)
    hfin
  rwa [frontier_ball x hs.ne'] at h

/-- The Kelvin image lies outside the closed ball. -/
private lemma closure_ball_subset_compl_kelvin {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {x y : E} {s : ℝ} (hs : 0 < s) (hy : y ≠ x) (hys : ‖y - x‖ < s) :
    closure (ball x s) ⊆ {x + (s ^ 2 / ‖y - x‖ ^ 2) • (y - x)}ᶜ ∧
      ‖x - (x + (s ^ 2 / ‖y - x‖ ^ 2) • (y - x))‖ = s ^ 2 / ‖y - x‖ := by
  have hρ : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hy)
  have hnorm : ‖x - (x + (s ^ 2 / ‖y - x‖ ^ 2) • (y - x))‖ = s ^ 2 / ‖y - x‖ := by
    rw [sub_add_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    field_simp
  refine ⟨fun z hz hzk => ?_, hnorm⟩
  rw [closure_ball x hs.ne', mem_closedBall, dist_eq_norm] at hz
  rw [mem_singleton_iff.1 hzk, ← norm_neg, neg_sub, hnorm, div_le_iff₀ hρ, sq] at hz
  nlinarith

/-- In dimension two, the expectation of `log ‖B_τ - y‖` at the exit time `τ` of the ball of
radius `s` about the starting point `x` is `log s`, for every `y` in the ball. -/
theorem IsBrownianSpace.integral_log_norm_exit_ball {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (x : EuclideanSpace ℝ (Fin 2)) (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 2))
    (hB : IsBrownianSpace 2 x B P) {s : ℝ} (hs : 0 < s) {y : EuclideanSpace ℝ (Fin 2)}
    (hy : ‖y - x‖ < s) :
    ∫ ω, Real.log ‖B (exitTime B x s ω).toNNReal ω - y‖ ∂P = Real.log s := by
  have := hB.isProbabilityMeasure
  simp_rw [exitTime_eq_openExitTime_ball]
  have hsph := hB.ae_mem_sphere_openExitTime_ball (by norm_num) hs
  rcases eq_or_ne y x with rfl | hyx
  · have hae : (fun ω => Real.log ‖B (openExitTime B (ball y s) ω).toNNReal ω - y‖) =ᵐ[P]
        fun _ => Real.log s := hsph.mono fun ω hω => by dsimp only; rw [mem_sphere_iff_norm.1 hω]
    rw [integral_congr_ae hae]
    simp
  have hρ : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hyx)
  obtain ⟨hsub, hnorm⟩ := closure_ball_subset_compl_kelvin hs hyx hy
  set k := x + (s ^ 2 / ‖y - x‖ ^ 2) • (y - x) with hk
  have hh : HarmonicNearClosure (fun z => Real.log ‖z - k‖ + Real.log (‖y - x‖ / s)) (ball x s) :=
    harmonicNearClosure_iff.2 (((harmonicOnNhd_log_norm_sub k).mono hsub).add
      (harmonicOnNhd_const _))
  have key := integral_openExit_harmonicNearClosure (by norm_num) hB isOpen_ball isBounded_ball hh
  have hae : (fun ω => Real.log ‖B (openExitTime B (ball x s) ω).toNNReal ω - y‖) =ᵐ[P]
      fun ω => Real.log ‖B (openExitTime B (ball x s) ω).toNNReal ω - k‖ +
        Real.log (‖y - x‖ / s) := hsph.mono fun ω hω => by
    dsimp only
    set z := B (openExitTime B (ball x s) ω).toNNReal ω
    have hz : ‖z - x‖ = s := mem_sphere_iff_norm.1 hω
    have hkm := norm_mul_norm_sub_kelvin hs.le hz hyx
    have hzk : z - k ≠ 0 := sub_ne_zero.2 fun h => hsub
      (by rw [closure_ball x hs.ne']; exact sphere_subset_closedBall hω) (mem_singleton_iff.2 h)
    rw [show ‖z - y‖ = ‖y - x‖ / s * ‖z - k‖ by field_simp; linarith,
      Real.log_mul (div_pos hρ hs).ne' (norm_ne_zero_iff.2 hzk), add_comm]
  rw [integral_congr_ae hae, key, hnorm, ← Real.log_mul (by positivity) (by positivity)]
  congr 1
  field_simp

/-- In dimension three, the expectation of `‖B_τ - y‖⁻¹` at the exit time `τ` of the ball of
radius `s` about the starting point `x` is `s⁻¹`, for every `y` in the ball. -/
theorem IsBrownianSpace.integral_inv_norm_exit_ball {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (x : EuclideanSpace ℝ (Fin 3)) (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 3))
    (hB : IsBrownianSpace 3 x B P) {s : ℝ} (hs : 0 < s) {y : EuclideanSpace ℝ (Fin 3)}
    (hy : ‖y - x‖ < s) :
    ∫ ω, ‖B (exitTime B x s ω).toNNReal ω - y‖⁻¹ ∂P = s⁻¹ := by
  have := hB.isProbabilityMeasure
  simp_rw [exitTime_eq_openExitTime_ball]
  have hsph := hB.ae_mem_sphere_openExitTime_ball (by norm_num) hs
  rcases eq_or_ne y x with rfl | hyx
  · have hae : (fun ω => ‖B (openExitTime B (ball y s) ω).toNNReal ω - y‖⁻¹) =ᵐ[P]
        fun _ => s⁻¹ := hsph.mono fun ω hω => by dsimp only; rw [mem_sphere_iff_norm.1 hω]
    rw [integral_congr_ae hae]
    simp
  have hρ : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hyx)
  obtain ⟨hsub, hnorm⟩ := closure_ball_subset_compl_kelvin hs hyx hy
  set k := x + (s ^ 2 / ‖y - x‖ ^ 2) • (y - x) with hk
  have hh : HarmonicNearClosure ((s / ‖y - x‖) • fun z => ‖z - k‖⁻¹) (ball x s) :=
    harmonicNearClosure_iff.2 (((harmonicOnNhd_inv_norm_sub k).mono hsub).const_smul)
  have key := integral_openExit_harmonicNearClosure (by norm_num) hB isOpen_ball isBounded_ball hh
  simp only [Pi.smul_apply, smul_eq_mul] at key
  have hae : (fun ω => ‖B (openExitTime B (ball x s) ω).toNNReal ω - y‖⁻¹) =ᵐ[P]
      fun ω => s / ‖y - x‖ * ‖B (openExitTime B (ball x s) ω).toNNReal ω - k‖⁻¹ :=
    hsph.mono fun ω hω => by
      dsimp only
      set z := B (openExitTime B (ball x s) ω).toNNReal ω
      have hz : ‖z - x‖ = s := mem_sphere_iff_norm.1 hω
      have hkm := norm_mul_norm_sub_kelvin hs.le hz hyx
      rw [show ‖z - y‖ = ‖y - x‖ / s * ‖z - k‖ by field_simp; linarith, mul_inv, inv_div]
  rw [integral_congr_ae hae, key, hnorm]
  field_simp

end LatticeProb
