import LatticeProb.Prob.BrownianExitKelvin

/-!
# The Poisson kernel of the unit ball

For `x, ζ` in `ℝ ^ d`, the Poisson kernel of the unit ball is
`P(x, ζ) = (1 - ‖x‖²) / ‖x - ζ‖ ^ d` (Axler–Bourdon–Ramey, *Harmonic Function Theory*, 1.15). It is
taken here without the normalising factor, the area of the unit sphere, which is absorbed into
averages over the sphere.

* `LatticeProb.Ishii.poissonKernel_pos`: `0 < P(x, ζ)` for `‖x‖ < 1 = ‖ζ‖` (ABR 1.20(a));
* `LatticeProb.Ishii.harmonicOnNhd_poissonKernel`: for `‖ζ‖ = 1`, the function `P(·, ζ)` is
  harmonic on `ℝ ^ d \ {ζ}` (ABR 1.18–1.19);
* `LatticeProb.Ishii.tendsto_setIntegral_poissonKernel_far`: for a boundary point `η` and `δ > 0`,
  the integral of `P(x, ·)` over the points of the sphere at distance more than `δ` from `η` tends
  to `0` as `x → η` inside the ball (ABR 1.20(c)).

The harmonicity follows from the product rule `LatticeProb.Ishii.laplacian_mul` for the Laplacian,
the radial formula `LatticeProb.laplacian_comp_norm_sub_sq`, and the identity
`‖x - ζ‖² = ‖x‖² - 2 ⟪x, ζ⟫ + 1` for `‖ζ‖ = 1`.
-/

open MeasureTheory Filter Topology Set Metric InnerProductSpace
open scoped RealInnerProductSpace Laplacian

noncomputable section

namespace LatticeProb.Ishii

section ProductRule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The product rule for the Laplacian:
`Δ (f g) = f Δ g + 2 ∑ᵢ ∂ᵢ f ∂ᵢ g + g Δ f`, where `∂ᵢ` is the derivative along the `i`-th vector of
the standard orthonormal basis. -/
theorem laplacian_mul {f g : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x)
    (hg : ContDiffAt ℝ 2 g x) :
    Δ (fun z => f z * g z) x = f x * Δ g x +
      2 * ∑ i, fderiv ℝ f x (stdOrthonormalBasis ℝ E i) *
        fderiv ℝ g x (stdOrthonormalBasis ℝ E i) + g x * Δ f x := by
  have hf1 : ∀ᶠ z in 𝓝 x, DifferentiableAt ℝ f z :=
    (hf.eventually (by simp)).mono fun z hz => hz.differentiableAt (by norm_num)
  have hg1 : ∀ᶠ z in 𝓝 x, DifferentiableAt ℝ g z :=
    (hg.eventually (by simp)).mono fun z hz => hz.differentiableAt (by norm_num)
  have hderiv : fderiv ℝ (fun z => f z * g z) =ᶠ[𝓝 x]
      fun z => f z • fderiv ℝ g z + g z • fderiv ℝ f z := by
    filter_upwards [hf1, hg1] with z hfz hgz
    exact fderiv_mul hfz hgz
  have hf2 : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hg2 : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hH : HasFDerivAt (fun z => f z • fderiv ℝ g z + g z • fderiv ℝ f z)
      ((f x • fderiv ℝ (fderiv ℝ g) x + (fderiv ℝ f x).smulRight (fderiv ℝ g x)) +
        (g x • fderiv ℝ (fderiv ℝ f) x + (fderiv ℝ g x).smulRight (fderiv ℝ f x))) x :=
    ((hf.differentiableAt (by norm_num)).hasFDerivAt.smul hg2.hasFDerivAt).add
      ((hg.differentiableAt (by norm_num)).hasFDerivAt.smul hf2.hasFDerivAt)
  have key : ∀ v, fderiv ℝ (fderiv ℝ (fun z => f z * g z)) x v v =
      f x * fderiv ℝ (fderiv ℝ g) x v v + 2 * (fderiv ℝ f x v * fderiv ℝ g x v) +
        g x * fderiv ℝ (fderiv ℝ f) x v v := by
    intro v
    rw [hderiv.fderiv_eq, hH.fderiv]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, smul_eq_mul]
    ring
  simp only [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_two_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, key]
  simp only [Finset.sum_add_distrib, Finset.mul_sum]

end ProductRule

variable {d : ℕ}

/-- The Poisson kernel of the unit ball of `ℝ ^ d`, `P(x, ζ) = (1 - ‖x‖²) / ‖x - ζ‖ ^ d`, without
the normalising factor. -/
def poissonKernel (x ζ : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (1 - ‖x‖ ^ 2) / ‖x - ζ‖ ^ d

/-- The Poisson kernel is positive on the open unit ball. -/
theorem poissonKernel_pos {x ζ : EuclideanSpace ℝ (Fin d)} (hx : ‖x‖ < 1) (hζ : ‖ζ‖ = 1) :
    0 < poissonKernel x ζ := by
  have hne : x ≠ ζ := by
    rintro rfl
    exact hx.ne hζ
  have h1 : ‖x‖ ^ 2 < 1 := pow_lt_one₀ (norm_nonneg _) hx two_ne_zero
  have h2 : 0 < ‖x - ζ‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  exact div_pos (by linarith) (pow_pos h2 d)

/-- The Poisson kernel is nonnegative on the closed unit ball. -/
theorem poissonKernel_nonneg {x : EuclideanSpace ℝ (Fin d)} (hx : ‖x‖ ≤ 1)
    (ζ : EuclideanSpace ℝ (Fin d)) : 0 ≤ poissonKernel x ζ := by
  have h1 : ‖x‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hx
  exact div_nonneg (by linarith) (by positivity)

/-- The Poisson kernel as the product `(1 - ‖x‖²) (‖x - ζ‖²) ^ (-d / 2)`. -/
theorem poissonKernel_eq_mul_rpow (x ζ : EuclideanSpace ℝ (Fin d)) :
    poissonKernel x ζ = (1 - ‖x‖ ^ 2) * (‖x - ζ‖ ^ 2) ^ (-(d : ℝ) / 2) := by
  have h : (‖x - ζ‖ ^ 2) ^ (-(d : ℝ) / 2) = (‖x - ζ‖ ^ d)⁻¹ := by
    rw [← Real.rpow_natCast ‖x - ζ‖ 2, ← Real.rpow_mul (norm_nonneg _),
      ← Real.rpow_natCast ‖x - ζ‖ d, ← Real.rpow_neg (norm_nonneg _)]
    congr 1
    push_cast
    ring
  rw [poissonKernel, div_eq_mul_inv, h]

/-- For `‖ζ‖ = 1`, the Poisson kernel `P(·, ζ)` is harmonic away from `ζ`. -/
theorem harmonicOnNhd_poissonKernel {ζ : EuclideanSpace ℝ (Fin d)} (hζ : ‖ζ‖ = 1) :
    HarmonicOnNhd (fun x => poissonKernel x ζ) {ζ}ᶜ := by
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = -(d : ℝ) / 2 := ⟨_, rfl⟩
  have hF : (fun x => poissonKernel x ζ) =
      fun x => (1 - ‖x - 0‖ ^ 2) * (‖x - ζ‖ ^ 2) ^ p := by
    funext x
    rw [sub_zero, poissonKernel_eq_mul_rpow, hp]
  have hcd1 : ContDiff ℝ 2 (fun x : EuclideanSpace ℝ (Fin d) => 1 - ‖x - 0‖ ^ 2) :=
    contDiff_const.sub ((contDiff_id.sub contDiff_const).norm_sq (𝕜 := ℝ))
  have hcd2 : ∀ z : EuclideanSpace ℝ (Fin d), z ≠ ζ →
      ContDiffAt ℝ 2 (fun x : EuclideanSpace ℝ (Fin d) => (‖x - ζ‖ ^ 2) ^ p) z := fun z hz =>
    (contDiff_id.sub contDiff_const).norm_sq (𝕜 := ℝ).contDiffAt.rpow_const_of_ne
      (pow_ne_zero 2 (norm_ne_zero_iff.2 (sub_ne_zero.2 hz)))
  intro x hx
  refine ⟨?_, ?_⟩
  · rw [hF]
    exact hcd1.contDiffAt.mul (hcd2 x hx)
  filter_upwards [isOpen_compl_singleton.mem_nhds hx] with z hz
  have hz' : z ≠ ζ := hz
  have hu0 : ‖z - ζ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 (sub_ne_zero.2 hz'))
  have hΔ1 := laplacian_comp_norm_sub_sq (φ := fun t => 1 - t) (φ' := fun _ => -1) (φ'' := 0)
    (c := 0) (x := z) hcd1.contDiffAt (Eventually.of_forall fun t => (hasDerivAt_id' t).const_sub 1)
    (hasDerivAt_const _ _)
  have hΔ2 := laplacian_comp_norm_sub_sq (φ := fun t => t ^ p)
    (φ' := fun t => p * t ^ (p - 1)) (φ'' := p * ((p - 1) * (‖z - ζ‖ ^ 2) ^ (p - 1 - 1)))
    (hcd2 z hz') ((eventually_ne_nhds hu0).mono fun t ht => Real.hasDerivAt_rpow_const (Or.inl ht))
    ((Real.hasDerivAt_rpow_const (Or.inl hu0)).const_mul p)
  have hd1 : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin d) => 1 - ‖x - 0‖ ^ 2)
      (-(2 • (innerSL ℝ (z - 0)).comp (ContinuousLinearMap.id ℝ _))) z :=
    ((hasFDerivAt_id z).sub_const 0).norm_sq.const_sub 1
  have hd2 : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin d) => (‖x - ζ‖ ^ 2) ^ p)
      ((p * (‖z - ζ‖ ^ 2) ^ (p - 1)) •
        (2 • (innerSL ℝ (z - ζ)).comp (ContinuousLinearMap.id ℝ _))) z := by
    have hr : HasDerivAt (fun t : ℝ => t ^ p) (p * (‖z - ζ‖ ^ 2) ^ (p - 1)) (‖z - ζ‖ ^ 2) :=
      Real.hasDerivAt_rpow_const (Or.inl hu0)
    exact hr.comp_hasFDerivAt z ((hasFDerivAt_id z).sub_const ζ).norm_sq
  have hsum : ∑ i, fderiv ℝ (fun x : EuclideanSpace ℝ (Fin d) => 1 - ‖x - 0‖ ^ 2) z
      (stdOrthonormalBasis ℝ _ i) *
        fderiv ℝ (fun x : EuclideanSpace ℝ (Fin d) => (‖x - ζ‖ ^ 2) ^ p) z
          (stdOrthonormalBasis ℝ _ i) =
      -(4 * p * (‖z - ζ‖ ^ 2) ^ (p - 1)) * ⟪z, z - ζ⟫ := by
    rw [hd1.fderiv, hd2.fderiv, ← (stdOrthonormalBasis ℝ _).sum_inner_mul_inner z (z - ζ),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [neg_apply, smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, innerSL_apply_apply,
      smul_eq_mul, nsmul_eq_mul, sub_zero]
    rw [real_inner_comm (stdOrthonormalBasis ℝ _ i) (z - ζ)]
    push_cast
    ring
  have he1 : (‖z - ζ‖ ^ 2) ^ (p - 1 - 1) * ‖z - ζ‖ ^ 2 = (‖z - ζ‖ ^ 2) ^ (p - 1) := by
    rw [← Real.rpow_add_one hu0]
    congr 1
    ring
  have he2 : (‖z - ζ‖ ^ 2) ^ p = (‖z - ζ‖ ^ 2) ^ (p - 1) * ‖z - ζ‖ ^ 2 := by
    rw [← Real.rpow_add_one hu0]
    congr 1
    ring
  have hn : ‖z - ζ‖ ^ 2 = ‖z‖ ^ 2 - 2 * ⟪z, ζ⟫ + 1 := by
    rw [norm_sub_sq_real, hζ, one_pow]
  have hi : ⟪z, z - ζ⟫ = ‖z‖ ^ 2 - ⟪z, ζ⟫ := by
    rw [inner_sub_right, real_inner_self_eq_norm_sq]
  rw [hF, Pi.zero_apply, laplacian_mul hcd1.contDiffAt (hcd2 z hz'), hsum, hΔ1, hΔ2]
  simp only [finrank_euclideanSpace_fin, sub_zero]
  subst hp
  linear_combination (1 - ‖z‖ ^ 2) * 4 * (-(d : ℝ) / 2) * (-(d : ℝ) / 2 - 1) * he1 +
    (-2 * (d : ℝ)) * he2 + (-2 * (d : ℝ) * (‖z - ζ‖ ^ 2) ^ (-(d : ℝ) / 2 - 1)) * hn +
    4 * (d : ℝ) * (‖z - ζ‖ ^ 2) ^ (-(d : ℝ) / 2 - 1) * hi

/-- Away from a boundary point `η`, the Poisson kernel has vanishing mass as `x → η` inside the
ball: for `δ > 0`, the integral of `P(x, ·)` over the points of the unit sphere at distance more
than `δ` from `η` tends to `0`. -/
theorem tendsto_setIntegral_poissonKernel_far {η : EuclideanSpace ℝ (Fin d)} (hη : ‖η‖ = 1)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun x => ∫ ζ in {ζ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 |
        δ < ‖(ζ : EuclideanSpace ℝ (Fin d)) - η‖}, poissonKernel x ζ
        ∂((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere))
      (𝓝[ball 0 1] η) (𝓝 0) := by
  set σ := (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere
  have hc : Continuous fun x : EuclideanSpace ℝ (Fin d) =>
      (1 - ‖x‖ ^ 2) * (2 / δ) ^ d * σ.real univ := by
    fun_prop
  have h0 : (1 - ‖η‖ ^ 2) * (2 / δ) ^ d * σ.real univ = 0 := by
    rw [hη]
    ring
  have hlim := hc.tendsto η
  rw [h0] at hlim
  refine squeeze_zero_norm' ?_ (hlim.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds η (half_pos hδ))]
    with x hx hxη
  rw [mem_ball_zero_iff] at hx
  rw [mem_ball, dist_eq_norm] at hxη
  have hC : 0 ≤ (1 - ‖x‖ ^ 2) * (2 / δ) ^ d := by
    have : ‖x‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hx.le
    have : 0 ≤ 2 / δ := by positivity
    have : 0 ≤ 1 - ‖x‖ ^ 2 := by linarith
    positivity
  refine (norm_setIntegral_le_of_norm_le_const (measure_lt_top σ _) fun ζ hζ => ?_).trans
    (mul_le_mul_of_nonneg_left (measureReal_mono (subset_univ _)) hC)
  have hζ' : δ < ‖(ζ : EuclideanSpace ℝ (Fin d)) - η‖ := hζ
  have hfar : δ / 2 ≤ ‖x - ζ‖ := by
    have := norm_sub_le_norm_sub_add_norm_sub (ζ : EuclideanSpace ℝ (Fin d)) x η
    rw [norm_sub_rev (ζ : EuclideanSpace ℝ (Fin d)) x] at this
    linarith
  have h1 : 0 ≤ 1 - ‖x‖ ^ 2 := by
    have : ‖x‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hx.le
    linarith
  rw [Real.norm_of_nonneg (poissonKernel_nonneg hx.le _), poissonKernel]
  calc (1 - ‖x‖ ^ 2) / ‖x - ζ‖ ^ d ≤ (1 - ‖x‖ ^ 2) / (δ / 2) ^ d :=
        div_le_div_of_nonneg_left h1 (by positivity)
          (pow_le_pow_left₀ (by positivity) hfar d)
    _ = (1 - ‖x‖ ^ 2) * (2 / δ) ^ d := by
        rw [div_eq_mul_inv, ← inv_pow, inv_div]

end LatticeProb.Ishii
