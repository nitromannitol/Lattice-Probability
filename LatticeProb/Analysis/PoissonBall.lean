import LatticeProb.Analysis.PoissonBallIntegral

/-!
# The Dirichlet problem on balls of `ℝ ^ d`

For a function `f` continuous on the sphere `sphere a r` of `ℝ ^ d`, the rescaled Poisson integral
of `f` on the open ball `ball a r`, extended by `f` on the sphere, is harmonic on the open ball,
continuous on the closed ball, and its value at the centre is the average of `f` over the sphere
(Axler–Bourdon–Ramey, *Harmonic Function Theory*, Theorem 1.17; Gilbarg–Trudinger, Theorem 2.6).

* `LatticeProb.Ishii.harmonicAt_comp_smul_sub`: harmonicity is preserved by the affine change of
  variables `y ↦ c • (y - a)` with `c ≠ 0`;
* `LatticeProb.Ishii.tendsto_poissonIntegral_nhdsWithin_ball`: at every point `η` of the unit
  sphere, the Poisson integral of `f` tends to `f η` as `x → η` inside the ball (ABR, proof of
  1.17, pp. 14–15);
* `LatticeProb.Ishii.continuousOn_piecewise_poissonIntegral`: the Poisson integral of `f`, extended
  by `f` on the sphere, is continuous on the closed unit ball;
* `LatticeProb.Ishii.exists_harmonic_ball`: the solution of the Dirichlet problem on a ball, with
  the mean-value identity at the centre.
-/

open MeasureTheory Filter Topology Set Metric InnerProductSpace
open scoped Laplacian

noncomputable section

namespace LatticeProb.Ishii

section Affine

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The Laplacian of `y ↦ g (c • (y - a))` at `y` is `c ^ 2` times the Laplacian of `g` at
`c • (y - a)`. -/
theorem laplacian_comp_smul_sub (g : E → ℝ) {c : ℝ} (hc : c ≠ 0) (a y : E) :
    Δ (fun y => g (c • (y - a))) y = c ^ 2 * Δ g (c • (y - a)) := by
  set L : E ≃L[ℝ] E := (LinearEquiv.smulOfNeZero ℝ E c hc).toContinuousLinearEquiv
  have hL : ∀ z, L z = c • z := fun z => rfl
  have hD : iteratedFDeriv ℝ 2 (fun y => g (c • (y - a))) y =
      (iteratedFDeriv ℝ 2 g (c • (y - a))).compContinuousLinearMap
        fun _ => (L : E →L[ℝ] E) := by
    have h1 : iteratedFDeriv ℝ 2 (fun y => g (c • (y - a))) y =
        iteratedFDeriv ℝ 2 (g ∘ L) (y - a) :=
      iteratedFDeriv_comp_sub (f := g ∘ L) 2 a y
    have h2 := L.iteratedFDerivWithin_comp_right g uniqueDiffOn_univ (mem_univ (L (y - a))) 2
    rw [preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at h2
    rw [h1, h2, hL]
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    laplacian_eq_iteratedFDeriv_stdOrthonormalBasis g]
  simp only [hD, ContinuousMultilinearMap.compContinuousLinearMap_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  set v := stdOrthonormalBasis ℝ E i
  have h3 : (fun j : Fin 2 => (L : E →L[ℝ] E) (![v, v] j)) = fun j => c • ![v, v] j :=
    funext fun j => hL _
  have h4 := ContinuousMultilinearMap.map_smul_univ (iteratedFDeriv ℝ 2 g (c • (y - a)))
    (fun _ => c) ![v, v]
  rw [h3, h4, Fin.prod_const, smul_eq_mul]

/-- Harmonicity is preserved by the affine change of variables `y ↦ c • (y - a)`, `c ≠ 0`. -/
theorem harmonicAt_comp_smul_sub {g : E → ℝ} {c : ℝ} (hc : c ≠ 0) {a x : E}
    (hg : HarmonicAt g (c • (x - a))) : HarmonicAt (fun y => g (c • (y - a))) x := by
  have hφ : ContDiff ℝ 2 fun y : E => c • (y - a) := by fun_prop
  constructor
  · exact hg.1.comp x hφ.contDiffAt
  · have hev : ∀ᶠ y in 𝓝 x, Δ g (c • (y - a)) = 0 :=
      hφ.continuous.continuousAt.tendsto.eventually hg.2
    filter_upwards [hev] with y hy
    rw [Pi.zero_apply, laplacian_comp_smul_sub g hc a y, hy, mul_zero]

end Affine

variable {d : ℕ}

/-- At every point `η` of the unit sphere, the Poisson integral of a function `f` continuous on
the sphere tends to `f η` as `x → η` inside the ball (ABR, proof of 1.17, pp. 14–15). -/
theorem tendsto_poissonIntegral_nhdsWithin_ball (hd : 1 ≤ d)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : ContinuousOn f (sphere 0 1))
    {η : EuclideanSpace ℝ (Fin d)} (hη : ‖η‖ = 1) :
    Tendsto (poissonIntegral f) (𝓝[ball 0 1] η) (𝓝 (f η)) := by
  set σ := (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere
  have : Nontrivial (EuclideanSpace ℝ (Fin d)) :=
    Module.nontrivial_of_finrank_pos (by rw [finrank_euclideanSpace_fin]; omega)
  have : NeZero σ := ⟨Measure.toSphere_ne_zero _⟩
  have hS : 0 < σ.real univ := measureReal_univ_pos
  have hηs : η ∈ sphere (0 : EuclideanSpace ℝ (Fin d)) 1 := mem_sphere_zero_iff_norm.2 hη
  obtain ⟨M, hM⟩ :=
    (isCompact_sphere (0 : EuclideanSpace ℝ (Fin d)) 1).exists_bound_of_continuousOn hf
  have hfc : Continuous fun ζ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 => f ζ :=
    hf.comp_continuous continuous_subtype_val fun ζ => ζ.2
  have hPc : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ < 1 →
      Continuous fun ζ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
        poissonKernel x (ζ : EuclideanSpace ℝ (Fin d)) := by
    intro x hx
    refine continuous_const.div (by fun_prop) fun ζ => ?_
    have hne : x - (ζ : EuclideanSpace ℝ (Fin d)) ≠ 0 := sub_ne_zero.2 fun h =>
      hx.ne (by rw [h, norm_eq_of_mem_sphere ζ])
    exact pow_ne_zero d (norm_ne_zero_iff.2 hne)
  have hint : ∀ {F : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 → ℝ}, Continuous F →
      Integrable F σ := fun hF =>
    hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hmass : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ < 1 →
      ∫ ζ, poissonKernel x (ζ : EuclideanSpace ℝ (Fin d)) ∂σ = σ.real univ := by
    intro x hx
    have h := average_poissonKernel_eq_one hd hx
    rw [average_eq, smul_eq_mul, inv_mul_eq_one₀ hS.ne'] at h
    exact h.symm
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hfδ⟩ := Metric.continuousWithinAt_iff.1 (hf η hηs) (ε / 2) (half_pos hε)
  set far := {ζ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 |
    δ / 2 < ‖(ζ : EuclideanSpace ℝ (Fin d)) - η‖}
  have hfar : MeasurableSet far :=
    measurableSet_lt measurable_const (measurable_subtype_coe.sub_const η).norm
  have htail := (tendsto_setIntegral_poissonKernel_far hη (half_pos hδ)).const_mul
    (2 * M * (σ.real univ)⁻¹)
  rw [mul_zero] at htail
  filter_upwards [self_mem_nhdsWithin, (tendsto_order.1 htail).2 (ε / 2) (half_pos hε)]
    with x hx hxt
  rw [mem_ball_zero_iff] at hx
  have hP0 : ∀ ζ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      0 ≤ poissonKernel x (ζ : EuclideanSpace ℝ (Fin d)) := fun ζ => poissonKernel_nonneg hx.le _
  have hPi : Integrable (fun ζ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
      poissonKernel x (ζ : EuclideanSpace ℝ (Fin d))) σ := hint (hPc x hx)
  have heq : poissonIntegral f x - f η = (σ.real univ)⁻¹ *
      ∫ ζ, poissonKernel x (ζ : EuclideanSpace ℝ (Fin d)) * (f ζ - f η) ∂σ := by
    have h1 : ∫ ζ, poissonKernel x (ζ : EuclideanSpace ℝ (Fin d)) * (f ζ - f η) ∂σ =
        ∫ ζ, poissonKernel x (ζ : EuclideanSpace ℝ (Fin d)) * f ζ ∂σ - σ.real univ * f η := by
      simp only [mul_sub]
      rw [integral_sub (hint (F := fun ζ => poissonKernel x (ζ : EuclideanSpace ℝ (Fin d)) * f ζ)
        ((hPc x hx).mul hfc)) (hPi.mul_const _), integral_mul_const,
        hmass x hx]
    rw [h1, poissonIntegral, average_eq, smul_eq_mul, mul_sub, ← mul_assoc,
      inv_mul_cancel₀ hS.ne', one_mul]
  have hbound : ∀ ζ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      ‖poissonKernel x (ζ : EuclideanSpace ℝ (Fin d)) * (f ζ - f η)‖ ≤
        ε / 2 * poissonKernel x (ζ : EuclideanSpace ℝ (Fin d)) +
          2 * M * far.indicator (fun ζ => poissonKernel x (ζ : EuclideanSpace ℝ (Fin d))) ζ := by
    intro ζ
    rw [norm_mul, Real.norm_of_nonneg (hP0 ζ)]
    by_cases hζ : ζ ∈ far
    · rw [indicator_of_mem hζ]
      have h1 : ‖f ζ - f η‖ ≤ 2 * M := by
        have := norm_sub_le (f ζ) (f η)
        have := hM ζ ζ.2
        have := hM η hηs
        linarith
      have h2 := mul_le_mul_of_nonneg_left h1 (hP0 ζ)
      have h3 := mul_nonneg (half_pos hε).le (hP0 ζ)
      linarith
    · rw [indicator_of_notMem hζ, mul_zero, add_zero]
      have hnear : dist (ζ : EuclideanSpace ℝ (Fin d)) η < δ := by
        have hζ' : ¬δ / 2 < ‖(ζ : EuclideanSpace ℝ (Fin d)) - η‖ := hζ
        rw [dist_eq_norm]
        linarith [not_lt.1 hζ']
      have h1 := hfδ ζ.2 hnear
      rw [dist_eq_norm] at h1
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right h1.le (hP0 ζ)
  have hI : ‖∫ ζ, poissonKernel x (ζ : EuclideanSpace ℝ (Fin d)) * (f ζ - f η) ∂σ‖ ≤
      ε / 2 * σ.real univ +
        2 * M * ∫ ζ in far, poissonKernel x (ζ : EuclideanSpace ℝ (Fin d)) ∂σ := by
    have hg := (hPi.const_mul (ε / 2)).add ((hPi.indicator hfar).const_mul (2 * M))
    refine (norm_integral_le_of_norm_le
      (g := fun ζ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
        ε / 2 * poissonKernel x (ζ : EuclideanSpace ℝ (Fin d)) +
          2 * M * far.indicator (fun ζ => poissonKernel x (ζ : EuclideanSpace ℝ (Fin d))) ζ)
      hg (Eventually.of_forall hbound)).trans_eq ?_
    rw [integral_add (hPi.const_mul _) ((hPi.indicator hfar).const_mul _), integral_const_mul,
      integral_const_mul, hmass x hx, integral_indicator hfar]
  rw [dist_eq_norm, heq, norm_mul, Real.norm_of_nonneg (inv_nonneg.2 hS.le)]
  have hsplit : (σ.real univ)⁻¹ * (ε / 2 * σ.real univ +
      2 * M * ∫ ζ in far, poissonKernel x (ζ : EuclideanSpace ℝ (Fin d)) ∂σ) =
      ε / 2 + 2 * M * (σ.real univ)⁻¹ *
        ∫ ζ in far, poissonKernel x (ζ : EuclideanSpace ℝ (Fin d)) ∂σ := by
    field_simp
  calc (σ.real univ)⁻¹ *
        ‖∫ ζ, poissonKernel x (ζ : EuclideanSpace ℝ (Fin d)) * (f ζ - f η) ∂σ‖
      ≤ (σ.real univ)⁻¹ * (ε / 2 * σ.real univ +
          2 * M * ∫ ζ in far, poissonKernel x (ζ : EuclideanSpace ℝ (Fin d)) ∂σ) :=
        mul_le_mul_of_nonneg_left hI (inv_nonneg.2 hS.le)
    _ < ε := by rw [hsplit]; linarith

open Classical in
/-- The Poisson integral of a function `f` continuous on the unit sphere, extended by `f` on the
sphere, is continuous on the closed unit ball (ABR 1.17). -/
theorem continuousOn_piecewise_poissonIntegral (hd : 1 ≤ d)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : ContinuousOn f (sphere 0 1)) :
    ContinuousOn (Set.piecewise (ball 0 1) (poissonIntegral f) f) (closedBall 0 1) := by
  intro x hx
  rcases (mem_closedBall_zero_iff.1 hx).lt_or_eq with hlt | heq
  · have hxb : x ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1 := mem_ball_zero_iff.2 hlt
    have hc : ContinuousAt (poissonIntegral f) x :=
      (harmonicOnNhd_poissonIntegral f hf x hxb).1.continuousAt
    refine (hc.congr ?_).continuousWithinAt
    filter_upwards [isOpen_ball.mem_nhds hxb] with y hy
    exact (piecewise_eq_of_mem _ _ _ hy).symm
  · have hnb : ∀ y ∈ sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        y ∉ ball (0 : EuclideanSpace ℝ (Fin d)) 1 := by
      intro y hy
      rw [mem_ball_zero_iff, mem_sphere_zero_iff_norm.1 hy]
      exact lt_irrefl 1
    have hxs : x ∈ sphere (0 : EuclideanSpace ℝ (Fin d)) 1 := mem_sphere_zero_iff_norm.2 heq
    rw [← ball_union_sphere]
    refine ContinuousWithinAt.union ?_ ?_
    · rw [ContinuousWithinAt, piecewise_eq_of_notMem _ _ _ (hnb x hxs)]
      exact tendsto_nhdsWithin_congr (fun y hy => (piecewise_eq_of_mem _ _ _ hy).symm)
        (tendsto_poissonIntegral_nhdsWithin_ball hd hf heq)
    · exact (hf x hxs).congr (fun y hy => piecewise_eq_of_notMem _ _ _ (hnb y hy))
        (piecewise_eq_of_notMem _ _ _ (hnb x hxs))

/-- The Dirichlet problem on a ball of `ℝ ^ d`: for `f` continuous on the sphere `sphere a r`,
there is a function harmonic on the open ball, continuous on the closed ball and equal to `f` on
the sphere, whose value at the centre is the average of `f` over the sphere (ABR 1.17,
Gilbarg–Trudinger, Theorem 2.6). -/
theorem exists_harmonic_ball {a : EuclideanSpace ℝ (Fin d)} {r : ℝ} (hr : 0 < r)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : ContinuousOn f (sphere a r)) :
    ∃ h : EuclideanSpace ℝ (Fin d) → ℝ, HarmonicOnNhd h (ball a r) ∧
      ContinuousOn h (closedBall a r) ∧ EqOn h f (sphere a r) ∧
      h a = ⨍ z, f (a + r • (z : EuclideanSpace ℝ (Fin d)))
        ∂((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere) := by
  classical
  set g : EuclideanSpace ℝ (Fin d) → ℝ := fun z => f (a + r • z) with hg_def
  set φ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun y => r⁻¹ • (y - a)
    with hφ_def
  have hφc : Continuous φ := by fun_prop
  have hnorm : ∀ y, ‖φ y‖ = ‖y - a‖ / r := fun y => by
    rw [hφ_def, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr.le), inv_mul_eq_div]
  have hgc : ContinuousOn g (sphere 0 1) := by
    refine hf.comp (by fun_prop : Continuous fun z : EuclideanSpace ℝ (Fin d) =>
      a + r • z).continuousOn fun z hz => ?_
    rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.le,
      mem_sphere_zero_iff_norm.1 hz, mul_one]
  have hga : ∀ y, g (φ y) = f y := fun y => by
    simp only [hg_def, hφ_def, smul_smul, mul_inv_cancel₀ hr.ne', one_smul, add_sub_cancel]
  refine ⟨fun y => Set.piecewise (ball 0 1) (poissonIntegral g) g (φ y), ?_, ?_, ?_, ?_⟩
  · intro y hy
    have hφy : φ y ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1 := by
      rw [mem_ball, dist_eq_norm] at hy
      rw [mem_ball_zero_iff, hnorm, div_lt_one hr]
      exact hy
    have hU : ∀ᶠ z in 𝓝 y, φ z ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1 :=
      hφc.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds hφy)
    refine (harmonicAt_congr_nhds ?_).2 (harmonicAt_comp_smul_sub (inv_ne_zero hr.ne')
      (harmonicOnNhd_poissonIntegral g hgc _ hφy))
    filter_upwards [hU] with z hz
    exact piecewise_eq_of_mem _ _ _ hz
  · rcases Nat.eq_zero_or_pos d with rfl | hd
    · exact (continuous_of_const fun x y => by rw [Subsingleton.elim x y]).continuousOn
    · refine (continuousOn_piecewise_poissonIntegral hd hgc).comp hφc.continuousOn fun y hy => ?_
      rw [mem_closedBall, dist_eq_norm] at hy
      rw [mem_closedBall_zero_iff, hnorm, div_le_one hr]
      exact hy
  · intro y hy
    have hφy : φ y ∉ ball (0 : EuclideanSpace ℝ (Fin d)) 1 := by
      rw [mem_sphere, dist_eq_norm] at hy
      rw [mem_ball_zero_iff, hnorm, hy, div_self hr.ne']
      exact lt_irrefl 1
    simp only [piecewise_eq_of_notMem _ _ _ hφy, hga]
  · have hφa : φ a = 0 := by rw [hφ_def]; simp
    have hφa' : φ a ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1 := by
      rw [hφa]
      exact mem_ball_self one_pos
    have h0 : ∀ ζ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        poissonKernel (0 : EuclideanSpace ℝ (Fin d)) ζ = 1 := fun ζ => by
      rw [poissonKernel, norm_zero, zero_sub, norm_neg, norm_eq_of_mem_sphere ζ]
      norm_num
    simp only [piecewise_eq_of_mem _ _ _ hφa']
    rw [hφa, poissonIntegral]
    simp only [h0, one_mul, hg_def]

end LatticeProb.Ishii
