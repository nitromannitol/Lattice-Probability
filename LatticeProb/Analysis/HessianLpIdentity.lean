import LatticeProb.Analysis.HessianLpReduction

/-!
# The Hessian energy identity

For `w` smooth on the ball `B(0, 4/3)` and a smooth cutoff `η` compactly supported in that ball,
two integrations by parts express `∫ η² |D²w|²` through `Δ w`, `D η` and `D w`:
`∫ η² ∑ᵢⱼ (∂ᵢ∂ⱼ w)² = ∫ η² (Δ w)² + 2 ∫ η Δ w ⟨D η, D w⟩ - 2 ∫ η ∑ᵢⱼ ∂ᵢη ∂ᵢ∂ⱼ w ∂ⱼ w`.

The identity is first proved for globally smooth `w` on a finite-dimensional inner product space
with an additive Haar measure. The local statement follows by replacing `w` with `χ w` for a bump
function `χ` equal to `1` near the support of `η`.
-/

open MeasureTheory Metric Filter Topology
open scoped InnerProductSpace ContDiff
open Laplacian

namespace HessianAdapter

section Global

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem contDiff_fderiv_apply' {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (v : E) :
    ContDiff ℝ ∞ (fun x => fderiv ℝ f x v) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

private theorem fderiv_fderiv_apply {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (x u v : E) :
    fderiv ℝ (fderiv ℝ f) x u v = fderiv ℝ (fun y => fderiv ℝ f y v) x u := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  rw [fderiv_clm_apply hd (differentiableAt_const v)]
  simp

private theorem fderiv_apply_comm {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (u v : E) :
    (fun x => fderiv ℝ (fun y => fderiv ℝ f y v) x u) =
      fun x => fderiv ℝ (fun y => fderiv ℝ f y u) x v := by
  funext x
  rw [← fderiv_fderiv_apply hf, ← fderiv_fderiv_apply hf]
  exact hf.contDiffAt.isSymmSndFDerivAt (by simp) u v

private theorem fderiv_mul_sq_mul_apply {g η h : E → ℝ} (hg : ContDiff ℝ ∞ g)
    (hη : ContDiff ℝ ∞ η) (hh : ContDiff ℝ ∞ h) (x v : E) :
    fderiv ℝ (fun y => g y * (η y ^ 2 * h y)) x v =
      fderiv ℝ g x v * (η x ^ 2 * h x) +
        g x * (2 * η x * fderiv ℝ η x v * h x + η x ^ 2 * fderiv ℝ h x v) := by
  have hg' := hg.differentiable (by simp) x
  have hη' := hη.differentiable (by simp) x
  have hh' := hh.differentiable (by simp) x
  have hη2 : DifferentiableAt ℝ (fun y => η y ^ 2) x := hη'.pow 2
  have hη2h : DifferentiableAt ℝ (fun y => η y ^ 2 * h y) x := hη2.mul hh'
  rw [fderiv_fun_mul hg' hη2h, fderiv_fun_mul hη2 hh', fderiv_fun_pow 2 hη']
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- The pointwise identity behind the two integrations by parts: in the directions `u` and `v`,
the difference of two divergence terms equals the integrand of the Hessian identity. -/
private theorem fderiv_sub_fderiv_eq {w η : E → ℝ} (hw : ContDiff ℝ ∞ w) (hη : ContDiff ℝ ∞ η)
    (u v x : E) :
    fderiv ℝ (fun y => fderiv ℝ w y v * (η y ^ 2 * fderiv ℝ (fun z => fderiv ℝ w z v) y u)) x u -
        fderiv ℝ (fun y => fderiv ℝ w y v * (η y ^ 2 * fderiv ℝ (fun z => fderiv ℝ w z u) y u))
          x v =
      η x ^ 2 * fderiv ℝ (fun z => fderiv ℝ w z v) x u ^ 2 -
          η x ^ 2 * fderiv ℝ (fun z => fderiv ℝ w z u) x u *
            fderiv ℝ (fun z => fderiv ℝ w z v) x v +
        2 * η x * (fderiv ℝ η x u * fderiv ℝ (fun z => fderiv ℝ w z v) x u * fderiv ℝ w x v) -
        2 * η x * fderiv ℝ (fun z => fderiv ℝ w z u) x u * (fderiv ℝ η x v * fderiv ℝ w x v) := by
  have hG : ∀ t, ContDiff ℝ ∞ (fun z => fderiv ℝ w z t) := contDiff_fderiv_apply' hw
  have hH : ∀ s t, ContDiff ℝ ∞ (fun y => fderiv ℝ (fun z => fderiv ℝ w z t) y s) :=
    fun s t => contDiff_fderiv_apply' (hG t) s
  rw [fderiv_mul_sq_mul_apply (hG v) hη (hH u v), fderiv_mul_sq_mul_apply (hG v) hη (hH u u)]
  have h3 : fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ w z v) y u) x u =
      fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ w z u) y u) x v := by
    rw [fderiv_apply_comm hw u v]
    exact congrFun (fderiv_apply_comm (hG u) u v) x
  rw [h3]
  ring

variable [FiniteDimensional ℝ E]

private theorem laplacian_eq_sum_fderiv' {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    Δ f = fun y => ∑ i, fderiv ℝ (fun y' => fderiv ℝ f y' (stdOrthonormalBasis ℝ E i)) y
      (stdOrthonormalBasis ℝ E i) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  funext y
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  exact fderiv_fderiv_apply hf y _ _

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

private theorem integral_fderiv_apply_eq_zero {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (v : E) : ∫ x, fderiv ℝ ψ x v ∂μ = 0 := by
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := μ)
    (f := fun _ : E => (1 : ℝ)) (g := ψ) (v := v) (by simp) ?_ ?_
    (fun x _ => differentiableAt_const _) (fun x _ => hψ.differentiable (by simp) x)
  · simpa using h
  · simpa using (contDiff_fderiv_apply' hψ v).continuous.integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ v)
  · simpa using hψ.continuous.integrable_of_hasCompactSupport hc

/-- The Hessian energy identity for a globally smooth function `w` and a smooth compactly
supported cutoff `η`, in the standard orthonormal basis. -/
theorem integral_sq_mul_sum_fderiv_fderiv_sq {w η : E → ℝ} (hw : ContDiff ℝ ∞ w)
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) :
    (∫ x, η x ^ 2 * ∑ i, ∑ j, (fderiv ℝ (fderiv ℝ w) x
        (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j)) ^ 2 ∂μ) =
      (∫ x, η x ^ 2 * Δ w x ^ 2 ∂μ) +
        2 * (∫ x, η x * Δ w x * ∑ i, fderiv ℝ η x (stdOrthonormalBasis ℝ E i) *
          fderiv ℝ w x (stdOrthonormalBasis ℝ E i) ∂μ) -
        2 * ∫ x, η x * ∑ i, ∑ j, fderiv ℝ η x (stdOrthonormalBasis ℝ E i) *
          fderiv ℝ (fderiv ℝ w) x (stdOrthonormalBasis ℝ E i)
            (stdOrthonormalBasis ℝ E j) * fderiv ℝ w x (stdOrthonormalBasis ℝ E j) ∂μ := by
  have hasCompactSupport_of_eq_zero : ∀ g : E → ℝ, (∀ x, η x = 0 → g x = 0) →
      HasCompactSupport g := fun g h0 =>
    HasCompactSupport.intro hc fun x hx => h0 x (image_eq_zero_of_notMem_tsupport hx)
  have integrable_of_eq_zero : ∀ g : E → ℝ, Continuous g → (∀ x, η x = 0 → g x = 0) →
      Integrable g μ := fun g hg h0 =>
    hg.integrable_of_hasCompactSupport (hasCompactSupport_of_eq_zero g h0)
  have hG : ∀ v, ContDiff ℝ ∞ (fun z => fderiv ℝ w z v) := contDiff_fderiv_apply' hw
  have hH : ∀ u v, ContDiff ℝ ∞ (fun y => fderiv ℝ (fun z => fderiv ℝ w z v) y u) :=
    fun u v => contDiff_fderiv_apply' (hG v) u
  have hT : ∀ v, ContDiff ℝ ∞ (fun z => fderiv ℝ η z v) := contDiff_fderiv_apply' hη
  have hD2 : ∀ u v, Continuous (fun x => fderiv ℝ (fderiv ℝ w) x u v) := fun u v =>
    (((hw.fderiv_right (m := ∞) (by simp)).continuous_fderiv (by simp)).clm_apply
      continuous_const).clm_apply continuous_const
  have hΔ : Continuous (Δ w) := by
    rw [laplacian_eq_sum_fderiv' hw]
    exact continuous_finsetSum _ fun i _ => (hH _ _).continuous
  have hΦ : ∀ u v, ContDiff ℝ ∞
      (fun y => fderiv ℝ w y v * (η y ^ 2 * fderiv ℝ (fun z => fderiv ℝ w z v) y u)) :=
    fun u v => (hG v).mul ((hη.pow 2).mul (hH u v))
  have hΨ : ∀ u v, ContDiff ℝ ∞
      (fun y => fderiv ℝ w y v * (η y ^ 2 * fderiv ℝ (fun z => fderiv ℝ w z u) y u)) :=
    fun u v => (hG v).mul ((hη.pow 2).mul (hH u u))
  have hΦc : ∀ u v, HasCompactSupport
      (fun y => fderiv ℝ w y v * (η y ^ 2 * fderiv ℝ (fun z => fderiv ℝ w z v) y u)) :=
    fun u v => hasCompactSupport_of_eq_zero _ fun x hx => by simp [hx]
  have hΨc : ∀ u v, HasCompactSupport
      (fun y => fderiv ℝ w y v * (η y ^ 2 * fderiv ℝ (fun z => fderiv ℝ w z u) y u)) :=
    fun u v => hasCompactSupport_of_eq_zero _ fun x hx => by simp [hx]
  have hΦi : ∀ u v t, Integrable (fun x => fderiv ℝ
      (fun y => fderiv ℝ w y v * (η y ^ 2 * fderiv ℝ (fun z => fderiv ℝ w z v) y u)) x t) μ :=
    fun u v t => (contDiff_fderiv_apply' (hΦ u v) t).continuous.integrable_of_hasCompactSupport
      ((hΦc u v).fderiv_apply ℝ t)
  have hΨi : ∀ u v t, Integrable (fun x => fderiv ℝ
      (fun y => fderiv ℝ w y v * (η y ^ 2 * fderiv ℝ (fun z => fderiv ℝ w z u) y u)) x t) μ :=
    fun u v t => (contDiff_fderiv_apply' (hΨ u v) t).continuous.integrable_of_hasCompactSupport
      ((hΨc u v).fderiv_apply ℝ t)
  set b := stdOrthonormalBasis ℝ E with hb
  have hpt : ∀ x, η x ^ 2 * ∑ i, ∑ j, (fderiv ℝ (fderiv ℝ w) x (b i) (b j)) ^ 2 =
      η x ^ 2 * Δ w x ^ 2 +
        2 * (η x * Δ w x * ∑ i, fderiv ℝ η x (b i) * fderiv ℝ w x (b i)) -
        2 * (η x * ∑ i, ∑ j, fderiv ℝ η x (b i) * fderiv ℝ (fderiv ℝ w) x (b i) (b j) *
          fderiv ℝ w x (b j)) +
      ∑ i, ∑ j, (fderiv ℝ (fun y => fderiv ℝ w y (b j) *
          (η y ^ 2 * fderiv ℝ (fun z => fderiv ℝ w z (b j)) y (b i))) x (b i) -
        fderiv ℝ (fun y => fderiv ℝ w y (b j) *
          (η y ^ 2 * fderiv ℝ (fun z => fderiv ℝ w z (b i)) y (b i))) x (b j)) := by
    intro x
    simp only [fderiv_sub_fderiv_eq hw hη, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      fderiv_fderiv_apply hw, laplacian_eq_sum_fderiv' hw]
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
    ring
  have hB : Integrable (fun x => η x ^ 2 * Δ w x ^ 2) μ :=
    integrable_of_eq_zero _ ((hη.continuous.pow 2).mul (hΔ.pow 2)) fun x hx => by simp [hx]
  have hC : Integrable
      (fun x => η x * Δ w x * ∑ i, fderiv ℝ η x (b i) * fderiv ℝ w x (b i)) μ :=
    integrable_of_eq_zero _ ((hη.continuous.mul hΔ).mul
      (continuous_finsetSum _ fun i _ => (hT _).continuous.mul (hG _).continuous))
      fun x hx => by simp [hx]
  have hE : Integrable (fun x => η x * ∑ i, ∑ j, fderiv ℝ η x (b i) *
      fderiv ℝ (fderiv ℝ w) x (b i) (b j) * fderiv ℝ w x (b j)) μ :=
    integrable_of_eq_zero _ (hη.continuous.mul (continuous_finsetSum _ fun i _ =>
      continuous_finsetSum _ fun j _ => ((hT _).continuous.mul (hD2 _ _)).mul (hG _).continuous))
      fun x hx => by simp [hx]
  have hSij : ∀ i j, Integrable (fun x => fderiv ℝ (fun y => fderiv ℝ w y (b j) *
          (η y ^ 2 * fderiv ℝ (fun z => fderiv ℝ w z (b j)) y (b i))) x (b i) -
        fderiv ℝ (fun y => fderiv ℝ w y (b j) *
          (η y ^ 2 * fderiv ℝ (fun z => fderiv ℝ w z (b i)) y (b i))) x (b j)) μ :=
    fun i j => (hΦi (b i) (b j) (b i)).sub (hΨi (b i) (b j) (b j))
  have hS : ∀ i, Integrable (fun x => ∑ j, (fderiv ℝ (fun y => fderiv ℝ w y (b j) *
          (η y ^ 2 * fderiv ℝ (fun z => fderiv ℝ w z (b j)) y (b i))) x (b i) -
        fderiv ℝ (fun y => fderiv ℝ w y (b j) *
          (η y ^ 2 * fderiv ℝ (fun z => fderiv ℝ w z (b i)) y (b i))) x (b j))) μ :=
    fun i => integrable_finsetSum _ fun j _ => hSij i j
  have hS0 : ∫ x, ∑ i, ∑ j, (fderiv ℝ (fun y => fderiv ℝ w y (b j) *
          (η y ^ 2 * fderiv ℝ (fun z => fderiv ℝ w z (b j)) y (b i))) x (b i) -
        fderiv ℝ (fun y => fderiv ℝ w y (b j) *
          (η y ^ 2 * fderiv ℝ (fun z => fderiv ℝ w z (b i)) y (b i))) x (b j)) ∂μ = 0 := by
    rw [integral_finsetSum _ fun i _ => hS i]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => hSij i j]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [integral_sub (hΦi (b i) (b j) (b i)) (hΨi (b i) (b j) (b j)),
      integral_fderiv_apply_eq_zero (hΦ (b i) (b j)) (hΦc (b i) (b j)),
      integral_fderiv_apply_eq_zero (hΨ (b i) (b j)) (hΨc (b i) (b j)), sub_zero]
  have hC2 : Integrable
      (fun x => 2 * (η x * Δ w x * ∑ i, fderiv ℝ η x (b i) * fderiv ℝ w x (b i))) μ :=
    hC.const_mul 2
  have hE2 : Integrable (fun x => 2 * (η x * ∑ i, ∑ j, fderiv ℝ η x (b i) *
      fderiv ℝ (fderiv ℝ w) x (b i) (b j) * fderiv ℝ w x (b j))) μ :=
    hE.const_mul 2
  have hBC : Integrable (fun x => η x ^ 2 * Δ w x ^ 2 +
      2 * (η x * Δ w x * ∑ i, fderiv ℝ η x (b i) * fderiv ℝ w x (b i))) μ := hB.add hC2
  have hBCE : Integrable (fun x => η x ^ 2 * Δ w x ^ 2 +
      2 * (η x * Δ w x * ∑ i, fderiv ℝ η x (b i) * fderiv ℝ w x (b i)) -
      2 * (η x * ∑ i, ∑ j, fderiv ℝ η x (b i) * fderiv ℝ (fderiv ℝ w) x (b i) (b j) *
        fderiv ℝ w x (b j))) μ := hBC.sub hE2
  have hSs : Integrable (fun x => ∑ i, ∑ j, (fderiv ℝ (fun y => fderiv ℝ w y (b j) *
          (η y ^ 2 * fderiv ℝ (fun z => fderiv ℝ w z (b j)) y (b i))) x (b i) -
        fderiv ℝ (fun y => fderiv ℝ w y (b j) *
          (η y ^ 2 * fderiv ℝ (fun z => fderiv ℝ w z (b i)) y (b i))) x (b j))) μ :=
    integrable_finsetSum _ fun i _ => hS i
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_add hBCE hSs,
    integral_sub hBC hE2, integral_add hB hC2, integral_const_mul, integral_const_mul, hS0,
    add_zero]

end Global

/-- L12b. The Hessian identity for `w` smooth on the ball `B(0, 4/3)` and a smooth cutoff `η`
compactly supported in that ball. -/
theorem L12b_hessian_energy (d : ℕ) : HessianEnergyStmt d := by
  intro w η hw hη hc hsub
  obtain ⟨r, hr, hKr⟩ := exists_lt_subset_ball (isClosed_tsupport η) hsub
  have hρ0 : (0 : ℝ) < max r 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hρ1 : max r 1 < 4 / 3 := max_lt hr (by norm_num)
  let χ : ContDiffBump (0 : Euc d) := ⟨max r 1, (max r 1 + 4 / 3) / 2, hρ0, by linarith⟩
  have hχ1 : ∀ x ∈ ball (0 : Euc d) (max r 1), χ x = 1 := fun x hx =>
    χ.one_of_mem_closedBall (ball_subset_closedBall hx)
  have hχs : tsupport χ ⊆ ball (0 : Euc d) (4 / 3) := by
    rw [χ.tsupport_eq]
    exact closedBall_subset_ball (by change (max r 1 + 4 / 3) / 2 < 4 / 3; linarith)
  have hv : ContDiff ℝ ∞ (fun x => χ x * w x) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ ball (0 : Euc d) (4 / 3)
    · exact χ.contDiff.contDiffAt.mul (hw.contDiffAt (isOpen_ball.mem_nhds hx))
    · have hx' : x ∉ tsupport χ := fun h => hx (hχs h)
      have h0 : (fun y => χ y * w y) =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx'] with y hy
        simp [show χ y = 0 from hy]
      exact contDiffAt_const.congr_of_eventuallyEq h0
  have hvw : ∀ x ∈ ball (0 : Euc d) (max r 1), (fun y => χ y * w y) =ᶠ[𝓝 x] w := by
    intro x hx
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    simp [hχ1 y hy]
  have hK : ∀ x, x ∉ ball (0 : Euc d) (max r 1) → η x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h =>
      hx (ball_subset_ball (le_max_left r 1) (hKr h))
  have e1 : ∀ x ∈ ball (0 : Euc d) (max r 1),
      fderiv ℝ (fun y => χ y * w y) x = fderiv ℝ w x := fun x hx => (hvw x hx).fderiv_eq
  have e2 : ∀ x ∈ ball (0 : Euc d) (max r 1),
      fderiv ℝ (fderiv ℝ (fun y => χ y * w y)) x = fderiv ℝ (fderiv ℝ w) x := fun x hx =>
    (hvw x hx).fderiv.fderiv_eq
  have e3 : ∀ x ∈ ball (0 : Euc d) (max r 1), Δ (fun y => χ y * w y) x = Δ w x :=
    fun x hx => (InnerProductSpace.laplacian_congr_nhds (hvw x hx)).eq_of_nhds
  have key := integral_sq_mul_sum_fderiv_fderiv_sq (μ := volume) hv hη hc
  have i1 : (∫ x, η x ^ 2 * ∑ i, ∑ j, (fderiv ℝ (fderiv ℝ w) x
      (stdOrthonormalBasis ℝ (Euc d) i) (stdOrthonormalBasis ℝ (Euc d) j)) ^ 2) =
      ∫ x, η x ^ 2 * ∑ i, ∑ j, (fderiv ℝ (fderiv ℝ (fun y => χ y * w y)) x
        (stdOrthonormalBasis ℝ (Euc d) i) (stdOrthonormalBasis ℝ (Euc d) j)) ^ 2 := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ ball (0 : Euc d) (max r 1)
    · simp only [e2 x hx]
    · simp [hK x hx]
  have i2 : (∫ x, η x ^ 2 * Δ w x ^ 2) = ∫ x, η x ^ 2 * Δ (fun y => χ y * w y) x ^ 2 := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ ball (0 : Euc d) (max r 1)
    · simp only [e3 x hx]
    · simp [hK x hx]
  have i3 : (∫ x, η x * Δ w x * ∑ i, fderiv ℝ η x (stdOrthonormalBasis ℝ (Euc d) i) *
      fderiv ℝ w x (stdOrthonormalBasis ℝ (Euc d) i)) =
      ∫ x, η x * Δ (fun y => χ y * w y) x * ∑ i, fderiv ℝ η x (stdOrthonormalBasis ℝ (Euc d) i) *
        fderiv ℝ (fun y => χ y * w y) x (stdOrthonormalBasis ℝ (Euc d) i) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ ball (0 : Euc d) (max r 1)
    · simp only [e1 x hx, e3 x hx]
    · simp [hK x hx]
  have i4 : (∫ x, η x * ∑ i, ∑ j, fderiv ℝ η x (stdOrthonormalBasis ℝ (Euc d) i) *
      fderiv ℝ (fderiv ℝ w) x (stdOrthonormalBasis ℝ (Euc d) i)
        (stdOrthonormalBasis ℝ (Euc d) j) * fderiv ℝ w x (stdOrthonormalBasis ℝ (Euc d) j)) =
      ∫ x, η x * ∑ i, ∑ j, fderiv ℝ η x (stdOrthonormalBasis ℝ (Euc d) i) *
        fderiv ℝ (fderiv ℝ (fun y => χ y * w y)) x (stdOrthonormalBasis ℝ (Euc d) i)
          (stdOrthonormalBasis ℝ (Euc d) j) *
            fderiv ℝ (fun y => χ y * w y) x (stdOrthonormalBasis ℝ (Euc d) j) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ ball (0 : Euc d) (max r 1)
    · simp only [e1 x hx, e2 x hx]
    · simp [hK x hx]
  rw [i1, i2, i3, i4]
  exact key

end HessianAdapter
