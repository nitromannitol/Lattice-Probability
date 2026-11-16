import LatticeProb.Analysis.Schauder.Continuum

/-!
# Sine coefficients of test functions

For a test function `f` of the unit cube,
`⟨Δf, φ_k⟩ = −λ_k ⟨f, φ_k⟩` (integration by parts twice in each coordinate; the sine modes are
eigenfunctions of the Laplacian), and hence `|⟨f, φ_k⟩| ≤ C_N λ_k^{−N}` for every `N`. The module
also records the smoothness of the sine modes and the elementary bound of each squared frequency
`π² (k_i + 1)²` by the eigenvalue `λ_k`.
-/

open MeasureTheory LatticeProb

noncomputable section

namespace LatticeProb.Analysis.Schauder

variable {d : ℕ}

/-- The Laplacian `Σ_i ∂_i² f` of a function on `ℝ^d`, written with the iterated derivative. -/
def laplacianSum (f : Euc d → ℝ) (z : Euc d) : ℝ :=
  ∑ i, iteratedFDeriv ℝ 2 f z ![EuclideanSpace.single i 1, EuclideanSpace.single i 1]

/-- The derivative of `g` in the direction `v`, as a function. -/
def dirDeriv (v : Euc d) (g : Euc d → ℝ) (z : Euc d) : ℝ := fderiv ℝ g z v

/-- The derivative of a smooth function in a fixed direction is smooth. -/
theorem contDiff_dirDeriv {g : Euc d → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (v : Euc d) :
    ContDiff ℝ (⊤ : ℕ∞) (dirDeriv v g) :=
  (hg.fderiv_right le_rfl).clm_apply contDiff_const

/-- The derivative in a fixed direction of a compactly supported function is compactly
supported. -/
theorem hasCompactSupport_dirDeriv {g : Euc d → ℝ} (hg : HasCompactSupport g) (v : Euc d) :
    HasCompactSupport (dirDeriv v g) :=
  hg.fderiv_apply ℝ v

/-- The support of a directional derivative lies in the support of the function. -/
theorem tsupport_dirDeriv_subset (g : Euc d → ℝ) (v : Euc d) :
    tsupport (dirDeriv v g) ⊆ tsupport g :=
  tsupport_fderiv_apply_subset ℝ v

/-- Directional derivatives of test functions are test functions. -/
theorem isTestFn_dirDeriv {D : Set (Euc d)} {g : Euc d → ℝ} (hg : Sobolev.IsTestFn D g)
    (v : Euc d) : Sobolev.IsTestFn D (dirDeriv v g) :=
  ⟨contDiff_dirDeriv hg.1 v, hasCompactSupport_dirDeriv hg.2.1 v,
    (tsupport_dirDeriv_subset g v).trans hg.2.2⟩

/-- The second iterated derivative of a smooth function in the direction `(v, v)` is the
directional derivative of the directional derivative. -/
theorem iteratedFDeriv_two_self_apply {g : Euc d → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (z v : Euc d) :
    iteratedFDeriv ℝ 2 g z ![v, v] = dirDeriv v (dirDeriv v g) z := by
  have hd : DifferentiableAt ℝ (fderiv ℝ g) z :=
    ((hg.fderiv_right (m := 1) (by norm_cast)).differentiable (by simp)) z
  have h1 := fderiv_clm_apply (c := fderiv ℝ g) (u := fun _ => v) hd (differentiableAt_const v)
  rw [iteratedFDeriv_two_apply]
  unfold dirDeriv
  rw [h1]
  simp

/-- The Laplacian of a smooth function as a sum of repeated directional derivatives. -/
theorem laplacianSum_eq_sum_dirDeriv {g : Euc d → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (z : Euc d) :
    laplacianSum g z =
      ∑ i, dirDeriv (EuclideanSpace.single i 1) (dirDeriv (EuclideanSpace.single i 1) g) z := by
  unfold laplacianSum
  exact Finset.sum_congr rfl fun i _ => iteratedFDeriv_two_self_apply hg z _

/-- Integration by parts in a direction `v`, for a compactly supported smooth `f` against a
smooth `g`. -/
theorem integral_dirDeriv_mul {f g : Euc d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (v : Euc d) :
    ∫ z, dirDeriv v f z * g z = -∫ z, f z * dirDeriv v g z := by
  have hf1 : Continuous f := hf.continuous
  have hg1 : Continuous g := hg.continuous
  have hdf : Continuous (dirDeriv v f) := (contDiff_dirDeriv hf v).continuous
  have hdg : Continuous (dirDeriv v g) := (contDiff_dirDeriv hg v).continuous
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := f) (g := g)
    (v := v)
    ((hdf.mul hg1).integrable_of_hasCompactSupport (hasCompactSupport_dirDeriv hfc v).mul_right)
    ((hf1.mul hdg).integrable_of_hasCompactSupport hfc.mul_right)
    ((hf1.mul hg1).integrable_of_hasCompactSupport hfc.mul_right)
    (fun x _ => (hf.differentiable (by simp)) x) (fun x _ => (hg.differentiable (by simp)) x)
  unfold dirDeriv
  linarith

/-- Integrating by parts twice in a direction `v`. -/
theorem integral_dirDeriv_dirDeriv_mul {f g : Euc d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (v : Euc d) :
    ∫ z, dirDeriv v (dirDeriv v f) z * g z = ∫ z, f z * dirDeriv v (dirDeriv v g) z := by
  rw [integral_dirDeriv_mul (contDiff_dirDeriv hf v) (hasCompactSupport_dirDeriv hfc v) hg v,
    integral_dirDeriv_mul hf hfc (contDiff_dirDeriv hg v) v, neg_neg]

/-- The Laplacian is symmetric for a compactly supported smooth `f` against a smooth `g`. -/
theorem integral_laplacianSum_mul {f g : Euc d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ∫ z, laplacianSum f z * g z = ∫ z, f z * laplacianSum g z := by
  have hint : ∀ (i : Fin d), Integrable (fun z => f z * dirDeriv (EuclideanSpace.single i 1)
      (dirDeriv (EuclideanSpace.single i 1) g) z) volume := fun i =>
    (hf.continuous.mul (contDiff_dirDeriv (contDiff_dirDeriv hg _) _).continuous
      ).integrable_of_hasCompactSupport hfc.mul_right
  have hint' : ∀ (i : Fin d), Integrable (fun z => dirDeriv (EuclideanSpace.single i 1)
      (dirDeriv (EuclideanSpace.single i 1) f) z * g z) volume := fun i =>
    ((contDiff_dirDeriv (contDiff_dirDeriv hf _) _).continuous.mul hg.continuous
      ).integrable_of_hasCompactSupport
      (hasCompactSupport_dirDeriv (hasCompactSupport_dirDeriv hfc _) _).mul_right
  simp_rw [laplacianSum_eq_sum_dirDeriv hf, laplacianSum_eq_sum_dirDeriv hg, Finset.sum_mul,
    Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ => hint' i, integral_finsetSum _ fun i _ => hint i]
  exact Finset.sum_congr rfl fun i _ => integral_dirDeriv_dirDeriv_mul hf hfc hg _

/-- The one-variable factor `t ↦ √2 sin(a t)` of a sine mode. -/
def sineFactor (a : ℝ) (t : ℝ) : ℝ := Real.sqrt 2 * Real.sin (a * t)

/-- The one-variable factor of a sine mode is smooth. -/
theorem contDiff_sineFactor (a : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (sineFactor a) := by
  unfold sineFactor
  fun_prop

/-- The product of all the factors of a sine mode except the `i`-th. -/
def sineModeRest (k : Fin d → ℕ) (i : Fin d) (z : Euc d) : ℝ :=
  ∏ j ∈ Finset.univ.erase i, sineFactor (Real.pi * ((k j : ℝ) + 1)) (z j)

/-- A sine mode is the product of its `i`-th factor and the rest. -/
theorem sineMode_eq_sineModeRest_mul (k : Fin d → ℕ) (i : Fin d) (z : Euc d) :
    sineMode k z = sineModeRest k i z * sineFactor (Real.pi * ((k i : ℝ) + 1)) (z i) := by
  unfold sineMode sineModeRest sineFactor
  exact (Finset.prod_erase_mul _ _ (Finset.mem_univ i)).symm

/-- The factors of a sine mode other than the `i`-th form a smooth function. -/
theorem contDiff_sineModeRest (k : Fin d → ℕ) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (sineModeRest k i) :=
  contDiff_prod fun j _ => (contDiff_sineFactor _).comp
    (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff

/-- A sine mode is smooth. -/
theorem contDiff_sineMode (k : Fin d → ℕ) : ContDiff ℝ (⊤ : ℕ∞) (sineMode k) :=
  contDiff_prod fun j _ => (contDiff_sineFactor _).comp
    (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff

/-- A sine mode is `C^n` for every natural number `n`. -/
theorem contDiff_sineMode_nat (k : Fin d → ℕ) (n : ℕ) : ContDiff ℝ n (sineMode k) :=
  (contDiff_sineMode k).of_le (by exact_mod_cast le_top)

/-- The factors of a sine mode other than the `i`-th do not depend on the `i`-th coordinate. -/
theorem dirDeriv_sineModeRest_self (k : Fin d → ℕ) (i : Fin d) (z : Euc d) :
    dirDeriv (EuclideanSpace.single i 1) (sineModeRest k i) z = 0 := by
  have hd : DifferentiableAt ℝ (sineModeRest k i) z :=
    ((contDiff_sineModeRest k i).differentiable (by simp)) z
  unfold dirDeriv
  rw [← hd.lineDeriv_eq_fderiv]
  have : (fun t : ℝ => sineModeRest k i (z + t • EuclideanSpace.single i 1)) =
      fun _ => sineModeRest k i z := by
    funext t
    unfold sineModeRest
    refine Finset.prod_congr rfl fun j hj => ?_
    have : j ≠ i := (Finset.mem_erase.1 hj).1
    simp [this]
  rw [lineDeriv, this]
  simp

/-- Product rule for `P(z) h(z_i)` in the direction `e_i`, when `P` does not depend on `z_i`. -/
theorem dirDeriv_mul_proj {P : Euc d → ℝ} {h : ℝ → ℝ} (i : Fin d)
    (hP : Differentiable ℝ P) (hPi : ∀ z, dirDeriv (EuclideanSpace.single i 1) P z = 0)
    (hh : Differentiable ℝ h) (z : Euc d) :
    dirDeriv (EuclideanSpace.single i 1) (fun w => P w * h (w i)) z = P z * deriv h (z i) := by
  have h1 : HasFDerivAt (fun w : Euc d => h (w i)) (deriv h (z i) • (EuclideanSpace.proj i :
      Euc d →L[ℝ] ℝ)) z :=
    ((hh (z i)).hasDerivAt).comp_hasFDerivAt z (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt
  have h2 : HasFDerivAt (fun w : Euc d => P w * h (w i)) _ z := (hP z).hasFDerivAt.mul h1
  have h3 := hPi z
  unfold dirDeriv at h3 ⊢
  rw [h2.fderiv]
  simp [h3]

/-- The derivative of the one-variable factor of a sine mode. -/
theorem deriv_sineFactor (a : ℝ) :
    deriv (sineFactor a) = fun t => Real.sqrt 2 * (a * Real.cos (a * t)) := by
  funext t
  unfold sineFactor
  have h : HasDerivAt (fun t : ℝ => Real.sqrt 2 * Real.sin (a * t))
      (Real.sqrt 2 * (Real.cos (a * t) * a)) t :=
    (((hasDerivAt_id t).const_mul a).sin).const_mul (Real.sqrt 2) |>.congr_deriv (by simp)
  rw [h.deriv]
  ring

/-- The second derivative of the one-variable factor of a sine mode. -/
theorem deriv_deriv_sineFactor (a : ℝ) :
    deriv (deriv (sineFactor a)) = fun t => -(a ^ 2 * sineFactor a t) := by
  rw [deriv_sineFactor]
  funext t
  unfold sineFactor
  have h : HasDerivAt (fun t : ℝ => Real.sqrt 2 * (a * Real.cos (a * t)))
      (Real.sqrt 2 * (a * (-Real.sin (a * t) * a))) t :=
    ((((hasDerivAt_id t).const_mul a).cos).const_mul a).const_mul (Real.sqrt 2)
      |>.congr_deriv (by simp)
  rw [h.deriv]
  ring

/-- The second derivative of a sine mode in the direction `e_i`. -/
theorem dirDeriv_dirDeriv_sineMode (k : Fin d → ℕ) (i : Fin d) (z : Euc d) :
    dirDeriv (EuclideanSpace.single i 1) (dirDeriv (EuclideanSpace.single i 1) (sineMode k)) z =
      -((Real.pi * ((k i : ℝ) + 1)) ^ 2 * sineMode k z) := by
  set a : ℝ := Real.pi * ((k i : ℝ) + 1) with ha
  have hP : Differentiable ℝ (sineModeRest k i) :=
    (contDiff_sineModeRest k i).differentiable (by simp)
  have hmode : sineMode k = fun w => sineModeRest k i w * sineFactor a (w i) :=
    funext (sineMode_eq_sineModeRest_mul k i)
  have h1 : dirDeriv (EuclideanSpace.single i 1) (sineMode k) =
      fun w => sineModeRest k i w * deriv (sineFactor a) (w i) := by
    funext w
    rw [hmode]
    exact dirDeriv_mul_proj i hP (dirDeriv_sineModeRest_self k i)
      ((contDiff_sineFactor a).differentiable (by simp)) w
  have hdiff : Differentiable ℝ (deriv (sineFactor a)) := by
    rw [deriv_sineFactor]
    fun_prop
  rw [h1, dirDeriv_mul_proj i hP (dirDeriv_sineModeRest_self k i) hdiff z,
    deriv_deriv_sineFactor, sineMode_eq_sineModeRest_mul k i z]
  ring

/-- The sine modes are eigenfunctions of the Laplacian. -/
theorem laplacianSum_sineMode (k : Fin d → ℕ) (z : Euc d) :
    laplacianSum (sineMode k) z = -(dirichletEigenvalue k * sineMode k z) := by
  rw [laplacianSum_eq_sum_dirDeriv (contDiff_sineMode k)]
  simp_rw [dirDeriv_dirDeriv_sineMode]
  unfold dirichletEigenvalue
  simp_rw [mul_pow]
  rw [Finset.sum_neg_distrib, ← Finset.sum_mul, ← Finset.mul_sum]

/-- A function vanishing off the cube has the same sine coefficients as its integral against the
sine mode over the whole space. -/
theorem sineCoeff_eq_integral {g : Euc d → ℝ} (hg : ∀ z, z ∉ unitCube d → g z = 0)
    (k : Fin d → ℕ) : sineCoeff g k = ∫ z, g z * sineMode k z := by
  unfold sineCoeff
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by simp [hg z hz]

/-- The Laplacian vanishes off the support of the function. -/
theorem laplacianSum_eq_zero_of_notMem_tsupport {g : Euc d → ℝ} {z : Euc d}
    (hz : z ∉ tsupport g) : laplacianSum g z = 0 := by
  have h : iteratedFDeriv ℝ 2 g z = 0 :=
    image_eq_zero_of_notMem_tsupport fun h => hz (tsupport_iteratedFDeriv_subset 2 h)
  simp [laplacianSum, h]

/-- The support of the Laplacian lies in the support of the function. -/
theorem tsupport_laplacianSum_subset (g : Euc d → ℝ) :
    tsupport (laplacianSum g) ⊆ tsupport g :=
  closure_minimal (fun z hz => by
    by_contra h
    exact hz (laplacianSum_eq_zero_of_notMem_tsupport h)) (isClosed_tsupport _)

/-- The Laplacian of a test function is a test function. -/
theorem isTestFn_laplacianSum {D : Set (Euc d)} {f : Euc d → ℝ} (hf : Sobolev.IsTestFn D f) :
    Sobolev.IsTestFn D (laplacianSum f) := by
  have hfun : laplacianSum f = fun z =>
      ∑ i, dirDeriv (EuclideanSpace.single i 1) (dirDeriv (EuclideanSpace.single i 1) f) z :=
    funext (laplacianSum_eq_sum_dirDeriv hf.1)
  refine ⟨?_, ?_, (tsupport_laplacianSum_subset f).trans hf.2.2⟩
  · rw [hfun]
    exact ContDiff.sum fun i _ => contDiff_dirDeriv (contDiff_dirDeriv hf.1 _) _
  · exact hf.2.1.of_isClosed_subset (isClosed_tsupport _) (tsupport_laplacianSum_subset f)

/-- Iterated Laplacians of a test function are test functions. -/
theorem isTestFn_iterate_laplacianSum {D : Set (Euc d)} {f : Euc d → ℝ}
    (hf : Sobolev.IsTestFn D f) (n : ℕ) : Sobolev.IsTestFn D (laplacianSum^[n] f) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact isTestFn_laplacianSum ih

/-- The sine modes are bounded by `(√2)^d`. -/
theorem abs_sineMode_le (k : Fin d → ℕ) (z : Euc d) : |sineMode k z| ≤ Real.sqrt 2 ^ d := by
  unfold sineMode
  rw [Finset.abs_prod]
  calc ∏ i, |Real.sqrt 2 * Real.sin (Real.pi * ((k i : ℝ) + 1) * z i)|
      ≤ ∏ _i : Fin d, Real.sqrt 2 := by
        refine Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) fun i _ => ?_
        rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg 2)]
        calc Real.sqrt 2 * |Real.sin _| ≤ Real.sqrt 2 * 1 :=
              mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (Real.sqrt_nonneg 2)
          _ = Real.sqrt 2 := mul_one _
    _ = Real.sqrt 2 ^ d := by simp

/-- A bound on the sine coefficients independent of `k`. -/
theorem abs_sineCoeff_le {g : Euc d → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (hg0 : ∀ z, z ∉ unitCube d → g z = 0) (k : Fin d → ℕ) :
    |sineCoeff g k| ≤ Real.sqrt 2 ^ d * ∫ z, |g z| := by
  rw [sineCoeff_eq_integral hg0, ← integral_const_mul]
  have hint : Integrable g volume := hg.integrable_of_hasCompactSupport hgc
  refine (abs_integral_le_integral_abs).trans ?_
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => abs_nonneg _)
    (hint.abs.const_mul _) (Filter.Eventually.of_forall fun z => ?_)
  show |g z * sineMode k z| ≤ Real.sqrt 2 ^ d * |g z|
  rw [abs_mul]
  nlinarith [abs_nonneg (g z), abs_sineMode_le k z]

/-- The Dirichlet eigenvalues are positive in dimension at least one. -/
theorem dirichletEigenvalue_pos (hd : 1 ≤ d) (k : Fin d → ℕ) : 0 < dirichletEigenvalue k := by
  unfold dirichletEigenvalue
  exact mul_pos (by positivity) (Finset.sum_pos (fun i _ => by positivity)
    ⟨⟨0, hd⟩, Finset.mem_univ _⟩)

/-- The eigenvalues are nonnegative. -/
theorem dirichletEigenvalue_nonneg (k : Fin d → ℕ) : 0 ≤ dirichletEigenvalue k := by
  unfold dirichletEigenvalue
  positivity

/-- The squared frequency `π² (k_i + 1)²` of the sine mode `φ_k` in the coordinate `i`. -/
def sineFreqSq (i : Fin d) (k : Fin d → ℕ) : ℝ := (Real.pi * ((k i : ℝ) + 1)) ^ 2

/-- The squared frequency in a coordinate is nonnegative. -/
theorem sineFreqSq_nonneg (i : Fin d) (k : Fin d → ℕ) : 0 ≤ sineFreqSq i k := sq_nonneg _

/-- The squared frequency in a coordinate is at most the eigenvalue. -/
theorem sineFreqSq_le_dirichletEigenvalue (i : Fin d) (k : Fin d → ℕ) :
    sineFreqSq i k ≤ dirichletEigenvalue k := by
  unfold sineFreqSq dirichletEigenvalue
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_left
    (Finset.single_le_sum (f := fun j => ((k j : ℝ) + 1) ^ 2) (fun j _ => by positivity)
      (Finset.mem_univ i)) (by positivity)

/-- **The sine modes diagonalize the Laplacian on test functions**: for `f ∈ C_c^∞(Q)`,
`⟨Δf, φ_k⟩ = −π²|k+1|² ⟨f, φ_k⟩` (integrate by parts twice in each coordinate; the boundary terms
vanish because `f` vanishes near `∂Q`). -/
theorem sineCoeff_laplacianSum (f : Euc d → ℝ) (hf : Sobolev.IsTestFn (unitCube d) f)
    (k : Fin d → ℕ) :
    sineCoeff (laplacianSum f) k = -(dirichletEigenvalue k * sineCoeff f k) := by
  rw [sineCoeff_eq_integral (fun z hz => laplacianSum_eq_zero_of_notMem_tsupport
      fun h => hz (hf.2.2 h)),
    sineCoeff_eq_integral (fun z hz => image_eq_zero_of_notMem_tsupport fun h => hz (hf.2.2 h)),
    integral_laplacianSum_mul hf.1 hf.2.1 (contDiff_sineMode k)]
  have : ∀ z, f z * laplacianSum (sineMode k) z =
      -(dirichletEigenvalue k * (f z * sineMode k z)) := fun z => by
    rw [laplacianSum_sineMode]
    ring
  simp_rw [this]
  rw [integral_neg, integral_const_mul]

/-- The sine coefficients of the `n`-fold Laplacian of a test function of the cube. -/
theorem sineCoeff_iterate_laplacianSum {f : Euc d → ℝ} (hf : Sobolev.IsTestFn (unitCube d) f)
    (k : Fin d → ℕ) (n : ℕ) :
    sineCoeff (laplacianSum^[n] f) k = (-dirichletEigenvalue k) ^ n * sineCoeff f k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', sineCoeff_laplacianSum _ (isTestFn_iterate_laplacianSum hf n),
      ih, pow_succ]
    ring

/-- **The sine coefficients of a test function decay faster than any power of the eigenvalue**:
for every `N`, `|⟨f, φ_k⟩| ≤ C_N (π²|k+1|²)^{-N}`. -/
theorem exists_abs_sineCoeff_le (hd : 1 ≤ d) (f : Euc d → ℝ)
    (hf : Sobolev.IsTestFn (unitCube d) f) (N : ℕ) :
    ∃ C : ℝ, ∀ k : Fin d → ℕ, |sineCoeff f k| ≤ C * ((dirichletEigenvalue k) ^ N)⁻¹ := by
  have hg := isTestFn_iterate_laplacianSum hf N
  refine ⟨Real.sqrt 2 ^ d * ∫ z, |(laplacianSum^[N] f) z|, fun k => ?_⟩
  have hpos : 0 < dirichletEigenvalue k := dirichletEigenvalue_pos hd k
  have h1 := abs_sineCoeff_le hg.1.continuous hg.2.1
    (fun z hz => image_eq_zero_of_notMem_tsupport fun h => hz (hg.2.2 h)) k
  rw [sineCoeff_iterate_laplacianSum hf k N, abs_mul, abs_pow, abs_neg,
    abs_of_pos hpos] at h1
  rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos hpos N), mul_comm]
  exact h1

end LatticeProb.Analysis.Schauder

end
