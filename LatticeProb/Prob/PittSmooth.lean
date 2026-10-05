import Mathlib
import LatticeProb.Prob.PittStatements

/-!
# Pitt's Gaussian association theorem: smooth case (packet P24)

From the covariance representation `PittCovRep k` (the hypothesis `hcov`) we prove
`PittSmoothStmt k`: association of `C²_b` coordinatewise nondecreasing functions under
`N(0, S)` for `S` positive semidefinite with nonnegative entries.

Route: `N(0,S) = (stdGaussian).map A` with `A = toEuclideanCLM (CFC.sqrt S)`; the compositions
`F = f ∘ A`, `G = g ∘ A` are `C²_b`; the covariance representation gives
`Cov(F, G) = ∫ sin a · ∑_i E[∂_i F · E_W ∂_i G]`; and the integrand is pointwise nonnegative
because `∑_i ∂_i F ∂_i G = ∑_{j,l} S_{jl} ∂_j f ∂_l g ≥ 0` (monotone functions have nonnegative
partial derivatives).
-/

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder Matrix

namespace LatticeProb

/-! ### Nonnegative partial derivatives of a coordinatewise monotone function -/

/-- A coordinatewise nondecreasing differentiable function has nonnegative partial derivatives. -/
theorem pitt_fderiv_single_nonneg {k : ℕ} {f : EuclideanSpace ℝ (Fin k) → ℝ}
    (hf : PittMono f) {x : EuclideanSpace ℝ (Fin k)} (hd : DifferentiableAt ℝ f x) (j : Fin k) :
    0 ≤ fderiv ℝ f x (EuclideanSpace.single j (1 : ℝ)) := by
  have h1 : HasDerivAt (fun t : ℝ => x + t • EuclideanSpace.single j (1 : ℝ))
      (EuclideanSpace.single j (1 : ℝ)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (EuclideanSpace.single j (1 : ℝ))).const_add x
  have h2 : HasDerivAt (fun t : ℝ => f (x + t • EuclideanSpace.single j (1 : ℝ)))
      (fderiv ℝ f x (EuclideanSpace.single j (1 : ℝ))) 0 := by
    have hd' : DifferentiableAt ℝ f (x + (0 : ℝ) • EuclideanSpace.single j (1 : ℝ)) := by
      simpa using hd
    have := hd'.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
    rw [zero_smul, add_zero] at this
    exact this
  refine h2.nonneg_of_monotone ?_
  intro s t hst
  refine hf _ _ fun i => ?_
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.single_apply]
  split_ifs
  · simpa using hst
  · simp

/-! ### Coordinate expansion and the algebraic identity -/

/-- A continuous linear functional on `ℝ^k` is determined by its values on the standard basis. -/
theorem pitt_clm_apply_eq_sum {k : ℕ} (L : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ)
    (v : EuclideanSpace ℝ (Fin k)) :
    L v = ∑ j, v j * L (EuclideanSpace.single j (1 : ℝ)) := by
  have hv : v = ∑ j, v j • EuclideanSpace.single j (1 : ℝ) := by
    ext m
    simp [Pi.single_apply]
  conv_lhs => rw [hv]
  simp [map_sum]

/-- The `j`-th coordinate of `toEuclideanCLM B (e_i)` is `B j i`. -/
theorem pitt_toEuclideanCLM_single_apply {k : ℕ} (B : Matrix (Fin k) (Fin k) ℝ) (i j : Fin k) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) B (EuclideanSpace.single i (1 : ℝ)) j = B j i := by
  have : Matrix.toEuclideanCLM (𝕜 := ℝ) B (EuclideanSpace.single i (1 : ℝ))
      = WithLp.toLp 2 (B *ᵥ Pi.single i (1 : ℝ)) := rfl
  rw [this]
  simp

/-- **The algebraic identity**:
`∑_i (∑_j B_{ji} p_j)(∑_l B_{li} q_l) = ∑_{j,l} (B Bᵀ)_{jl} p_j q_l`. -/
theorem pitt_sum_identity {k : ℕ} (B : Matrix (Fin k) (Fin k) ℝ) (p q : Fin k → ℝ) :
    ∑ i, (∑ j, B j i * p j) * (∑ l, B l i * q l)
      = ∑ j, ∑ l, (B * B.transpose) j l * (p j * q l) := by
  calc ∑ i, (∑ j, B j i * p j) * (∑ l, B l i * q l)
      = ∑ i, ∑ j, ∑ l, B j i * B l i * (p j * q l) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
    _ = ∑ j, ∑ i, ∑ l, B j i * B l i * (p j * q l) := Finset.sum_comm
    _ = ∑ j, ∑ l, ∑ i, B j i * B l i * (p j * q l) :=
        Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ j, ∑ l, (B * B.transpose) j l * (p j * q l) := by
        simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]

/-- The square root of a positive semidefinite matrix satisfies `B Bᵀ = S`. -/
theorem pitt_sqrt_mul_transpose {k : ℕ} {S : Matrix (Fin k) (Fin k) ℝ} (hS : S.PosSemidef) :
    CFC.sqrt S * (CFC.sqrt S).transpose = S := by
  have hher : (CFC.sqrt S).IsHermitian := (CFC.sqrt_nonneg S).isSelfAdjoint.isHermitian
  have hMt : (CFC.sqrt S).transpose = CFC.sqrt S := by
    ext i j
    have h := congr_fun (congr_fun hher i) j
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_apply] using h
  rw [hMt]
  exact CFC.sqrt_mul_sqrt_self S hS.nonneg

/-- The quadratic expression `∑_{j,l} S_{jl} p_j q_l` is nonnegative for nonnegative data. -/
theorem pitt_form_nonneg {k : ℕ} {S : Matrix (Fin k) (Fin k) ℝ} (hS : ∀ i j, 0 ≤ S i j)
    {p q : Fin k → ℝ} (hp : ∀ j, 0 ≤ p j) (hq : ∀ l, 0 ≤ q l) :
    0 ≤ ∑ j, ∑ l, S j l * (p j * q l) :=
  Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun l _ =>
    mul_nonneg (hS j l) (mul_nonneg (hp j) (hq l))

/-- **Pointwise nonnegativity**: for `S` PSD with nonnegative entries and coordinatewise
nondecreasing differentiable `f, g`, with `B = √S`,
`∑_i (Df(u) B e_i)(Dg(u') B e_i) ≥ 0`. -/
theorem pitt_sum_nonneg {k : ℕ} {S : Matrix (Fin k) (Fin k) ℝ} (hS : S.PosSemidef)
    (hS0 : ∀ i j, 0 ≤ S i j) {f g : EuclideanSpace ℝ (Fin k) → ℝ} (hf : PittMono f)
    (hg : PittMono g) (hfd : Differentiable ℝ f) (hgd : Differentiable ℝ g)
    (u u' : EuclideanSpace ℝ (Fin k)) :
    0 ≤ ∑ i, fderiv ℝ f u (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)
          (EuclideanSpace.single i (1 : ℝ)))
        * fderiv ℝ g u' (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)
          (EuclideanSpace.single i (1 : ℝ))) := by
  have hexp : ∀ (h : EuclideanSpace ℝ (Fin k) → ℝ) (x : EuclideanSpace ℝ (Fin k)) (i : Fin k),
      fderiv ℝ h x (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) (EuclideanSpace.single i (1 : ℝ)))
        = ∑ j, CFC.sqrt S j i * fderiv ℝ h x (EuclideanSpace.single j (1 : ℝ)) := by
    intro h x i
    rw [pitt_clm_apply_eq_sum]
    simp only [pitt_toEuclideanCLM_single_apply]
  simp only [hexp]
  rw [pitt_sum_identity (CFC.sqrt S) (fun j => fderiv ℝ f u (EuclideanSpace.single j (1 : ℝ)))
    (fun l => fderiv ℝ g u' (EuclideanSpace.single l (1 : ℝ))), pitt_sqrt_mul_transpose hS]
  exact pitt_form_nonneg hS0 (fun j => pitt_fderiv_single_nonneg hf (hfd u) j)
    (fun l => pitt_fderiv_single_nonneg hg (hgd u') l)

/-! ### Composition with a continuous linear map preserves `C²_b` -/

/-- Chain rule for a composition with a continuous linear map on the right. -/
theorem pitt_fderiv_comp_clm {d : ℕ} (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Differentiable ℝ f) (x v : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (fun z => f (A z)) x v = fderiv ℝ f (A x) (A v) := by
  have h := (hf (A x)).hasFDerivAt.comp x A.hasFDerivAt
  have h' : fderiv ℝ (fun z => f (A z)) x = (fderiv ℝ f (A x)).comp A := h.fderiv
  rw [h']
  rfl

/-- **(1)** `C²_b` is stable under precomposition with a continuous linear map. -/
theorem pitt_comp_clm_C2b {d : ℕ} (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : mehlerIClassC2b f) :
    mehlerIClassC2b (fun z => f (A z)) := by
  obtain ⟨hf2, ⟨C0, h0⟩, ⟨C1, h1⟩, ⟨C2, h2⟩⟩ := hf
  have hfd : Differentiable ℝ f := hf2.differentiable (by norm_num)
  have hC1 : 0 ≤ C1 := (norm_nonneg _).trans (h1 0)
  have hC2 : 0 ≤ C2 := (norm_nonneg _).trans (h2 0)
  refine ⟨hf2.comp A.contDiff, ⟨C0, fun x => h0 _⟩, ⟨C1 * ‖A‖, fun x => ?_⟩,
    ⟨C2 * (‖A‖ * ‖A‖), fun x => ?_⟩⟩
  · have h := (hfd (A x)).hasFDerivAt.comp x A.hasFDerivAt
    have h' : fderiv ℝ (fun z => f (A z)) x = (fderiv ℝ f (A x)).comp A := h.fderiv
    rw [h']
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (h1 _) (norm_nonneg _))
  · have h := A.iteratedFDeriv_comp_right hf2 x (i := 2) (by norm_num)
    have h' : iteratedFDeriv ℝ 2 (fun z => f (A z)) x
        = (iteratedFDeriv ℝ 2 f (A x)).compContinuousLinearMap fun _ => A := h
    rw [h']
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_two]
    exact mul_le_mul_of_nonneg_right (h2 _) (by positivity)

/-! ### Nonnegativity of the covariance representation -/

/-- If the pointwise form `∑_i Df(u) A e_i · Dg(u') A e_i` is nonnegative, then the whole
right-hand side of the covariance representation for `(f ∘ A, g ∘ A)` is nonnegative. -/
theorem pitt_inner_nonneg {k : ℕ}
    (A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))
    {f g : EuclideanSpace ℝ (Fin k) → ℝ} (hf : mehlerIClassC2b f) (hg : mehlerIClassC2b g)
    (hpt : ∀ u u' : EuclideanSpace ℝ (Fin k),
      0 ≤ ∑ i : Fin k, fderiv ℝ f u (A (EuclideanSpace.single i (1 : ℝ)))
        * fderiv ℝ g u' (A (EuclideanSpace.single i (1 : ℝ)))) (a : ℝ) :
    0 ≤ ∑ i : Fin k, ∫ z, fderiv ℝ (fun z => f (A z)) z (EuclideanSpace.single i (1 : ℝ)) *
      (∫ w, fderiv ℝ (fun z => g (A z)) (Real.cos a • z + Real.sin a • w)
        (EuclideanSpace.single i (1 : ℝ)) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
      ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) := by
  have hF := pitt_comp_clm_C2b A hf
  have hG := pitt_comp_clm_C2b A hg
  have hfd : Differentiable ℝ f := hf.1.differentiable (by norm_num)
  have hgd : Differentiable ℝ g := hg.1.differentiable (by norm_num)
  -- continuity and bounds of the partial derivatives
  have hX : ∀ i : Fin k, Continuous (mehlerIDir (EuclideanSpace.single i (1 : ℝ))
      (fun z => f (A z))) ∧ ∃ C, ∀ x, |mehlerIDir (EuclideanSpace.single i (1 : ℝ))
        (fun z => f (A z)) x| ≤ C := fun i => hF.c1b.dir_cont_bdd _
  have hY : ∀ i : Fin k, Continuous (mehlerIDir (EuclideanSpace.single i (1 : ℝ))
      (fun z => g (A z))) ∧ ∃ C, ∀ x, |mehlerIDir (EuclideanSpace.single i (1 : ℝ))
        (fun z => g (A z)) x| ≤ C := fun i => hG.c1b.dir_cont_bdd _
  have hMc : ∀ i : Fin k, Continuous (mehlerI a (mehlerIDir (EuclideanSpace.single i (1 : ℝ))
      (fun z => g (A z)))) := fun i => mehlerI_continuous a (hG.dir_c1b _)
  have hint : ∀ i : Fin k, Integrable (fun z => fderiv ℝ (fun z => f (A z)) z
      (EuclideanSpace.single i (1 : ℝ)) * (∫ w, fderiv ℝ (fun z => g (A z))
        (Real.cos a • z + Real.sin a • w) (EuclideanSpace.single i (1 : ℝ))
        ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))) (stdGaussian (EuclideanSpace ℝ (Fin k))) := by
    intro i
    obtain ⟨CX, hCX⟩ := (hX i).2
    obtain ⟨CY, hCY⟩ := (hG.dir_c1b (EuclideanSpace.single i (1 : ℝ))).2.1
    have hCX0 : 0 ≤ CX := (abs_nonneg _).trans (hCX 0)
    refine Integrable.of_bound ((hX i).1.mul (hMc i)).aestronglyMeasurable (CX * CY)
      (ae_of_all _ fun z => ?_)
    rw [norm_mul]
    refine mul_le_mul ?_ (mehlerI_norm_le hCY a z) (norm_nonneg _) hCX0
    exact (Real.norm_eq_abs _).trans_le (hCX z)
  rw [← integral_finsetSum _ (fun i _ => hint i)]
  refine integral_nonneg fun z => ?_
  have hYint : ∀ i : Fin k, Integrable (fun w => fderiv ℝ (fun z => g (A z))
      (Real.cos a • z + Real.sin a • w) (EuclideanSpace.single i (1 : ℝ)))
      (stdGaussian (EuclideanSpace ℝ (Fin k))) := by
    intro i
    obtain ⟨CY, hCY⟩ := (hY i).2
    exact mehlerI_integrable_comp (hY i).1 CY (fun x => by simpa [Real.norm_eq_abs] using hCY x)
      (Real.cos a • z) (Real.sin a)
  have hcongr : ∀ i : Fin k, fderiv ℝ (fun z => f (A z)) z (EuclideanSpace.single i (1 : ℝ)) *
      (∫ w, fderiv ℝ (fun z => g (A z)) (Real.cos a • z + Real.sin a • w)
        (EuclideanSpace.single i (1 : ℝ)) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
      = ∫ w, fderiv ℝ (fun z => f (A z)) z (EuclideanSpace.single i (1 : ℝ)) *
        fderiv ℝ (fun z => g (A z)) (Real.cos a • z + Real.sin a • w)
          (EuclideanSpace.single i (1 : ℝ)) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) :=
    fun i => (integral_const_mul _ _).symm
  show 0 ≤ ∑ i : Fin k, _
  simp_rw [hcongr]
  rw [← integral_finsetSum _ (fun i _ => (hYint i).const_mul _)]
  refine integral_nonneg fun w => ?_
  show 0 ≤ ∑ i : Fin k, _
  simp only [pitt_fderiv_comp_clm A hfd, pitt_fderiv_comp_clm A hgd]
  exact hpt _ _

/-! ### The theorem -/

/-- **Pitt's association theorem for smooth bounded nondecreasing functions**, given the
covariance representation `PittCovRep k` for the standard Gaussian. -/
theorem pitt_smooth (k : ℕ) (hcov : PittCovRep k) : PittSmoothStmt k := by
  intro S hS hS0 f g hf hg hfm hgm
  set A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) with hA
  have hmap : multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) S
      = (stdGaussian (EuclideanSpace ℝ (Fin k))).map A := by
    simp [multivariateGaussian, hA]
  have hAm : AEMeasurable A (stdGaussian (EuclideanSpace ℝ (Fin k))) :=
    A.continuous.measurable.aemeasurable
  have hfc : Continuous f := hf.1.continuous
  have hgc : Continuous g := hg.1.continuous
  have hfd : Differentiable ℝ f := hf.1.differentiable (by norm_num)
  have hgd : Differentiable ℝ g := hg.1.differentiable (by norm_num)
  have h1 : ∫ x, f x ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) S)
      = ∫ z, f (A z) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) := by
    rw [hmap]; exact integral_map hAm hfc.aestronglyMeasurable
  have h2 : ∫ x, g x ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) S)
      = ∫ z, g (A z) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) := by
    rw [hmap]; exact integral_map hAm hgc.aestronglyMeasurable
  have h3 : ∫ x, f x * g x ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) S)
      = ∫ z, f (A z) * g (A z) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) := by
    rw [hmap]; exact integral_map hAm (hfc.mul hgc).aestronglyMeasurable
  rw [h1, h2, h3]
  have hcov' := hcov (fun z => f (A z)) (fun z => g (A z)) (pitt_comp_clm_C2b A hf).c1b
    (pitt_comp_clm_C2b A hg)
  have hnn : 0 ≤ ∫ z, f (A z) * g (A z) ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))
      - (∫ z, f (A z) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
        * (∫ z, g (A z) ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) := by
    rw [hcov']
    refine setIntegral_nonneg measurableSet_Ioo fun a ha => mul_nonneg ?_ ?_
    · exact Real.sin_nonneg_of_nonneg_of_le_pi ha.1.le (by linarith [Real.pi_pos, ha.2])
    · exact pitt_inner_nonneg A hf hg
        (fun u u' => pitt_sum_nonneg hS hS0 hfm hgm hfd hgd u u') a
  linarith

end LatticeProb
