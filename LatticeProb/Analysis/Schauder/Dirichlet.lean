import LatticeProb.Analysis.NegSobolev
import LatticeProb.Analysis.Schauder.ChainDeriv
import LatticeProb.Analysis.Schauder.ContinuumC2Free
import LatticeProb.Analysis.Schauder.DirichletInverse
import LatticeProb.Analysis.Schauder.HessianBound

/-!
# The interior Schauder estimate for the Dirichlet inverse

`SchauderInteriorDirichlet` is the interior Schauder estimate (Gilbarg–Trudinger, §4.3) in the form
used for the Dirichlet inverse `u = (−DΔ_Q)⁻¹ f` on the unit cube `Q`: for a test function `f` on `Q`,
`u` is `C⁴` on `Q`, and its derivatives of order at most `4` are bounded on `Q` by `C D⁻¹ ‖f‖_{C³}`.

The statement is that of the Vertex-Reinforced-Walk-Homogenization development
(`VRW/External/SchauderInterior.lean`), with its objects replaced by the definitions of
`LatticeProb.Analysis.Schauder.Continuum`. The proof follows `VRW/External/SchauderInteriorProved.lean`,
with the lemmas of the Lattice-High-Contrast-Homogenization development it uses ported into this
namespace.
-/

open MeasureTheory LatticeProb
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb.Analysis.Schauder

variable {d : ℕ}


/-- The operator norm of a continuous `k`-multilinear form on `ℝ^d` is at most the sum of the
absolute values of its values on the standard basis tuples. -/
private theorem norm_le_sum_basis (k : ℕ)
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin k => Euc d) ℝ) :
    ‖M‖ ≤ ∑ m : Fin k → Fin d,
      |M (fun j => (EuclideanSpace.single (m j) (1 : ℝ) : Euc d))| := by
  refine ContinuousMultilinearMap.opNorm_le_bound
    (Finset.sum_nonneg fun _ _ => abs_nonneg _) fun x => ?_
  have hx : x = fun j => ∑ i : Fin d, x j i • (EuclideanSpace.single i (1 : ℝ) : Euc d) :=
    funext fun j => LatticeProb.Analysis.Schauder.euc_eq_sum_smul_single (x j)
  conv_lhs => rw [hx]
  rw [ContinuousMultilinearMap.map_sum]
  calc ‖∑ m : Fin k → Fin d,
        M (fun j => x j (m j) • (EuclideanSpace.single (m j) (1 : ℝ) : Euc d))‖
      ≤ ∑ m : Fin k → Fin d,
          ‖M (fun j => x j (m j) • (EuclideanSpace.single (m j) (1 : ℝ) : Euc d))‖ :=
        norm_sum_le _ _
    _ = ∑ m : Fin k → Fin d,
          (∏ j, |x j (m j)|) *
            ‖M (fun j => (EuclideanSpace.single (m j) (1 : ℝ) : Euc d))‖ := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [ContinuousMultilinearMap.map_smul_univ, norm_smul, Real.norm_eq_abs, Finset.abs_prod]
    _ ≤ ∑ m : Fin k → Fin d,
          (∏ _j : Fin k, ‖x _j‖) *
            |M (fun j => (EuclideanSpace.single (m j) (1 : ℝ) : Euc d))| := by
        refine Finset.sum_le_sum fun m _ => ?_
        refine mul_le_mul ?_ le_rfl (abs_nonneg _) (by positivity)
        exact Finset.prod_le_prod₀ (fun j _ => abs_nonneg _)
          (fun j _ => PiLp.norm_apply_le (x j) (m j))
    _ = (∑ m : Fin k → Fin d,
          |M (fun j => (EuclideanSpace.single (m j) (1 : ℝ) : Euc d))|) *
          (∏ _j : Fin k, ‖x _j‖) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun m _ => mul_comm _ _

/-- `Δ(∂_e u) = ∂_e(Δu)`, expressed through `sineSum f`. -/
private theorem laplacianSum_dirDeriv_dirichletInverse (hd : 1 ≤ d) {D : ℝ} (hD : 0 < D)
    (f : Euc d → ℝ) (hf : LatticeProb.NegSobolev.IsTestFn (unitCube d) f) (e : Euc d) :
    laplacianSum (dirDeriv e (LatticeProb.Analysis.Schauder.dirichletInverse D f)) =
      fun y => (-(1 / D)) * fderiv ℝ (LatticeProb.Analysis.Schauder.sineSum f) y e := by
  set u := LatticeProb.Analysis.Schauder.dirichletInverse D f with hu
  have hcd : ContDiff ℝ (⊤ : ℕ∞) u := LatticeProb.Analysis.Schauder.contDiff_dirichletInverse hd hD f hf
  have hu3 : ContDiff ℝ 3 u := hcd.of_le (WithTop.coe_le_coe.mpr (by norm_num : (3 : ℕ∞) ≤ ⊤))
  have hu2 : ContDiff ℝ 2 (dirDeriv e u) :=
    contDiff_dirDeriv_of_contDiff (hu3.of_le (by norm_num)) e
  have hcomm : laplacianSum (dirDeriv e u) = dirDeriv e (laplacianSum u) := by
    funext y
    rw [LatticeProb.Analysis.Schauder.laplacianSum_eq_sum_dirDeriv_of_contDiff hu2 y,
      LatticeProb.Analysis.Schauder.dirDeriv_laplacianSum hu3 e y]
  rw [hcomm]
  have hlapu : laplacianSum u = fun x => (-(1 / D)) * LatticeProb.Analysis.Schauder.sineSum f x := by
    funext x
    rw [LatticeProb.Analysis.Schauder.laplacianSum_dirichletInverse_eq hd hD f hf x]
    ring
  rw [hlapu]
  funext y
  simp only [dirDeriv]
  rw [fderiv_const_mul ((LatticeProb.Analysis.Schauder.contDiff_sineSum hd f hf).differentiable (by simp) y)]
  rfl

/-- A global gradient bound for the Laplacian of `∂_e u`. -/
private theorem norm_fderiv_laplacianSum_dirDeriv_le (hd : 1 ≤ d) {D : ℝ} (hD : 0 < D)
    (f : Euc d → ℝ) (hf : LatticeProb.NegSobolev.IsTestFn (unitCube d) f) (e y : Euc d) :
    ‖fderiv ℝ (laplacianSum (dirDeriv e (LatticeProb.Analysis.Schauder.dirichletInverse D f))) y‖ ≤
      c3Norm f / D * ‖e‖ := by
  rw [laplacianSum_dirDeriv_dirichletInverse hd hD f hf e]
  have hsine2 : ContDiff ℝ 2 (LatticeProb.Analysis.Schauder.sineSum f) :=
    (LatticeProb.Analysis.Schauder.contDiff_sineSum hd f hf).of_le
      (WithTop.coe_le_coe.mpr (by norm_num : (2 : ℕ∞) ≤ ⊤))
  have hg : ContDiff ℝ 1 (fun y : Euc d => (fderiv ℝ (LatticeProb.Analysis.Schauder.sineSum f) y) e) :=
    contDiff_dirDeriv_of_contDiff hsine2 e
  rw [fderiv_const_mul (hg.differentiable (by norm_num) y)]
  rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (one_div_pos.2 hD), one_div]
  rw [show (c3Norm f / D) * ‖e‖ = D⁻¹ * (c3Norm f * ‖e‖) by ring]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hD.le)
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg ((abs_nonneg _).trans (LatticeProb.Analysis.Schauder.abs_le_c3Norm hf 0)) (norm_nonneg e))
    fun b => ?_
  have hgd : (fderiv ℝ (fun y : Euc d => (fderiv ℝ (LatticeProb.Analysis.Schauder.sineSum f) y) e) y) b =
      dirDeriv b (dirDeriv e (LatticeProb.Analysis.Schauder.sineSum f)) y := rfl
  rw [hgd]
  have h2 := LatticeProb.Analysis.Schauder.abs_dirDeriv_two_le
    (f := LatticeProb.Analysis.Schauder.sineSum f) hsine2 y b e
  have h3 : ‖iteratedFDeriv ℝ 2 (LatticeProb.Analysis.Schauder.sineSum f) y‖ ≤ c3Norm f :=
    (LatticeProb.Analysis.Schauder.sineSum_spec hd 1 one_pos f hf).2.2 2 (by norm_num) y
  calc ‖dirDeriv b (dirDeriv e (LatticeProb.Analysis.Schauder.sineSum f)) y‖
      = |dirDeriv b (dirDeriv e (LatticeProb.Analysis.Schauder.sineSum f)) y| := by rw [Real.norm_eq_abs]
    _ ≤ ‖iteratedFDeriv ℝ 2 (LatticeProb.Analysis.Schauder.sineSum f) y‖ * (‖b‖ * ‖e‖) := h2
    _ ≤ c3Norm f * (‖b‖ * ‖e‖) :=
        mul_le_mul_of_nonneg_right h3 (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = c3Norm f * ‖e‖ * ‖b‖ := by ring

/-- **Order `3`, per direction** (SIBLING-REPO (LHC `b23f694`), heat-semigroup route). -/
theorem exists_norm_iteratedFDeriv_two_dirDeriv_le (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {D : ℝ}, 0 < D → ∀ (f : Euc d → ℝ),
      LatticeProb.NegSobolev.IsTestFn (unitCube d) f → ∀ (e z : Euc d),
        ‖iteratedFDeriv ℝ 2 (dirDeriv e (LatticeProb.Analysis.Schauder.dirichletInverse D f)) z‖ ≤
          C * c3Norm f / D * ‖e‖ := by
  obtain ⟨C₁, hC₁nn, hC₁⟩ :=
    LatticeProb.Analysis.Schauder.exists_norm_iteratedFDeriv_dirichletInverse_le_two_free (d := d) hd
  obtain ⟨K, hKnn, hK⟩ := LatticeProb.Analysis.Schauder.exists_norm_iteratedFDeriv_two_le_of_bounded (d := d)
  refine ⟨K * (C₁ + 1), by positivity, ?_⟩
  intro D hD f hf e z
  set u := LatticeProb.Analysis.Schauder.dirichletInverse D f with hu
  have hcd : ContDiff ℝ (⊤ : ℕ∞) u := LatticeProb.Analysis.Schauder.contDiff_dirichletInverse hd hD f hf
  have hbdU : BoundedDerivs 5 u :=
    ⟨hcd.of_le (WithTop.coe_le_coe.mpr (by norm_num : (5 : ℕ∞) ≤ ⊤)),
      fun k _ => LatticeProb.Analysis.Schauder.exists_bound_iteratedFDeriv_dirichletInverse hd hD f hf k⟩
  have hbd : BoundedDerivs 4 (dirDeriv e u) := hbdU.dirDeriv e
  have hc3 : 0 ≤ c3Norm f := (abs_nonneg _).trans (LatticeProb.Analysis.Schauder.abs_le_c3Norm hf 0)
  have hA : ∀ y, |dirDeriv e u y| ≤ (C₁ * c3Norm f / D) * ‖e‖ := fun y => by
    have h1 := (hC₁ D hD f hf y).2.1
    calc |dirDeriv e u y| = ‖fderiv ℝ u y e‖ := rfl
      _ ≤ ‖fderiv ℝ u y‖ * ‖e‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (C₁ * c3Norm f / D) * ‖e‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg e)
  have hB : ∀ y, ‖fderiv ℝ (laplacianSum (dirDeriv e u)) y‖ ≤ (c3Norm f / D) * ‖e‖ :=
    fun y => norm_fderiv_laplacianSum_dirDeriv_le hd hD f hf e y
  have h := hK (dirDeriv e u) ((C₁ * c3Norm f / D) * ‖e‖) ((c3Norm f / D) * ‖e‖) hbd hA hB z
  calc ‖iteratedFDeriv ℝ 2 (dirDeriv e u) z‖
      ≤ K * (((C₁ * c3Norm f / D) * ‖e‖) + ((c3Norm f / D) * ‖e‖)) := h
    _ = K * (C₁ + 1) * c3Norm f / D * ‖e‖ := by ring



/-- **Order `3`, operator norm**: assemble the per-direction bounds over the standard basis
tuples. -/
theorem exists_norm_iteratedFDeriv_three_le (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {D : ℝ}, 0 < D → ∀ (f : Euc d → ℝ),
      LatticeProb.NegSobolev.IsTestFn (unitCube d) f → ∀ z : Euc d,
        ‖iteratedFDeriv ℝ 3 (LatticeProb.Analysis.Schauder.dirichletInverse D f) z‖ ≤ C * c3Norm f / D := by
  obtain ⟨C₃, hC₃nn, hC₃⟩ := exists_norm_iteratedFDeriv_two_dirDeriv_le (d := d) hd
  refine ⟨(d : ℝ) ^ 3 * C₃, by positivity, ?_⟩
  intro D hD f hf z
  set u := LatticeProb.Analysis.Schauder.dirichletInverse D f with hu
  have hu3 : ContDiff ℝ 3 u :=
    (LatticeProb.Analysis.Schauder.contDiff_dirichletInverse hd hD f hf).of_le
      (WithTop.coe_le_coe.mpr (by norm_num : (3 : ℕ∞) ≤ ⊤))
  have hc3 : 0 ≤ c3Norm f := (abs_nonneg _).trans (LatticeProb.Analysis.Schauder.abs_le_c3Norm hf 0)
  calc ‖iteratedFDeriv ℝ 3 u z‖
      ≤ ∑ m : Fin 3 → Fin d,
          |iteratedFDeriv ℝ 3 u z (fun j => (EuclideanSpace.single (m j) (1 : ℝ) : Euc d))| :=
        norm_le_sum_basis 3 _
    _ ≤ ∑ m : Fin 3 → Fin d,
          ‖iteratedFDeriv ℝ 2 (dirDeriv (EuclideanSpace.single (m 2) (1 : ℝ)) u) z‖ := by
        refine Finset.sum_le_sum fun m _ => ?_
        have hm : (fun j : Fin 3 => (EuclideanSpace.single (m j) (1 : ℝ) : Euc d)) =
            ![EuclideanSpace.single (m 0) 1, EuclideanSpace.single (m 1) 1,
              EuclideanSpace.single (m 2) 1] := by
          funext j; fin_cases j <;> rfl
        have hinit : Fin.init ![EuclideanSpace.single (m 0) (1 : ℝ), EuclideanSpace.single (m 1) 1,
              EuclideanSpace.single (m 2) 1] =
            ![EuclideanSpace.single (m 0) (1 : ℝ), EuclideanSpace.single (m 1) 1] := by
          funext j; fin_cases j <;> rfl
        rw [hm, LatticeProb.Analysis.Schauder.iteratedFDeriv_succ_apply_eq_dirDeriv hu3 z
          ![EuclideanSpace.single (m 0) 1, EuclideanSpace.single (m 1) 1,
            EuclideanSpace.single (m 2) 1], hinit]
        have h := (iteratedFDeriv ℝ 2
          (dirDeriv (EuclideanSpace.single (m 2) (1 : ℝ)) u) z).le_opNorm
          ![EuclideanSpace.single (m 0) (1 : ℝ), EuclideanSpace.single (m 1) (1 : ℝ)]
        rw [Fin.prod_univ_two] at h
        simpa using h
    _ ≤ ∑ _m : Fin 3 → Fin d, C₃ * c3Norm f / D := by
        refine Finset.sum_le_sum fun m _ => ?_
        simpa using hC₃ hD f hf (EuclideanSpace.single (m 2) (1 : ℝ)) z
    _ = ((d : ℝ) ^ 3 * C₃) * c3Norm f / D := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
        ring



/-- `Δ(∂_e g) = ∂_e(Δg)` for a `C³` function. -/
private theorem laplacianSum_dirDeriv_eq {g : Euc d → ℝ} (hg3 : ContDiff ℝ 3 g) (e : Euc d) :
    laplacianSum (dirDeriv e g) = dirDeriv e (laplacianSum g) := by
  funext y
  rw [LatticeProb.Analysis.Schauder.laplacianSum_eq_sum_dirDeriv_of_contDiff
      (contDiff_dirDeriv_of_contDiff (hg3.of_le (by norm_num)) e) y,
    LatticeProb.Analysis.Schauder.dirDeriv_laplacianSum hg3 e y]

/-- `∂_e(c g) = c ∂_e g`. -/
private theorem dirDeriv_const_mul (c : ℝ) (g : Euc d → ℝ) (e : Euc d)
    (hg : Differentiable ℝ g) : dirDeriv e (fun y => c * g y) = fun y => c * dirDeriv e g y := by
  funext y
  simp only [dirDeriv]
  rw [fderiv_const_mul (hg.differentiableAt) c]
  rfl

/-- `Δ(∂_e∂_{e'} u) = -(1/D) ∂_e∂_{e'} sineSum f`. -/
private theorem laplacianSum_dirDeriv_dirDeriv_dirichletInverse (hd : 1 ≤ d) {D : ℝ} (hD : 0 < D)
    (f : Euc d → ℝ) (hf : LatticeProb.NegSobolev.IsTestFn (unitCube d) f) (e e' : Euc d) :
    laplacianSum (dirDeriv e (dirDeriv e' (LatticeProb.Analysis.Schauder.dirichletInverse D f))) =
      fun y => (-(1 / D)) * dirDeriv e (dirDeriv e' (LatticeProb.Analysis.Schauder.sineSum f)) y := by
  set u := LatticeProb.Analysis.Schauder.dirichletInverse D f with hu
  have hcd : ContDiff ℝ (⊤ : ℕ∞) u := LatticeProb.Analysis.Schauder.contDiff_dirichletInverse hd hD f hf
  have hu4 : ContDiff ℝ 4 u := hcd.of_le (WithTop.coe_le_coe.mpr (by norm_num : (4 : ℕ∞) ≤ ⊤))
  have hu3 : ContDiff ℝ 3 u := hu4.of_le (by norm_num)
  have hde' : ContDiff ℝ 3 (dirDeriv e' u) :=
    contDiff_dirDeriv_of_contDiff hu4 e'
  rw [laplacianSum_dirDeriv_eq hde' e]
  rw [laplacianSum_dirDeriv_eq hu3 e']
  have hlapu : laplacianSum u = fun x => (-(1 / D)) * LatticeProb.Analysis.Schauder.sineSum f x := by
    funext x
    rw [LatticeProb.Analysis.Schauder.laplacianSum_dirichletInverse_eq hd hD f hf x]
    ring
  rw [hlapu]
  rw [dirDeriv_const_mul (-(1 / D)) (LatticeProb.Analysis.Schauder.sineSum f) e'
    ((LatticeProb.Analysis.Schauder.contDiff_sineSum hd f hf).differentiable (by simp))]
  rw [dirDeriv_const_mul (-(1 / D))
    (dirDeriv e' (LatticeProb.Analysis.Schauder.sineSum f)) e
    ((contDiff_dirDeriv_of_contDiff
      ((LatticeProb.Analysis.Schauder.contDiff_sineSum hd f hf).of_le
        (WithTop.coe_le_coe.mpr (by norm_num : (2 : ℕ∞) ≤ ⊤))) e').differentiable (by norm_num))]

/-- A global gradient bound for the Laplacian of `∂_e∂_{e'} u`. -/
private theorem norm_fderiv_laplacianSum_dirDeriv_dirDeriv_le (hd : 1 ≤ d) {D : ℝ} (hD : 0 < D)
    (f : Euc d → ℝ) (hf : LatticeProb.NegSobolev.IsTestFn (unitCube d) f) (e e' y : Euc d) :
    ‖fderiv ℝ (laplacianSum (dirDeriv e (dirDeriv e' (LatticeProb.Analysis.Schauder.dirichletInverse D f)))) y‖ ≤
      c3Norm f / D * ‖e‖ * ‖e'‖ := by
  rw [laplacianSum_dirDeriv_dirDeriv_dirichletInverse hd hD f hf e e']
  have hsine3 : ContDiff ℝ 3 (LatticeProb.Analysis.Schauder.sineSum f) :=
    (LatticeProb.Analysis.Schauder.contDiff_sineSum hd f hf).of_le
      (WithTop.coe_le_coe.mpr (by norm_num : (3 : ℕ∞) ≤ ⊤))
  have hg : Differentiable ℝ (fun y : Euc d => dirDeriv e (dirDeriv e' (LatticeProb.Analysis.Schauder.sineSum f)) y) :=
    ((contDiff_dirDeriv_of_contDiff (contDiff_dirDeriv_of_contDiff hsine3 e') e).differentiable
      (by norm_num))
  rw [fderiv_const_mul (hg.differentiableAt) (-(1 / D))]
  rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (one_div_pos.2 hD), one_div]
  rw [show (c3Norm f / D) * ‖e‖ * ‖e'‖ = D⁻¹ * (c3Norm f * ‖e‖ * ‖e'‖) by ring]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hD.le)
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg ((abs_nonneg _).trans (LatticeProb.Analysis.Schauder.abs_le_c3Norm hf 0))
      (norm_nonneg e)) (norm_nonneg e')) fun b => ?_
  have hgd : (fderiv ℝ (fun y : Euc d => dirDeriv e (dirDeriv e' (LatticeProb.Analysis.Schauder.sineSum f)) y) y) b =
      dirDeriv b (dirDeriv e (dirDeriv e' (LatticeProb.Analysis.Schauder.sineSum f))) y := rfl
  rw [hgd]
  have h2 := LatticeProb.Analysis.Schauder.abs_dirDeriv_three_le (f := LatticeProb.Analysis.Schauder.sineSum f) hsine3 y b e e'
  have h3 : ‖iteratedFDeriv ℝ 3 (LatticeProb.Analysis.Schauder.sineSum f) y‖ ≤ c3Norm f :=
    (LatticeProb.Analysis.Schauder.sineSum_spec hd 1 one_pos f hf).2.2 3 (by norm_num) y
  calc ‖dirDeriv b (dirDeriv e (dirDeriv e' (LatticeProb.Analysis.Schauder.sineSum f))) y‖
      = |dirDeriv b (dirDeriv e (dirDeriv e' (LatticeProb.Analysis.Schauder.sineSum f))) y| := by rw [Real.norm_eq_abs]
    _ ≤ ‖iteratedFDeriv ℝ 3 (LatticeProb.Analysis.Schauder.sineSum f) y‖ * (‖b‖ * ‖e‖ * ‖e'‖) := h2
    _ ≤ c3Norm f * (‖b‖ * ‖e‖ * ‖e'‖) :=
        mul_le_mul_of_nonneg_right h3
          (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _))
    _ = c3Norm f * ‖e‖ * ‖e'‖ * ‖b‖ := by ring

/-- **Order `4`, per direction** (SIBLING-REPO (LHC `b23f694`), heat-semigroup route). -/
theorem exists_norm_iteratedFDeriv_two_dirDeriv_dirDeriv_le (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {D : ℝ}, 0 < D → ∀ (f : Euc d → ℝ),
      LatticeProb.NegSobolev.IsTestFn (unitCube d) f → ∀ (e e' z : Euc d),
        ‖iteratedFDeriv ℝ 2 (dirDeriv e (dirDeriv e' (LatticeProb.Analysis.Schauder.dirichletInverse D f))) z‖ ≤
          C * c3Norm f / D * ‖e‖ * ‖e'‖ := by
  obtain ⟨C₂, hC₂nn, hC₂⟩ :=
    LatticeProb.Analysis.Schauder.exists_norm_iteratedFDeriv_dirichletInverse_le_two_free (d := d) hd
  obtain ⟨K, hKnn, hK⟩ := LatticeProb.Analysis.Schauder.exists_norm_iteratedFDeriv_two_le_of_bounded (d := d)
  refine ⟨K * (C₂ + 1), by positivity, ?_⟩
  intro D hD f hf e e' z
  set u := LatticeProb.Analysis.Schauder.dirichletInverse D f with hu
  have hcd : ContDiff ℝ (⊤ : ℕ∞) u := LatticeProb.Analysis.Schauder.contDiff_dirichletInverse hd hD f hf
  have hbdU : BoundedDerivs 6 u :=
    ⟨hcd.of_le (WithTop.coe_le_coe.mpr (by norm_num : (6 : ℕ∞) ≤ ⊤)),
      fun k _ => LatticeProb.Analysis.Schauder.exists_bound_iteratedFDeriv_dirichletInverse hd hD f hf k⟩
  have hbd : BoundedDerivs 4 (dirDeriv e (dirDeriv e' u)) := (hbdU.dirDeriv e').dirDeriv e
  have hA : ∀ y, |dirDeriv e (dirDeriv e' u) y| ≤ (C₂ * c3Norm f / D) * ‖e‖ * ‖e'‖ := fun y => by
    have h1 := (hC₂ D hD f hf y).2.2
    have hg2 : ContDiff ℝ 2 u := hcd.of_le (WithTop.coe_le_coe.mpr (by norm_num : (2 : ℕ∞) ≤ ⊤))
    have h2 := LatticeProb.Analysis.Schauder.abs_dirDeriv_two_le (f := u) hg2 y e e'
    calc |dirDeriv e (dirDeriv e' u) y|
        ≤ ‖iteratedFDeriv ℝ 2 u y‖ * (‖e‖ * ‖e'‖) := h2
      _ ≤ (C₂ * c3Norm f / D) * (‖e‖ * ‖e'‖) :=
          mul_le_mul_of_nonneg_right h1 (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = (C₂ * c3Norm f / D) * ‖e‖ * ‖e'‖ := by ring
  have hB : ∀ y, ‖fderiv ℝ (laplacianSum (dirDeriv e (dirDeriv e' u))) y‖ ≤
      (c3Norm f / D) * ‖e‖ * ‖e'‖ :=
    fun y => norm_fderiv_laplacianSum_dirDeriv_dirDeriv_le hd hD f hf e e' y
  have h := hK (dirDeriv e (dirDeriv e' u)) ((C₂ * c3Norm f / D) * ‖e‖ * ‖e'‖)
    ((c3Norm f / D) * ‖e‖ * ‖e'‖) hbd hA hB z
  calc ‖iteratedFDeriv ℝ 2 (dirDeriv e (dirDeriv e' u)) z‖
      ≤ K * (((C₂ * c3Norm f / D) * ‖e‖ * ‖e'‖) + ((c3Norm f / D) * ‖e‖ * ‖e'‖)) := h
    _ = K * (C₂ + 1) * c3Norm f / D * ‖e‖ * ‖e'‖ := by ring



/-- **Order `4`, operator norm**. -/
theorem exists_norm_iteratedFDeriv_four_le (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {D : ℝ}, 0 < D → ∀ (f : Euc d → ℝ),
      LatticeProb.NegSobolev.IsTestFn (unitCube d) f → ∀ z : Euc d,
        ‖iteratedFDeriv ℝ 4 (LatticeProb.Analysis.Schauder.dirichletInverse D f) z‖ ≤ C * c3Norm f / D := by
  obtain ⟨C₄, hC₄nn, hC₄⟩ := exists_norm_iteratedFDeriv_two_dirDeriv_dirDeriv_le (d := d) hd
  refine ⟨(d : ℝ) ^ 4 * C₄, by positivity, ?_⟩
  intro D hD f hf z
  set u := LatticeProb.Analysis.Schauder.dirichletInverse D f with hu
  have hu4 : ContDiff ℝ 4 u :=
    (LatticeProb.Analysis.Schauder.contDiff_dirichletInverse hd hD f hf).of_le
      (WithTop.coe_le_coe.mpr (by norm_num : (4 : ℕ∞) ≤ ⊤))
  have hinit3 : ∀ a b c e : Euc d, Fin.init ![a, b, c, e] = ![a, b, c] := by
    intro a b c e; funext j; fin_cases j <;> rfl
  have hinit2 : ∀ a b c : Euc d, Fin.init ![a, b, c] = ![a, b] := by
    intro a b c; funext j; fin_cases j <;> rfl
  calc ‖iteratedFDeriv ℝ 4 u z‖
      ≤ ∑ m : Fin 4 → Fin d,
          |iteratedFDeriv ℝ 4 u z (fun j => (EuclideanSpace.single (m j) (1 : ℝ) : Euc d))| :=
        norm_le_sum_basis 4 _
    _ ≤ ∑ m : Fin 4 → Fin d,
          ‖iteratedFDeriv ℝ 2
            (dirDeriv (EuclideanSpace.single (m 2) (1 : ℝ))
              (dirDeriv (EuclideanSpace.single (m 3) (1 : ℝ)) u)) z‖ := by
        refine Finset.sum_le_sum fun m _ => ?_
        have hm : (fun j : Fin 4 => (EuclideanSpace.single (m j) (1 : ℝ) : Euc d)) =
            ![EuclideanSpace.single (m 0) 1, EuclideanSpace.single (m 1) 1,
              EuclideanSpace.single (m 2) 1, EuclideanSpace.single (m 3) 1] := by
          funext j; fin_cases j <;> rfl
        rw [hm, LatticeProb.Analysis.Schauder.iteratedFDeriv_succ_apply_eq_dirDeriv hu4 z
          ![EuclideanSpace.single (m 0) 1, EuclideanSpace.single (m 1) 1,
            EuclideanSpace.single (m 2) 1, EuclideanSpace.single (m 3) 1]]
        rw [show (![EuclideanSpace.single (m 0) (1 : ℝ), EuclideanSpace.single (m 1) 1,
              EuclideanSpace.single (m 2) 1, EuclideanSpace.single (m 3) 1] : Fin 4 → Euc d)
              (Fin.last 3) = EuclideanSpace.single (m 3) (1 : ℝ) from rfl, hinit3]
        rw [LatticeProb.Analysis.Schauder.iteratedFDeriv_succ_apply_eq_dirDeriv
          (contDiff_dirDeriv_of_contDiff hu4 (EuclideanSpace.single (m 3) (1 : ℝ))) z
          ![EuclideanSpace.single (m 0) 1, EuclideanSpace.single (m 1) 1,
            EuclideanSpace.single (m 2) 1]]
        rw [show (![EuclideanSpace.single (m 0) (1 : ℝ), EuclideanSpace.single (m 1) 1,
              EuclideanSpace.single (m 2) 1] : Fin 3 → Euc d) (Fin.last 2) =
              EuclideanSpace.single (m 2) (1 : ℝ) from rfl, hinit2]
        have h := (iteratedFDeriv ℝ 2
          (dirDeriv (EuclideanSpace.single (m 2) (1 : ℝ))
            (dirDeriv (EuclideanSpace.single (m 3) (1 : ℝ)) u)) z).le_opNorm
          ![EuclideanSpace.single (m 0) (1 : ℝ), EuclideanSpace.single (m 1) (1 : ℝ)]
        rw [Fin.prod_univ_two] at h
        simpa using h
    _ ≤ ∑ _m : Fin 4 → Fin d, C₄ * c3Norm f / D := by
        refine Finset.sum_le_sum fun m _ => ?_
        simpa using hC₄ hD f hf (EuclideanSpace.single (m 2) (1 : ℝ))
          (EuclideanSpace.single (m 3) (1 : ℝ)) z
    _ = ((d : ℝ) ^ 4 * C₄) * c3Norm f / D := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
        ring

/-- The interior Schauder estimate for the Dirichlet inverse on the unit cube: for every dimension
`d ≥ 1` there is a constant `C` such that for every `D > 0` and every test function `f` on the cube,
`(−DΔ_Q)⁻¹ f` is `C⁴` on the cube with `‖D^k (−DΔ_Q)⁻¹ f‖ ≤ C D⁻¹ ‖f‖_{C³}` for `k ≤ 4`. -/
def SchauderInteriorDirichlet : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∃ C : ℝ, ∀ D : ℝ, 0 < D → ∀ f : Euc d → ℝ,
    LatticeProb.NegSobolev.IsTestFn (unitCube d) f →
      ContDiffOn ℝ 4 (dirichletInverse D f) (unitCube d) ∧
        ∀ k : ℕ, k ≤ 4 → ∀ z ∈ unitCube d,
          ‖iteratedFDeriv ℝ k (dirichletInverse D f) z‖ ≤ C / D * c3Norm f

/-- The interior Schauder estimate for the Dirichlet inverse on the unit cube. -/
theorem schauderInteriorDirichlet : SchauderInteriorDirichlet := by
  intro d hd
  obtain ⟨C₂, hC₂nn, hC₂⟩ :=
    LatticeProb.Analysis.Schauder.exists_norm_iteratedFDeriv_dirichletInverse_le_two_free (d := d) hd
  obtain ⟨C₃, hC₃nn, hC₃⟩ := exists_norm_iteratedFDeriv_three_le (d := d) hd
  obtain ⟨C₄, hC₄nn, hC₄⟩ := exists_norm_iteratedFDeriv_four_le (d := d) hd
  refine ⟨max (max C₂ C₃) C₄, ?_⟩
  change ∀ D : ℝ, 0 < D → ∀ f : LatticeProb.Analysis.Schauder.Euc d → ℝ,
    LatticeProb.NegSobolev.IsTestFn (LatticeProb.Analysis.Schauder.unitCube d) f →
      ContDiffOn ℝ 4 (LatticeProb.Analysis.Schauder.dirichletInverse D f) (LatticeProb.Analysis.Schauder.unitCube d) ∧
        ∀ k : ℕ, k ≤ 4 → ∀ z ∈ LatticeProb.Analysis.Schauder.unitCube d,
          ‖iteratedFDeriv ℝ k (LatticeProb.Analysis.Schauder.dirichletInverse D f) z‖ ≤
            max (max C₂ C₃) C₄ / D * LatticeProb.Analysis.Schauder.c3Norm f
  intro D hD f hf
  have hc3 : 0 ≤ LatticeProb.Analysis.Schauder.c3Norm f := (abs_nonneg _).trans (LatticeProb.Analysis.Schauder.abs_le_c3Norm hf 0)
  have hle : ∀ C : ℝ, C ≤ max (max C₂ C₃) C₄ →
      C * LatticeProb.Analysis.Schauder.c3Norm f / D ≤ max (max C₂ C₃) C₄ / D * LatticeProb.Analysis.Schauder.c3Norm f := by
    intro C hC
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC hc3) hD.le
  refine ⟨?_, fun k hk z hz => ?_⟩
  · exact ((LatticeProb.Analysis.Schauder.contDiff_dirichletInverse hd hD f hf).of_le
      (WithTop.coe_le_coe.mpr le_top)).contDiffOn
  · interval_cases k
    · rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
      exact (hC₂ D hD f hf z).1.trans (hle C₂ (le_trans (le_max_left _ _) (le_max_left _ _)))
    · rw [norm_iteratedFDeriv_one]
      exact (hC₂ D hD f hf z).2.1.trans (hle C₂ (le_trans (le_max_left _ _) (le_max_left _ _)))
    · exact (hC₂ D hD f hf z).2.2.trans (hle C₂ (le_trans (le_max_left _ _) (le_max_left _ _)))
    · exact (hC₃ hD f hf z).trans (hle C₃ (le_trans (le_max_right _ _) (le_max_left _ _)))
    · exact (hC₄ hD f hf z).trans (hle C₄ (le_max_right _ _))

end LatticeProb.Analysis.Schauder
