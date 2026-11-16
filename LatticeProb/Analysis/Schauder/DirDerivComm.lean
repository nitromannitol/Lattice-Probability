import LatticeProb.Analysis.Schauder.SineCoeff

/-!
# Directional derivatives at finite smoothness

The derivative bookkeeping for the heat-semigroup proof of the Hessian bound that replaces the
interior Schauder estimate. The functions there are only `C⁴`, so the identities of the module
`LatticeProb.Analysis.Schauder.SineCoeff` (proved for `C^∞` functions) are re-proved here at the
smoothness they actually need: a Hessian entry is a nested directional derivative, directional
derivatives of a `C²` function commute, the Laplacian of a `C²` function is the sum of its pure
second directional derivatives, and a directional derivative of the Laplacian of a `C³` function is
the Laplacian of the directional derivative.
-/

namespace LatticeProb.Analysis.Schauder

noncomputable section

variable {d : ℕ}

/-- A directional derivative of a `C^{n+1}` function is `Cⁿ`. -/
theorem contDiff_dirDeriv_of_contDiff {f : Euc d → ℝ} {n : ℕ} (hf : ContDiff ℝ (n + 1) f)
    (e : Euc d) : ContDiff ℝ n (dirDeriv e f) :=
  (hf.fderiv_right le_rfl).clm_apply contDiff_const

/-- The nested directional derivative of a `C²` function is the second derivative applied to the
two directions. -/
theorem dirDeriv_dirDeriv_eq_fderiv_fderiv {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f)
    (z a b : Euc d) : dirDeriv a (dirDeriv b f) z = fderiv ℝ (fderiv ℝ f) z a b := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) z :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by simp)) z
  have h1 := fderiv_clm_apply (c := fderiv ℝ f) (u := fun _ => b) hd (differentiableAt_const b)
  unfold dirDeriv
  rw [h1]
  simp

/-- A Hessian entry is a nested directional derivative. -/
theorem iteratedFDeriv_two_apply_eq_dirDeriv {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f)
    (z a b : Euc d) :
    iteratedFDeriv ℝ 2 f z ![a, b] = dirDeriv a (dirDeriv b f) z := by
  rw [iteratedFDeriv_two_apply, dirDeriv_dirDeriv_eq_fderiv_fderiv hf]
  simp

/-- Directional derivatives of a `C²` function commute. -/
theorem dirDeriv_comm {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) (a b : Euc d) :
    dirDeriv a (dirDeriv b f) = dirDeriv b (dirDeriv a f) := by
  funext z
  have hsymm : IsSymmSndFDerivAt ℝ f z :=
    hf.contDiffAt.isSymmSndFDerivAt (by simp)
  rw [dirDeriv_dirDeriv_eq_fderiv_fderiv hf, dirDeriv_dirDeriv_eq_fderiv_fderiv hf]
  exact hsymm.eq a b

/-- The Laplacian of a `C²` function is the sum of its pure second directional derivatives. -/
theorem laplacianSum_eq_sum_dirDeriv_of_contDiff {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f)
    (z : Euc d) :
    laplacianSum f z =
      ∑ i, dirDeriv (EuclideanSpace.single i 1) (dirDeriv (EuclideanSpace.single i 1) f) z := by
  unfold laplacianSum
  exact Finset.sum_congr rfl fun i _ => iteratedFDeriv_two_apply_eq_dirDeriv hf z _ _

/-- A directional derivative of the Laplacian of a `C³` function is the Laplacian of the
directional derivative. -/
theorem dirDeriv_laplacianSum {f : Euc d → ℝ} (hf : ContDiff ℝ 3 f) (w z : Euc d) :
    dirDeriv w (laplacianSum f) z =
      ∑ i, dirDeriv (EuclideanSpace.single i 1)
        (dirDeriv (EuclideanSpace.single i 1) (dirDeriv w f)) z := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hf3 : ContDiff ℝ ((2 : ℕ) + 1) f := by exact_mod_cast hf
  have hfun : laplacianSum f = fun y =>
      ∑ i, dirDeriv (EuclideanSpace.single i 1) (dirDeriv (EuclideanSpace.single i 1) f) y :=
    funext fun y => laplacianSum_eq_sum_dirDeriv_of_contDiff hf2 y
  have hdiff : ∀ i ∈ (Finset.univ : Finset (Fin d)), DifferentiableAt ℝ
      (dirDeriv (EuclideanSpace.single i 1) (dirDeriv (EuclideanSpace.single i 1) f)) z := by
    intro i _
    have h2 : ContDiff ℝ ((1 : ℕ) + 1)
        (dirDeriv (EuclideanSpace.single i 1) f) := by
      exact_mod_cast contDiff_dirDeriv_of_contDiff hf3 (EuclideanSpace.single i 1)
    have h1 := contDiff_dirDeriv_of_contDiff h2 (EuclideanSpace.single i 1)
    exact (h1.differentiable (by simp)) z
  rw [show dirDeriv w (laplacianSum f) z = fderiv ℝ (laplacianSum f) z w from rfl, hfun,
    fderiv_fun_sum hdiff, sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hg : ContDiff ℝ 2 (dirDeriv (EuclideanSpace.single i 1) f) := by
    exact_mod_cast contDiff_dirDeriv_of_contDiff hf3 (EuclideanSpace.single i 1)
  have hc1 := dirDeriv_comm hg w (EuclideanSpace.single i 1)
  have hc2 := dirDeriv_comm hf2 w (EuclideanSpace.single i 1)
  have h3 : dirDeriv w
      (dirDeriv (EuclideanSpace.single i 1) (dirDeriv (EuclideanSpace.single i 1) f)) =
      dirDeriv (EuclideanSpace.single i 1)
        (dirDeriv (EuclideanSpace.single i 1) (dirDeriv w f)) := by
    rw [hc1, hc2]
  exact congrFun h3 z
