/-
**The finite-dimensional characteristic function of a `d`-dimensional Brownian motion, at a
general linear combination over coordinates and times.**

This module is stated for `LatticeProb.IsBrownianSpace` alone and mentions no model-specific
object. It supplies the fact that a general linear combination of `d` independent coordinates
of a `LatticeProb.IsBrownianSpace`, evaluated at finitely many times, is Gaussian with a
computable variance, so that its characteristic function can be identified termwise against a
matching discrete finite-dimensional limit (for instance the characteristic function of a
rescaled simple random walk converging to the same exponential).

Route: `IsBrownianSpace.coord ℓ` gives that `√d · B(·)(·)(ℓ)` is a genuine Mathlib
`ProbabilityTheory.IsBrownianReal`, hence (via `IsPreBrownianReal.isGaussianProcess`) a
Gaussian process in the time argument; composing with the evaluation times and rescaling by
the weights via `IsGaussianProcess.comp_right`/`.smul` gives that a finite linear combination
over a fixed coordinate is itself Gaussian (`IsGaussianProcess.hasGaussianLaw_fun_sum`), whose
characteristic function at `1` is read off `HasGaussianLaw.charFun_map_eq` once its mean
(`IsPreBrownianReal.integral_eval`, zero) and variance (a bilinear expansion via
`covariance_fun_sum_fun_sum` against `IsPreBrownianReal.covariance_eval`, `cov[B s, B t] =
min s t`) are computed. `IsBrownianSpace.indep` gives that the `d` coordinate combinations are
themselves independent random variables, so the characteristic function of their sum is the
PRODUCT of the individual ones (`iIndepFun.charFun_map_fun_sum_eq_prod`), which multiplies the
per-coordinate Gaussian exponentials into the stated joint exponential.

Moved from Parking-Sharpness.
-/
import Mathlib
import LatticeProb.Prob.BrownianExit

open MeasureTheory ProbabilityTheory Filter Topology LatticeProb
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace LatticeProb.Scaling.WalkCLT

/-- **The characteristic function, at argument `1`, of a finite linear combination (over both
a finite set of `d` coordinates and a finite set of times) of a `d`-dimensional Brownian
motion on `LatticeProb.IsBrownianSpace`.** General: depends only on the library's Brownian
motion, no model-specific object. -/
theorem charFun_isBrownianSpace_linearCombination
    {d : ℕ} (hd1 : 1 ≤ d)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} (hB : IsBrownianSpace d 0 B P)
    {m : ℕ} (t : Fin m → Fin d → ℝ) (ts : Fin m → ℝ≥0) :
    charFun (P.map (fun ω => ∑ i, ∑ ℓ, t i ℓ * B (ts i) ω ℓ)) 1
      = Complex.exp
          (-((∑ ℓ : Fin d, ∑ i, ∑ i', t i ℓ * t i' ℓ * (min (ts i) (ts i') : ℝ) : ℝ) : ℂ)
            / (2 * d)) := by
  have hdR : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd1)
  have hdR' : Real.sqrt d ≠ 0 := hdR.ne'
  set Bs : Fin d → ℝ≥0 → Ω → ℝ :=
    fun ℓ s ω => Real.sqrt d * (B s ω ℓ - (0 : EuclideanSpace ℝ (Fin d)) ℓ) with hBsdef
  have hBsBrownian : ∀ ℓ, IsBrownianReal (Bs ℓ) P := hB.coord
  have hBseq : ∀ ℓ s ω, Bs ℓ s ω = Real.sqrt d * B s ω ℓ := by
    intro ℓ s ω; simp [hBsdef]
  set Y' : Fin d → Ω → ℝ := fun ℓ ω => ∑ i, t i ℓ * Bs ℓ (ts i) ω with hY'def
  set Y : Fin d → Ω → ℝ := fun ℓ ω => ∑ i, t i ℓ * B (ts i) ω ℓ with hYdef
  have hYeq : ∀ ℓ ω, Y ℓ ω = (1 / Real.sqrt d) * Y' ℓ ω := by
    intro ℓ ω
    simp only [hYdef, hY'def, hBseq]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  -- Gaussian process for `Y'ℓ`
  have hGaussY'proc : ∀ ℓ, IsGaussianProcess (fun (i : Fin m) ω => t i ℓ * Bs ℓ (ts i) ω) P := by
    intro ℓ
    have h1 : IsGaussianProcess (Bs ℓ ∘ ts) P := (hBsBrownian ℓ).isGaussianProcess.comp_right ts
    have h2 := h1.smul (fun i : Fin m => t i ℓ)
    refine h2.congr (fun i => ?_)
    filter_upwards with ω
    show (t i ℓ) • ((Bs ℓ ∘ ts) i ω) = t i ℓ * Bs ℓ (ts i) ω
    simp [smul_eq_mul]
  have hHasGaussY' : ∀ ℓ, HasGaussianLaw (Y' ℓ) P := by
    intro ℓ
    have := (hGaussY'proc ℓ).hasGaussianLaw_fun_sum (I := (Finset.univ : Finset (Fin m)))
    simpa [hY'def] using this
  -- mean of `Y'ℓ`
  have hmeanBs : ∀ ℓ s, P[Bs ℓ s] = 0 := fun ℓ s => (hBsBrownian ℓ).integral_eval s
  have hintBs : ∀ ℓ s, Integrable (Bs ℓ s) P := fun ℓ s => (hBsBrownian ℓ).integrable_eval s
  have hmeanY' : ∀ ℓ, P[Y' ℓ] = 0 := by
    intro ℓ
    have hint : ∀ i : Fin m, Integrable (fun ω => t i ℓ * Bs ℓ (ts i) ω) P := fun i =>
      (hintBs ℓ (ts i)).const_mul _
    show (∫ ω, ∑ i, t i ℓ * Bs ℓ (ts i) ω ∂P) = 0
    rw [integral_finsetSum Finset.univ (fun i _ => hint i)]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [integral_const_mul, hmeanBs ℓ (ts i), mul_zero]
  -- variance of `Y'ℓ`, by bilinear expansion against the covariance of `Bs ℓ`
  have hMemLpBs : ∀ ℓ s, MemLp (Bs ℓ s) 2 P := fun ℓ s =>
    ((hBsBrownian ℓ).isGaussianProcess.hasGaussianLaw_eval s).memLp_two
  have hcovBs : ∀ ℓ s s', cov[Bs ℓ s, Bs ℓ s'; P] = (min s s' : ℝ) := fun ℓ s s' =>
    (hBsBrownian ℓ).covariance_eval s s'
  have hvarY' : ∀ ℓ, Var[Y' ℓ; P] = ∑ i, ∑ i', t i ℓ * t i' ℓ * (min (ts i) (ts i') : ℝ) := by
    intro ℓ
    have hmemX : ∀ i : Fin m, MemLp (fun ω => t i ℓ * Bs ℓ (ts i) ω) 2 P := fun i =>
      (hMemLpBs ℓ (ts i)).const_mul _
    have hcovXX : cov[fun ω => ∑ i, t i ℓ * Bs ℓ (ts i) ω,
        fun ω => ∑ i', t i' ℓ * Bs ℓ (ts i') ω; P]
        = ∑ i, ∑ i', cov[fun ω => t i ℓ * Bs ℓ (ts i) ω,
            fun ω => t i' ℓ * Bs ℓ (ts i') ω; P] :=
      covariance_fun_sum_fun_sum hmemX hmemX
    have hpair : ∀ i i' : Fin m, cov[fun ω => t i ℓ * Bs ℓ (ts i) ω,
        fun ω => t i' ℓ * Bs ℓ (ts i') ω; P] = t i ℓ * t i' ℓ * (min (ts i) (ts i') : ℝ) := by
      intro i i'
      rw [covariance_const_mul_left, covariance_const_mul_right, hcovBs ℓ (ts i) (ts i')]
      ring
    have hVarEq : Var[Y' ℓ; P] = cov[Y' ℓ, Y' ℓ; P] :=
      (covariance_self (hHasGaussY' ℓ).aemeasurable).symm
    rw [hVarEq]
    show cov[fun ω => ∑ i, t i ℓ * Bs ℓ (ts i) ω, fun ω => ∑ i', t i' ℓ * Bs ℓ (ts i') ω; P] = _
    rw [hcovXX]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => hpair i i'
  have hY'am : ∀ ℓ, AEMeasurable (Y' ℓ) P := fun ℓ => (hHasGaussY' ℓ).aemeasurable
  have hYfe : ∀ ℓ, Y ℓ = fun ω => (1 / Real.sqrt d) * Y' ℓ ω := fun ℓ => funext (hYeq ℓ)
  have hYam : ∀ ℓ, AEMeasurable (Y ℓ) P := fun ℓ => by
    rw [hYfe ℓ]; exact (hY'am ℓ).const_mul _
  have hone2 : ∀ a b : ℝ, (inner ℝ a b : ℝ) = a * b := fun a b => by
    rw [RCLike.inner_apply]; simp; ring
  -- char function of `Yℓ` via scaling
  have hchareq : ∀ ℓ, charFun (P.map (Y ℓ)) 1 = charFun (P.map (Y' ℓ)) (1 / Real.sqrt d) := by
    intro ℓ
    rw [charFun_apply, charFun_apply,
      integral_map (hYam ℓ) (by fun_prop), integral_map (hY'am ℓ) (by fun_prop)]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    show Complex.exp (((⟪Y ℓ ω, (1:ℝ)⟫ : ℝ) : ℂ) * Complex.I)
        = Complex.exp (((⟪Y' ℓ ω, (1 / Real.sqrt d : ℝ)⟫ : ℝ) : ℂ) * Complex.I)
    rw [hone2, hone2, mul_one, hYeq ℓ ω]
    ring_nf
  have hmeanY : ∀ ℓ, P[Y ℓ] = 0 := by
    intro ℓ
    rw [hYfe ℓ, integral_const_mul, hmeanY' ℓ, mul_zero]
  have hvarY : ∀ ℓ, Var[Y ℓ; P]
      = (∑ i, ∑ i', t i ℓ * t i' ℓ * (min (ts i) (ts i') : ℝ)) / d := by
    intro ℓ
    rw [hYfe ℓ, variance_const_mul, hvarY' ℓ, div_pow, one_pow,
      Real.sq_sqrt (by positivity : (0:ℝ) ≤ (d:ℝ))]
    ring
  have hcharY' : ∀ ℓ, charFun (P.map (Y' ℓ)) (1 / Real.sqrt d)
      = Complex.exp (((P[Y ℓ] : ℝ)) * Complex.I - (Var[Y ℓ; P] : ℝ) / 2) := by
    intro ℓ
    have hkey := (hHasGaussY' ℓ).charFun_map_eq (1 / Real.sqrt d : ℝ)
    have heqfun : (fun ω => (⟪(1 / Real.sqrt d : ℝ), Y' ℓ ω⟫ : ℝ)) = Y ℓ := by
      funext ω
      rw [hone2, ← hYeq ℓ ω]
    rw [heqfun] at hkey
    exact hkey
  have hchar1 : ∀ ℓ, charFun (P.map (Y ℓ)) 1
      = Complex.exp (-((∑ i, ∑ i', t i ℓ * t i' ℓ * (min (ts i) (ts i') : ℝ) : ℝ) : ℂ) / (2 * d)) := by
    intro ℓ
    rw [hchareq ℓ, hcharY' ℓ, hmeanY ℓ, hvarY ℓ]
    simp only [Complex.ofReal_zero, zero_mul, zero_sub]
    congr 1
    push_cast
    ring
  -- independence across coordinates
  have hgmeas : ∀ ℓ : Fin d, Measurable (fun h : ℝ≥0 → ℝ => ∑ i, t i ℓ * h (ts i)) := fun ℓ =>
    Finset.measurable_sum _ fun i _ => (measurable_pi_apply (ts i)).const_mul _
  have hYcomp : ∀ ℓ, Y ℓ = (fun h : ℝ≥0 → ℝ => ∑ i, t i ℓ * h (ts i)) ∘ (fun ω s => B s ω ℓ) := by
    intro ℓ; funext ω; rfl
  have hind : iIndepFun (fun ℓ => Y ℓ) P := by
    have := hB.indep.comp (fun ℓ : Fin d => fun h : ℝ≥0 → ℝ => ∑ i, t i ℓ * h (ts i)) hgmeas
    simpa [← hYcomp] using this
  have hprod : charFun (P.map (fun ω => ∑ ℓ, Y ℓ ω)) 1
      = ∏ ℓ, charFun (P.map (Y ℓ)) 1 := by
    have hh := iIndepFun.charFun_map_fun_sum_eq_prod (X := Y) (P := P) hYam hind
    have h1 := congrFun hh 1
    simpa [Finset.prod_apply] using h1
  -- assemble
  have hswap : (fun ω : Ω => ∑ i, ∑ ℓ, t i ℓ * B (ts i) ω ℓ) = fun ω => ∑ ℓ, Y ℓ ω := by
    funext ω
    show (∑ i, ∑ ℓ, t i ℓ * B (ts i) ω ℓ) = ∑ ℓ, ∑ i, t i ℓ * B (ts i) ω ℓ
    exact Finset.sum_comm
  rw [hswap, hprod]
  rw [show (∏ ℓ : Fin d, charFun (P.map (Y ℓ)) 1)
      = ∏ ℓ : Fin d, Complex.exp
        (-((∑ i, ∑ i', t i ℓ * t i' ℓ * (min (ts i) (ts i') : ℝ) : ℝ) : ℂ) / (2 * d))
      from Finset.prod_congr rfl fun ℓ _ => hchar1 ℓ]
  rw [← Complex.exp_sum]
  congr 1
  rw [← Finset.sum_div, Finset.sum_neg_distrib]
  push_cast
  ring

/-- **`AEMeasurable`: a single coordinate of a `LatticeProb.IsBrownianSpace` at a fixed time.**
General: `IsPreBrownianReal.aemeasurable` gives only `AEMeasurable`, not `Measurable`, matching
the design of Mathlib's Brownian-motion library (a modification is needed for genuine pointwise
measurability); this unwraps the scaling `IsBrownianSpace.coord` carries. -/
theorem aemeasurable_isBrownianSpace_coord {d : ℕ} (hd1 : 1 ≤ d)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} (hB : IsBrownianSpace d 0 B P) (t : ℝ≥0) (ℓ : Fin d) :
    AEMeasurable (fun ω => B t ω ℓ) P := by
  have hdR : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd1)
  have h1 : AEMeasurable (fun ω => Real.sqrt d * (B t ω ℓ - (0 : EuclideanSpace ℝ (Fin d)) ℓ)) P :=
    (hB.coord ℓ).aemeasurable t
  have heq : (fun ω => B t ω ℓ) = fun ω => (1 / Real.sqrt d) *
      (Real.sqrt d * (B t ω ℓ - (0 : EuclideanSpace ℝ (Fin d)) ℓ)) := by
    funext ω
    rw [show (0 : EuclideanSpace ℝ (Fin d)) ℓ = 0 from rfl, sub_zero]
    field_simp
  rw [heq]
  exact h1.const_mul _

end LatticeProb.Scaling.WalkCLT

end
