import LatticeProb.Prob.GaussKahaneVector

/-!
# Kahane's convexity inequality for the Laplace functionals `y ↦ e^{-λ y}`

`LatticeProb.Kahane.kahaneFun_exp_neg`: for `λ ≥ 0` the function `y ↦ e^{-λ y}` is admissible
(`KahaneFun`) with the constant `1 + λ + λ²` and growth exponent `0`, since `e^{-λ y}`,
`λ e^{-λ y}` and `λ² e^{-λ y}` are bounded on `(0, ∞)`.

`LatticeProb.Kahane.kahane_convexity_exp_neg` is Kahane's inequality for these functions:

  `E exp (-λ ∑ᵢ pᵢ e^{Xᵢ - Var Xᵢ/2}) ≤ E exp (-λ ∑ᵢ pᵢ e^{Yᵢ - Var Yᵢ/2})`

for centred Gaussian vectors with `Cov X ≤ Cov Y`. This is the comparison of Laplace transforms
of discretised multiplicative chaos masses.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped RealInnerProductSpace

namespace LatticeProb

namespace Kahane

/-- `y ↦ e^{-λ y}` is admissible for Kahane's inequality when `λ ≥ 0`. -/
theorem kahaneFun_exp_neg {lam : ℝ} (hl : 0 ≤ lam) :
    KahaneFun (fun y => Real.exp (-lam * y)) (fun y => -lam * Real.exp (-lam * y))
      (fun y => lam ^ 2 * Real.exp (-lam * y)) (1 + lam + lam ^ 2) 0 where
  hasDerivAt y _ := by
    have h : HasDerivAt (fun y : ℝ => -lam * y) (-lam) y := by
      simpa using (hasDerivAt_id y).const_mul (-lam)
    simpa [mul_comm] using h.exp
  hasDerivAt' y _ := by
    have h : HasDerivAt (fun y : ℝ => -lam * y) (-lam) y := by
      simpa using (hasDerivAt_id y).const_mul (-lam)
    have h2 := h.exp.const_mul (-lam)
    refine h2.congr_deriv ?_
    ring
  continuousOn'' := by
    have : Continuous (fun y : ℝ => lam ^ 2 * Real.exp (-lam * y)) := by fun_prop
    exact this.continuousOn
  nonneg'' y _ := by positivity
  growth y hy := by
    have h1 : Real.exp (-lam * y) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    rw [abs_of_pos (Real.exp_pos _)]
    simp only [pow_zero, mul_one]
    nlinarith [sq_nonneg lam]
  growth' y hy := by
    have h1 : Real.exp (-lam * y) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    have h2 := Real.exp_pos (-lam * y)
    rw [abs_of_nonpos (by nlinarith)]
    simp only [pow_zero, mul_one]
    nlinarith [sq_nonneg lam]
  growth'' y hy := by
    have h1 : Real.exp (-lam * y) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    have h2 := Real.exp_pos (-lam * y)
    rw [abs_of_nonneg (by positivity)]
    simp only [pow_zero, mul_one]
    nlinarith [sq_nonneg lam]

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}

/-- **Kahane's convexity inequality for Laplace functionals**: for `λ ≥ 0`, centred Gaussian
vectors `X`, `Y` with `Cov X ≤ Cov Y` entrywise and positive weights `pᵢ`,
`E exp (-λ ∑ᵢ pᵢ e^{Xᵢ - Var Xᵢ/2}) ≤ E exp (-λ ∑ᵢ pᵢ e^{Yᵢ - Var Yᵢ/2})`. -/
theorem kahane_convexity_exp_neg {lam : ℝ} (hl : 0 ≤ lam) {p : ι → ℝ} (hp : ∀ i, 0 < p i)
    {X : Ω → ι → ℝ} {Y : Ω' → ι → ℝ} (hX : HasGaussianLaw X P) (hY : HasGaussianLaw Y P')
    (hXm : ∀ i, ∫ ω, X ω i ∂P = 0) (hYm : ∀ i, ∫ ω, Y ω i ∂P' = 0)
    (hcov : ∀ i j, cov[fun ω => X ω i, fun ω => X ω j; P] ≤
      cov[fun ω => Y ω i, fun ω => Y ω j; P']) :
    ∫ ω, Real.exp (-lam * ∑ i, p i * Real.exp (X ω i - Var[fun ω => X ω i; P] / 2)) ∂P ≤
      ∫ ω, Real.exp (-lam * ∑ i, p i * Real.exp (Y ω i - Var[fun ω => Y ω i; P'] / 2)) ∂P' :=
  kahane_convexity (kahaneFun_exp_neg hl) hp hX hY hXm hYm hcov

end Kahane

end LatticeProb
