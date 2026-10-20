/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: LQGMetric/Gaussian/KahaneRpow.lean.
-/
import LatticeProb.Prob.GaussKahaneVector

/-!
# Kahane's convexity inequality for the moments `y ↦ y^q`, `q ∉ (0, 1)`

`LatticeProb.Kahane.kahaneFun_rpow`: `y ↦ y^q` is admissible (`KahaneFun`) for `q ≤ 0` or `q ≥ 1`,
and `LatticeProb.Kahane.kahane_convexity_rpow` is Kahane's inequality for these functions:

  `E (∑ᵢ pᵢ e^{Xᵢ - Var Xᵢ/2})^q ≤ E (∑ᵢ pᵢ e^{Yᵢ - Var Yᵢ/2})^q`

for centred Gaussian vectors with `Cov X ≤ Cov Y`. The case `q ≥ 1` covers positive moments and
the case `q ≤ 0` covers negative moments of such sums. The growth bound `y^a ≤ (y + y⁻¹)^k`
for `|a| ≤ k` is proved directly in this file.

The namespace `KahaneRpowExample` shows that the hypotheses are satisfiable: `y ↦ y^2` is
admissible, and `Y = X` satisfies the covariance comparison.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped RealInnerProductSpace NNReal

namespace LatticeProb

namespace Kahane

/-- For `y > 0`, `1 ≤ y + y⁻¹`. -/
lemma one_le_add_inv {y : ℝ} (hy : 0 < y) : 1 ≤ y + y⁻¹ := by
  rcases le_total 1 y with h | h
  · linarith [inv_pos.2 hy]
  · have : 1 ≤ y⁻¹ := one_le_inv₀ hy |>.2 h
    linarith

/-- For `y > 0` and `|a| ≤ k`, `y ^ a ≤ (y + y⁻¹) ^ k`. -/
lemma rpow_le_pow_add_inv {y a : ℝ} (hy : 0 < y) {k : ℕ} (hk : |a| ≤ k) :
    y ^ a ≤ (y + y⁻¹) ^ k := by
  have h1 := one_le_add_inv hy
  have hi := inv_pos.2 hy
  rw [← Real.rpow_natCast]
  rcases le_total 0 a with ha | ha
  · rw [abs_of_nonneg ha] at hk
    calc y ^ a ≤ (y + y⁻¹) ^ a := Real.rpow_le_rpow hy.le (by linarith) ha
      _ ≤ (y + y⁻¹) ^ (k : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 hk
  · rw [abs_of_nonpos ha] at hk
    calc y ^ a = y⁻¹ ^ (-a) := by rw [Real.inv_rpow hy.le, Real.rpow_neg hy.le, inv_inv]
      _ ≤ (y + y⁻¹) ^ (-a) := Real.rpow_le_rpow hi.le (by linarith) (by linarith)
      _ ≤ (y + y⁻¹) ^ (k : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 hk

/-- A bound `|c| ≤ K` multiplied by `y ^ a` with `|a| ≤ k` is bounded by `K (y + y⁻¹) ^ k`. -/
lemma abs_mul_rpow_le {y c a K : ℝ} (hy : 0 < y) {k : ℕ} (hk : |a| ≤ k) (hc : |c| ≤ K) :
    |c * y ^ a| ≤ K * (y + y⁻¹) ^ k := by
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hy.le a)]
  exact mul_le_mul hc (rpow_le_pow_add_inv hy hk) (Real.rpow_nonneg hy.le a)
    ((abs_nonneg _).trans hc)

/-- `y ↦ y^q` is admissible for Kahane's inequality when `q ≤ 0` or `q ≥ 1`. -/
theorem kahaneFun_rpow (q : ℝ) (hq : q ≤ 0 ∨ 1 ≤ q) :
    KahaneFun (fun y => y ^ q) (fun y => q * y ^ (q - 1)) (fun y => q * (q - 1) * y ^ (q - 2))
      (1 + |q| + |q * (q - 1)|) (⌈|q|⌉₊ + 2) where
  hasDerivAt y hy := Real.hasDerivAt_rpow_const (Or.inl hy.ne')
  hasDerivAt' y hy := by
    have := (Real.hasDerivAt_rpow_const (p := q - 1) (Or.inl hy.ne')).const_mul q
    refine this.congr_deriv ?_
    rw [show q - 1 - 1 = q - 2 by ring]; ring
  continuousOn'' y hy :=
    ((Real.hasDerivAt_rpow_const (p := q - 2) (Or.inl (ne_of_gt hy))).continuousAt.const_mul
      (q * (q - 1))).continuousWithinAt
  nonneg'' y hy := by
    refine mul_nonneg ?_ (Real.rpow_nonneg hy.le _)
    rcases hq with hq | hq
    · nlinarith
    · nlinarith
  growth y hy := by
    have h := abs_mul_rpow_le (c := 1) (a := q) (K := 1 + |q| + |q * (q - 1)|)
      (k := ⌈|q|⌉₊ + 2) hy
      (by have := Nat.le_ceil |q|; push_cast; linarith)
      (by rw [abs_one]; linarith [abs_nonneg q, abs_nonneg (q * (q - 1))])
    simpa using h
  growth' y hy := abs_mul_rpow_le hy
    (by have := Nat.le_ceil |q|; have := abs_sub q 1; push_cast; rw [abs_one] at this; linarith)
    (by linarith [abs_nonneg (q * (q - 1))])
  growth'' y hy := abs_mul_rpow_le hy
    (by have := Nat.le_ceil |q|; have := abs_sub q 2; push_cast
        rw [abs_two] at this; linarith)
    (by linarith [abs_nonneg q])

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}

/-- **Kahane's convexity inequality for the moments** `q ≤ 0` or `q ≥ 1`. -/
theorem kahane_convexity_rpow {q : ℝ} (hq : q ≤ 0 ∨ 1 ≤ q) {p : ι → ℝ} (hp : ∀ i, 0 < p i)
    {X : Ω → ι → ℝ} {Y : Ω' → ι → ℝ} (hX : HasGaussianLaw X P) (hY : HasGaussianLaw Y P')
    (hXm : ∀ i, ∫ ω, X ω i ∂P = 0) (hYm : ∀ i, ∫ ω, Y ω i ∂P' = 0)
    (hcov : ∀ i j, cov[fun ω => X ω i, fun ω => X ω j; P] ≤
      cov[fun ω => Y ω i, fun ω => Y ω j; P']) :
    ∫ ω, (∑ i, p i * Real.exp (X ω i - Var[fun ω => X ω i; P] / 2)) ^ q ∂P ≤
      ∫ ω, (∑ i, p i * Real.exp (Y ω i - Var[fun ω => Y ω i; P'] / 2)) ^ q ∂P' :=
  kahane_convexity (kahaneFun_rpow q hq) hp hX hY hXm hYm hcov

namespace KahaneRpowExample

/-- The power `y ↦ y ^ 2` is admissible for `KahaneFun`, so the hypothesis of
`kahane_convexity_rpow` is satisfiable with `q = 2`. -/
example : KahaneFun (fun y : ℝ => y ^ (2 : ℝ)) (fun y => 2 * y ^ (2 - 1 : ℝ))
    (fun y => 2 * (2 - 1) * y ^ (2 - 2 : ℝ)) (1 + |(2 : ℝ)| + |2 * (2 - 1)|) (⌈|(2 : ℝ)|⌉₊ + 2) :=
  kahaneFun_rpow 2 (Or.inr (by norm_num))

/-- With `Y = X` the covariance comparison holds with equality, so `kahane_convexity_rpow`
applies to any centred Gaussian vector `X` with positive weights, for `q = 2`. -/
example {p : ι → ℝ} (hp : ∀ i, 0 < p i) {X : Ω → ι → ℝ} (hX : HasGaussianLaw X P)
    (hXm : ∀ i, ∫ ω, X ω i ∂P = 0) :
    ∫ ω, (∑ i, p i * Real.exp (X ω i - Var[fun ω => X ω i; P] / 2)) ^ (2 : ℝ) ∂P ≤
      ∫ ω, (∑ i, p i * Real.exp (X ω i - Var[fun ω => X ω i; P] / 2)) ^ (2 : ℝ) ∂P :=
  kahane_convexity_rpow (q := 2) (Or.inr (by norm_num)) hp hX hX hXm hXm fun _ _ => le_rfl

end KahaneRpowExample

end Kahane

end LatticeProb
