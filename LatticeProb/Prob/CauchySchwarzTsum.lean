/-
# Cauchy-Schwarz for `tsum`

Moved from `manhattan-formalization` (`Manhattan.Paper.Nash`'s `section CS`),
where it was a shared helper behind two of the paper's estimates: the Nash
inequality on `ℤ²` (`Manhattan.Paper.Nash`, moved to
`LatticeProb.Walk.NashZ2`) and the Poisson-clock `L¹` concentration bound
(`Manhattan.Paper.TimeDerivative`, moved to `LatticeProb.Prob.PoissonClock`,
reached there via `Manhattan.Paper.{L2Decay,HeatKernel}`'s import of
`Manhattan.Paper.Nash`). Fully generic: Cauchy-Schwarz for an unordered sum
of nonnegative terms over an arbitrary index type.
-/
import Mathlib

namespace LatticeProb

/-- Cauchy-Schwarz for `tsum`: `∑ a i b i ≤ √(∑ a i²) · √(∑ b i²)` for
nonnegative summable `a`, `b`. -/
theorem tsum_mul_le_sqrt_mul_sqrt {ι : Type*} (a b : ι → ℝ) (ha0 : ∀ i, 0 ≤ a i)
    (hb0 : ∀ i, 0 ≤ b i) (hab : Summable fun i => a i * b i)
    (ha : Summable fun i => a i ^ 2) (hb : Summable fun i => b i ^ 2) :
    (∑' i, a i * b i) ≤ Real.sqrt (∑' i, a i ^ 2) * Real.sqrt (∑' i, b i ^ 2) := by
  have hA : (0:ℝ) ≤ ∑' i, a i ^ 2 := tsum_nonneg fun i => sq_nonneg _
  have hB : (0:ℝ) ≤ ∑' i, b i ^ 2 := tsum_nonneg fun i => sq_nonneg _
  refine hab.tsum_le_of_sum_le fun s => ?_
  have h1 : (∑ i ∈ s, a i * b i) ^ 2 ≤ (∑ i ∈ s, a i ^ 2) * ∑ i ∈ s, b i ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq s a b
  have h2 : (∑ i ∈ s, a i ^ 2) ≤ ∑' i, a i ^ 2 := ha.sum_le_tsum s (fun i _ => sq_nonneg _)
  have h3 : (∑ i ∈ s, b i ^ 2) ≤ ∑' i, b i ^ 2 := hb.sum_le_tsum s (fun i _ => sq_nonneg _)
  have h4 : (∑ i ∈ s, a i * b i) ^ 2 ≤ (∑' i, a i ^ 2) * ∑' i, b i ^ 2 :=
    h1.trans (mul_le_mul h2 h3 (Finset.sum_nonneg fun i _ => sq_nonneg _) hA)
  have h5 : 0 ≤ ∑ i ∈ s, a i * b i := Finset.sum_nonneg fun i _ => mul_nonneg (ha0 i) (hb0 i)
  rw [← Real.sqrt_mul hA]
  exact (Real.le_sqrt h5 (mul_nonneg hA hB)).2 h4

end LatticeProb
