import Mathlib
import LatticeProb.Walk.BinomialLocalCLT

/-!
# Solution: BinomialLocalCLT

The challenge module `LatticeProbAudit/BinomialLocalCLT/Challenge.lean`
imports only Mathlib and states the theorem with one intentional `sorry`.  This
solution proves the byte-identical statement by
`LatticeProb.BinomialLCLT.exists_binomPMF_localCLT`, whose statement is the
challenge's after unfolding `binomPMF` and `gaussianDensity`.
-/

namespace LatticeProbAudit

/-- The binomial local central limit theorem with an explicit `1/m` error.  The probability
that a sum of `m` independent `±1` signs equals `j` is `C(m, (m + j)/2) / 2^m`; the theorem
compares `√m` times it with twice the standard normal density at `j/√m`, over the `j` of the
parity of `m` in `[-m, m]`. -/
theorem binomial_local_clt :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ j : ℤ, j ≡ (m : ℤ) [ZMOD 2] → |j| ≤ (m : ℤ) →
      |Real.sqrt m * ((m.choose ((m + j) / 2).toNat : ℝ) / 2 ^ m)
          - 2 * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(((j : ℝ) / Real.sqrt m) ^ 2) / 2))|
        ≤ C / m := by
  exact LatticeProb.BinomialLCLT.exists_binomPMF_localCLT

end LatticeProbAudit
