import Mathlib

/-!
# The binomial local central limit theorem: comparator challenge

Mathlib-only comparator challenge for the binomial local central limit theorem
with an explicit `1/m` error, `LatticeProb.BinomialLCLT.exists_binomPMF_localCLT`
in `LatticeProb/Walk/BinomialLocalCLT.lean`.

Content: there is a constant `C` such that for every `m ≥ 1` and every integer
`j` with `|j| ≤ m` and `j ≡ m (mod 2)`,
`|√m · P_m(j) − 2 φ(j/√m)| ≤ C/m`, where `P_m(j) = C(m, (m + j)/2) / 2^m` is the
probability that a sum of `m` independent `±1` signs equals `j` and
`φ(x) = (2π)^{-1/2} e^{-x²/2}` is the standard normal density.  The factor `2`
is the reciprocal of the density of the parity class of `m`.

Only Mathlib is imported, and no definition is needed: the binomial probability
and the normal density are written out.  The sole intentional `sorry` is the
proof of the final theorem.

## Presentation deltas

The library names the two functions `binomPMF` and `gaussianDensity`; the
challenge writes out their bodies.  The hypothesis `|j| ≤ m` is essential, not
cosmetic: for `j < -m` the natural-number truncation `toNat` returns `0`, and
the expression reads `1 / 2^m` there instead of the probability `0`.
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
  sorry

end LatticeProbAudit
