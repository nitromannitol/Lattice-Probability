import LatticeProb.Analysis.Schauder.BoundedDerivs

/-!
# Bounded derivatives of compactly supported functions

A `C^n` function on `ℝ^d` with compact support has every derivative of order `≤ n` continuous with
compact support, hence bounded. Consequently a smooth bump function, and the product of a smooth
bump function with a `C^n` function, has bounded derivatives up to order `n`; this is how cutoff
functions are fed into the predicate `BoundedDerivs`.
-/

namespace LatticeProb.Analysis.Schauder

noncomputable section

variable {d : ℕ}

/-- A `C^n` function with compact support has bounded derivatives up to order `n`. -/
theorem boundedDerivs_of_hasCompactSupport {n : ℕ} {v : Euc d → ℝ} (hv : ContDiff ℝ n v)
    (hc : HasCompactSupport v) : BoundedDerivs n v :=
  ⟨hv, fun _ hk =>
    (hv.continuous_iteratedFDeriv (by exact_mod_cast hk)).bounded_above_of_compact_support
      (hc.iteratedFDeriv _)⟩

/-- A smooth bump times a `C^n` function has bounded derivatives up to order `n`. -/
theorem boundedDerivs_bump_mul {n : ℕ} {c : Euc d} (η : ContDiffBump c) {u : Euc d → ℝ}
    (hu : ContDiff ℝ n u) : BoundedDerivs n (fun z => η z * u z) :=
  boundedDerivs_of_hasCompactSupport (η.contDiff.mul hu) (η.hasCompactSupport.mul_right)

/-- A smooth bump has bounded derivatives of every order. -/
theorem boundedDerivs_bump (n : ℕ) {c : Euc d} (η : ContDiffBump c) :
    BoundedDerivs n (fun z => η z) :=
  boundedDerivs_of_hasCompactSupport η.contDiff η.hasCompactSupport

end

end LatticeProb.Analysis.Schauder
