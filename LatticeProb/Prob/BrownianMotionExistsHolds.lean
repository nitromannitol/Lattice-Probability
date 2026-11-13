import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.BMExistence

/-!
# Existence of a standard real Brownian motion

The proposition `QuantumZipper.NonVacuity.BrownianMotionExists` holds: the continuous
modification of the Gaussian process with covariance `min s t`, built from an i.i.d. standard
Gaussian sequence in `QuantumZipper.BMExist.exists_isBrownianReal_stdP`, is a standard real
Brownian motion on the probability space `(ℕ → ℝ, LQGDimension.ExistAsm.stdP)`.

## Main results

* `LatticeProb.brownianMotionExists_holds`: `QuantumZipper.NonVacuity.BrownianMotionExists`.
-/

namespace LatticeProb

/-- A standard real Brownian motion exists on some probability space. -/
theorem brownianMotionExists_holds : QuantumZipper.NonVacuity.BrownianMotionExists := by
  obtain ⟨B, hB⟩ := QuantumZipper.BMExist.exists_isBrownianReal_stdP
  exact ⟨ℕ → ℝ, inferInstance, LQGDimension.ExistAsm.stdP, B, inferInstance, hB⟩

end LatticeProb
