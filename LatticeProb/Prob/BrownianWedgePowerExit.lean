import LatticeProb.Analysis.HarmonicIsometry
import LatticeProb.Analysis.WedgeHarmonicPower
import LatticeProb.Prob.BrownianOpenHarmonicExit

/-! # Brownian exit identities for harmonic power profiles -/

set_option autoImplicit false

open MeasureTheory InnerProductSpace Set
open scoped NNReal

namespace LatticeProb

/-- The real part of a complex power is harmonic in Euclidean coordinates on the
open right half-plane. -/
theorem harmonicAt_euclidean_re_cpow {p : ℝ} {x : Euc 2}
    (hx : 0 < (Complex.orthonormalBasisOneI.repr.symm x).re) :
    HarmonicAt (fun y : Euc 2 =>
      ((Complex.orthonormalBasisOneI.repr.symm y) ^ (p : ℂ)).re) x := by
  exact harmonicAt_comp_linearIsometryEquiv Complex.orthonormalBasisOneI.repr.symm
    (harmonicAt_re_cpow (Or.inl hx))

/-- The expected power profile at the actual Brownian exit from a bounded open
set equals its starting value when the closure lies in the open right half-plane. -/
theorem integral_openExit_euclidean_re_cpow {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {x : Euc 2} {B : ℝ≥0 → Ω → Euc 2}
    (hB : IsBrownianSpace 2 x B P) {U : Set (Euc 2)} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {p : ℝ}
    (hhalf : ∀ y ∈ closure U, 0 < (Complex.orthonormalBasisOneI.repr.symm y).re) :
    ∫ ω, ((Complex.orthonormalBasisOneI.repr.symm
      (B (openExitTime B U ω).toNNReal ω)) ^ (p : ℂ)).re ∂P =
      ((Complex.orthonormalBasisOneI.repr.symm x) ^ (p : ℂ)).re := by
  refine integral_openExit_harmonicNearClosure (h := fun y : Euc 2 =>
    ((Complex.orthonormalBasisOneI.repr.symm y) ^ (p : ℂ)).re)
    (by norm_num) hB hU hUb ?_
  apply harmonicNearClosure_iff.mpr
  intro y hy
  exact harmonicAt_euclidean_re_cpow (hhalf y hy)

end LatticeProb
