import Mathlib
import LatticeProb.Network.GFF
import LatticeProbAudit.Support.Vocabulary
import LatticeProbAudit.Support.Bridge

/-!
# Solution: GFF

The challenge module `Audit/LatticeProbAudit/GFF/Challenge.lean` imports only
Mathlib and states the theorem with one intentional `sorry`.  This solution
imports the library together with `LatticeProbAudit.Support.Vocabulary`, a
verbatim copy of the challenge's vocabulary, rewrites the vocabulary's killed
Green function into the library's (`Audit/LatticeProbAudit/Support/Bridge.lean`),
and proves the byte-identical statement with the library's field
`LatticeProb.Network.gff`, from `LatticeProb.Network.killedGreenMatrix_posSemidef`,
`LatticeProb.Network.integral_gff` and `LatticeProb.Network.covariance_gff`.
-/

namespace LatticeProbAudit

open MeasureTheory ProbabilityTheory

universe u

/-- The Gaussian free field on a finite set `C` with zero boundary values: the killed
Green function is positive semidefinite on `C`, and it is the covariance of a centred
Gaussian measure on `ℝ^C`. -/
theorem gff {V : Type u} {G : SimpleGraph V} [G.LocallyFinite] (hG : G.Connected)
    (C : Finset V) {q : V} (hq : q ∉ C) :
    (Matrix.of fun x y : C => killedGreenReal G (C : Set V) x y).PosSemidef ∧
      ∃ μ : Measure (EuclideanSpace ℝ C), IsGaussian μ ∧ ∫ φ, φ ∂μ = 0 ∧
        ∀ x y : C, cov[fun φ : EuclideanSpace ℝ C => φ x, fun φ => φ y; μ]
          = killedGreenReal G (C : Set V) x y := by
  classical
  rw [Bridge.killedGreenReal_eq]
  refine ⟨LatticeProb.Network.killedGreenMatrix_posSemidef hG C hq,
    LatticeProb.Network.gff G C, ?_, LatticeProb.Network.integral_gff C,
    fun x y => LatticeProb.Network.covariance_gff hG C hq x y⟩
  unfold LatticeProb.Network.gff
  infer_instance

end LatticeProbAudit
