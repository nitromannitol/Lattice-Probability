import LatticeProb.LQG.LocalMeasureKernel2

/-!
# Almost sure linearity of the pairings of a whole-plane GFF

For fixed test functions `φ`, `ψ` and fixed coefficients `a`, `b`, the pairing of a whole-plane Gaussian free field
with `a φ + b ψ` equals `a (h, φ) + b (h, ψ)` almost surely. The exceptional null set depends on `φ`, `ψ`, `a`, `b`;
the statement is the dot-notation form of `LatticeProb.LocalMeasureKernel.ae_pairing_linear_combination`, whose proof
shows that the difference is a centered Gaussian variable of variance zero by bilinearity of the covariance.
-/

open MeasureTheory Set
open LatticeProb.Gauss

namespace LatticeProb.Gauss.IsWholePlaneGFF

/-- Almost sure linearity of the pairings of a whole-plane GFF: for test functions `φ`, `ψ` and reals `a`, `b`,
`(h, a φ + b ψ) = a (h, φ) + b (h, ψ)` almost surely. -/
theorem ae_pairing_linear {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {φ ψ : ℂ → ℝ}
    (hφ : IsTestFunction Set.univ φ) (hψ : IsTestFunction Set.univ ψ) (a b : ℝ) :
    ∀ᵐ ω ∂P, hC ω (fun x => a * φ x + b * ψ x) = a * hC ω φ + b * hC ω ψ :=
  LatticeProb.LocalMeasureKernel.ae_pairing_linear_combination hh hφ hψ a b

end LatticeProb.Gauss.IsWholePlaneGFF
