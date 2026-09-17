import LatticeProb.Analysis.Sobolev.DualNet
import LatticeProb.External.RellichKondrachovNegSobolev

open MeasureTheory
open scoped ENNReal FourierTransform

namespace LatticeProb.Sobolev

/-- **The compact embedding `H^{-s₀}(D) ↪ H^{-s}(D)` for `s₀ < s`**, in the
form the consumer's tightness argument uses: granted the cited
Rellich–Kondrachov compact embedding, every functional bounded in the
`H^{-s₀}(D)` dual norm is approximated in the `H^{-s}(D)` dual norm by its
values on a finite set of test functions. -/
theorem negSobolevNorm_le_finset_sup_add {d : ℕ} (D : Set (Space d))
    (hD : IsDomain D) {s₀ s : ℝ} (h : s₀ < s) (η : ℝ) (hη : 0 < η)
    (hRK : LatticeProb.External.RellichKondrachovNegSobolev) :
    ∃ (N : ℕ) (ψ : Fin N → Space d → ℝ), (∀ i, IsTestFn D (ψ i)) ∧
      ∀ F : (Space d → ℝ) → ℝ,
        (∀ φ ψ : Space d → ℝ, F (φ + ψ) = F φ + F ψ) →
        (∀ (c : ℝ) (φ : Space d → ℝ), F (fun x => c * φ x) = c * F φ) →
        negSobolevNorm d s₀ D F ≤ 1 →
          negSobolevNorm d s D F ≤ (⨆ i, ENNReal.ofReal |F (ψ i)|) + ENNReal.ofReal η := by
  obtain ⟨N, ψ, hψt, hnet⟩ := hRK d D hD s₀ s h η hη
  exact ⟨N, ψ, hψt, fun F hadd hsmul hF => negSobolevNorm_le_sup_add D h η hη N ψ hψt hnet F hadd hsmul hF⟩

end LatticeProb.Sobolev
