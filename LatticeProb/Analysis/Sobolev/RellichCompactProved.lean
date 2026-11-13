import LatticeProb.Analysis.Sobolev.TightTransfer
import LatticeProb.Analysis.Sobolev.RellichConvolvedCompact

/-!
# The negative-order compact embedding without hypotheses

The Rellich–Kondrachov compact embedding in negative Sobolev order is proved in
`LatticeProb.Sobolev.rellichKondrachovNegSobolev_holds`.  Supplying it to the
dual-norm approximation `negSobolevNorm_le_finset_sup_add` and to the tightness
transfer `tight_transfer` gives both results with no cited input.
-/

open MeasureTheory
open scoped ENNReal

namespace LatticeProb.Sobolev

/-- **The compact embedding `H^{-s₀}(D) ↪ H^{-s}(D)` for `s₀ < s`**: every functional
bounded in the `H^{-s₀}(D)` dual norm is approximated in the `H^{-s}(D)` dual norm by
its values on a finite set of test functions. -/
theorem negSobolevNorm_le_finset_sup_add_unconditional {d : ℕ} (D : Set (Space d))
    (hD : IsDomain D) {s₀ s : ℝ} (h : s₀ < s) (η : ℝ) (hη : 0 < η) :
    ∃ (N : ℕ) (ψ : Fin N → Space d → ℝ), (∀ i, IsTestFn D (ψ i)) ∧
      ∀ F : (Space d → ℝ) → ℝ,
        (∀ φ ψ : Space d → ℝ, F (φ + ψ) = F φ + F ψ) →
        (∀ (c : ℝ) (φ : Space d → ℝ), F (fun x => c * φ x) = c * F φ) →
        negSobolevNorm d s₀ D F ≤ 1 →
          negSobolevNorm d s D F ≤ (⨆ i, ENNReal.ofReal |F (ψ i)|) + ENNReal.ofReal η :=
  negSobolevNorm_le_finset_sup_add D hD h η hη rellichKondrachovNegSobolev_holds

/-- **Tightness transfer.**  If a family of random functionals has `H^{-s₀}(D)` dual
norm at most `1` except on a set of measure at most `η`, then there are finitely many
test functions `ψ` such that the `H^{-s}(D)` dual norm is controlled by the pairings
`F ω (ψ i)` except on a set of measure at most `η`. -/
theorem tight_transfer_unconditional {d : ℕ} (D : Set (Space d)) (hD : IsDomain D)
    {s₀ s : ℝ} (h : s₀ < s) (η : ℝ) (hη : 0 < η)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (F : Ω → (Space d → ℝ) → ℝ)
    (hadd : ∀ ω φ ψ, F ω (φ + ψ) = F ω φ + F ω ψ)
    (hsmul : ∀ ω c φ, F ω (fun x => c * φ x) = c * F ω φ)
    (htight : μ {ω | 1 < negSobolevNorm d s₀ D (F ω)} ≤ ENNReal.ofReal η) :
    ∃ (N : ℕ) (ψ : Fin N → Space d → ℝ), (∀ i, IsTestFn D (ψ i)) ∧
      μ {ω | (⨆ i, ENNReal.ofReal |F ω (ψ i)|) + ENNReal.ofReal η < negSobolevNorm d s D (F ω)}
        ≤ ENNReal.ofReal η :=
  tight_transfer D hD h η hη rellichKondrachovNegSobolev_holds μ F hadd hsmul htight

end LatticeProb.Sobolev
