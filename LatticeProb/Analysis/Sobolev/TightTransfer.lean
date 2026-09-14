import LatticeProb.Analysis.Sobolev.Compact

open MeasureTheory
open scoped ENNReal FourierTransform

namespace LatticeProb.Sobolev

/-- **Tightness transfer.**  If a family of random functionals has `H^{-s₀}(D)`
dual norm at most `1` except on a set of measure at most `η`, then there are
finitely many test functions `ψ` such that the `H^{-s}(D)` dual norm is
controlled by the finitely many pairings `F ω (ψ i)` except on a set of measure
at most `η`.  This is the form the consumer's `TendstoInNegSobolev` reads. -/
theorem tight_transfer {d : ℕ} (D : Set (Space d)) (hD : IsDomain D)
    {s₀ s : ℝ} (h : s₀ < s) (η : ℝ) (hη : 0 < η)
    (hRK : LatticeProb.External.RellichKondrachovNegSobolev)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (F : Ω → (Space d → ℝ) → ℝ)
    (hadd : ∀ ω φ ψ, F ω (φ + ψ) = F ω φ + F ω ψ)
    (hsmul : ∀ ω c φ, F ω (fun x => c * φ x) = c * F ω φ)
    (htight : μ {ω | 1 < negSobolevNorm d s₀ D (F ω)} ≤ ENNReal.ofReal η) :
    ∃ (N : ℕ) (ψ : Fin N → Space d → ℝ), (∀ i, IsTestFn D (ψ i)) ∧
      μ {ω | (⨆ i, ENNReal.ofReal |F ω (ψ i)|) + ENNReal.ofReal η < negSobolevNorm d s D (F ω)}
        ≤ ENNReal.ofReal η := by
  obtain ⟨N, ψ, hψt, hnet⟩ := hRK d D hD s₀ s h η hη
  refine ⟨N, ψ, hψt, ?_⟩
  refine le_trans (measure_mono ?_) htight
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  by_contra hcon
  push Not at hcon
  exact absurd (negSobolevNorm_le_sup_add D h η hη N ψ hψt hnet (F ω) (hadd ω) (hsmul ω) hcon)
    (not_le.mpr hω)

end LatticeProb.Sobolev
