/-
Tightness transfer between negative Sobolev orders: a family of random
functionals tight in `H^{-s₀}(D)` is tight in `H^{-s}(D)` for `s₀ < s`.
-/
import LatticeProb.Analysis.Sobolev.Basic

open MeasureTheory
open scoped ENNReal FourierTransform

namespace LatticeProb.Sobolev

/-- Tightness in `H^{-s₀}(D)` implies tightness in `H^{-s}(D)` for `s₀ < s`:
the set where the `H^{-s}` dual norm exceeds `M` is contained in the set where
the `H^{-s₀}` dual norm exceeds `M`. -/
theorem tight_of_tight_anti {Ω : Type*} [MeasurableSpace Ω] (d : ℕ) {s₀ s : ℝ} (h : s₀ < s)
    (P : Measure Ω) (F : ℝ → Ω → (Space d → ℝ) → ℝ)
    (hT : ∀ D : Set (Space d), IsDomain D → ∀ ε : ℝ, 0 < ε →
      ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ R : ℝ, 1 ≤ R →
        P {ω | M < negSobolevNorm d s₀ D (F R ω)} ≤ ENNReal.ofReal ε) :
    ∀ D : Set (Space d), IsDomain D → ∀ ε : ℝ, 0 < ε →
      ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ R : ℝ, 1 ≤ R →
        P {ω | M < negSobolevNorm d s D (F R ω)} ≤ ENNReal.ofReal ε := by
  intro D hD ε hε
  obtain ⟨M, hM, hMR⟩ := hT D hD ε hε
  refine ⟨M, hM, fun R hR => ?_⟩
  refine le_trans (measure_mono ?_) (hMR R hR)
  intro ω hω
  exact lt_of_lt_of_le hω (negSobolevNorm_anti h.le D (F R ω))

end LatticeProb.Sobolev
