import Mathlib
import LatticeProb.LQG.LQGMeasure
import LatticeProb.Analysis.VagueLimitSequence

/-!
# Existence of the vague limit of the circle-average approximations from countably many integrals

`exists_countable_determining_isLQGLimit`: there is a countable family `D` of continuous compactly supported functions
on `ℂ` such that, for every `γ` and every circle-average function `hε` continuous in the space variable at each dyadic
scale, convergence of `∫ g d(ε^{γ²/2} e^{γ hε ε z} dz)` along `ε = 2^{-k}` for all `g ∈ D` gives a locally finite
measure `m` with `IsLQGLimit γ hε m`.

This is the deterministic half of the construction of the Liouville measure (Duplantier and Sheffield, *Liouville
quantum gravity and KPZ*, Invent. Math. 185 (2011), Proposition 1.1): the probabilistic half is the almost sure
convergence of the countably many integrals. The proof combines the countable convergence-determining family of
`LatticeProb.VagueLimit.exists_countable_determining` with the Riesz-Markov-Kakutani representation theorem.
-/

open MeasureTheory Filter Topology

namespace LatticeProb.LQG

/-- **Vague limit of the circle-average approximations from countably many integrals.** -/
theorem exists_countable_determining_isLQGLimit :
    ∃ D : Set (ℂ → ℝ), D.Countable ∧ (∀ g ∈ D, Continuous g ∧ HasCompactSupport g) ∧
      ∀ (γ : ℝ) (hε : ℝ → ℂ → ℝ), (∀ k : ℕ, Continuous (hε (dyadicScale k))) →
        (∀ g ∈ D, ∃ ℓ : ℝ,
          Tendsto (fun k : ℕ => ∫ z, g z ∂(lqgApprox γ hε (dyadicScale k))) atTop (𝓝 ℓ)) →
        ∃ m : Measure ℂ, IsLQGLimit γ hε m := by
  obtain ⟨D, hDc, hDcc, hD⟩ := LatticeProb.VagueLimit.exists_countable_determining_vague_limit (X := ℂ)
  refine ⟨D, hDc, hDcc, fun γ hε hc hconv => ?_⟩
  have hfin : ∀ k : ℕ, IsFiniteMeasureOnCompacts (lqgApprox γ hε (dyadicScale k)) := fun k => by
    have : IsLocallyFiniteMeasure (lqgApprox γ hε (dyadicScale k)) := by
      unfold lqgApprox
      exact IsLocallyFiniteMeasure.withDensity_ofReal
        (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul (hc k))))
    infer_instance
  obtain ⟨m, hm, hlim⟩ := hD (fun k => lqgApprox γ hε (dyadicScale k)) hfin hconv
  exact ⟨m, ⟨hm, hlim⟩⟩

end LatticeProb.LQG
