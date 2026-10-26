import LatticeProb.Prob.Percolation.CorrectedPlaneCharacterization
import LatticeProb.Prob.Percolation.LatticeBondCritical

/-!
# Qualitative first-order corrector input from the literature

This explicit proposition records a qualitative consequence of Armstrong–Dario,
arXiv:1609.09431v2, Theorem 2 and (1.22), and Dario–Gu, arXiv:1909.10439v4,
pp. 5–6 and Section 2.3.1, Proposition 2.12 (p. 22). It asserts no proof or instance.
The common almost-sure event precedes all slopes and all component basepoints.
Existence and uniqueness of the infinite component are supplied separately.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.External

open MeasureTheory LatticeProb.Percolation

/-- Almost surely, each slope has a unique normalized harmonic plane, and every A₁
function has a unique slope. Normalization uses an actual component vertex. The uniform
sublinear error is the qualitative consequence of the cited oscillation estimate; no
stochastic moment estimate or gradient estimate is included in this proposition. -/
def SupercriticalBondCorrectorInput : Prop :=
  ∀ (d : ℕ) [NeZero d], 2 ≤ d → ∀ p : unitInterval,
    criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
    ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω,
      (∀ q : Fin d → ℝ, ∀ o : uniqueInfiniteComponent h,
        ∃! u : uniqueInfiniteComponent h → ℝ,
          IsCorrectedPlane (uniqueInfiniteComponent h) q u ∧ u o = 0) ∧
      (∀ u : uniqueInfiniteComponent h → ℝ,
        u ∈ harmonicGrowthSpace (uniqueInfiniteComponent h) 1 →
        ∃! q : Fin d → ℝ, IsCorrectedPlane (uniqueInfiniteComponent h) q u)

end LatticeProb.External
