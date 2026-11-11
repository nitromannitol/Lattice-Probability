import Mathlib
import LatticeProb.LQG.LengthMetric
import LatticeProb.LQG.LengthMetricDerived

/-!
# Weyl comparison of internal metrics on a closed set, with arclength reparametrization

For a Euclidean length metric `D` on `ℂ` and the Weyl scaling `E = e^{ξ f} · D` (Gwynne-Miller, arXiv:1905.00383,
(1.7)-(1.8)), with `ξ f ≤ B` on a set `U`, the internal metric of `E` on `U` is at most `e^B` times the internal metric
of `D` on `U`. The statement is `LatticeProb.LQG.WeylInternalClosed`; `LatticeProb.LQG.weylInternalClosed_derived`
proves it with no hypothesis added. The argument: a path in `U` is reparametrized by its `D`-arclength (Burago-Burago-Ivanov);
each sub-arc is a competitor in the infimum defining `weylScaling`, with weighted cost at most `e^B` times its length;
telescoping over a partition bounds the `E`-length of the path. The proof uses only that the path lies in `U`.

Provenance: the arclength reparametrization lemmas are adapted from the Lean formalization accompanying
[Harmonic balls in Liouville quantum gravity, arXiv:2208.11795], with the namespace changed to `LatticeProb.LQG` and the
imports changed to Mathlib and `LatticeProb.LQG.LengthMetric`. The Weyl comparison lemmas are adapted from the same
source. The arclength and curve-length lemmas they use are the `LatticeProb.LQG` declarations of `LatticeProb/LQG/LengthMetricDerived.lean`, imported here
-/

namespace LatticeProb.LQG

open MeasureTheory Set
open scoped ENNReal NNReal

/-- The closed-set Weyl comparison of internal metrics: for a Euclidean length metric `D`, a function `E ≥ 0` with
`ENNReal.ofReal (E x y) = weylScaling D ξ f x y`, and a closed set `U` with `ξ f ≤ B` on `U`, the internal metric of `E`
on `U` is at most `e^B` times the internal metric of `D` on `U` (Gwynne-Miller, arXiv:1905.00383, (1.8)). -/
def WeylInternalClosed : Prop :=
  ∀ (D E : ℂ → ℂ → ℝ) (ξ B : ℝ) (f : ℂ → ℝ) (U : Set ℂ), IsEuclideanLengthMetric D →
    (∀ x y, 0 ≤ E x y) → (∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y) → IsClosed U →
    (∀ z ∈ U, ξ * f z ≤ B) → ∀ x y, internalMetric E U x y ≤ ENNReal.ofReal (Real.exp B) * internalMetric D U x y

/-- **Closed-set Weyl comparison.** The statement `WeylInternalClosed` holds, with no hypothesis added. -/
theorem weylInternalClosed_derived : WeylInternalClosed := by
  intro D E ξ B f U hD _hEnn hscale _hclosed hweight x y
  have hc0 : ENNReal.ofReal (Real.exp B) ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos B)).ne'
  have hctop : ENNReal.ofReal (Real.exp B) ≠ ⊤ := ENNReal.ofReal_ne_top
  unfold internalMetric
  calc ⨅ (P : Path x y) (_ : ∀ t, P t ∈ U), pathLength E P
      ≤ ⨅ (P : Path x y) (_ : ∀ t, P t ∈ U), ENNReal.ofReal (Real.exp B) * pathLength D P :=
        le_iInf₂ fun P hP => (iInf₂_le P hP).trans (pathLength_le_of_weylScaling hD hscale hweight P hP)
    _ = ENNReal.ofReal (Real.exp B) * ⨅ (P : Path x y) (_ : ∀ t, P t ∈ U), pathLength D P := by
        simp only [ENNReal.mul_iInf_of_ne hc0 hctop]


end LatticeProb.LQG
