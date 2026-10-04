/-
# The Rellich–Kondrachov external as the internal low-frequency finite net

`LatticeProb.External.RellichKondrachovNegSobolev` and the internal
`LatticeProb.Sobolev.rkLowFrequencyStatement` are the same finite-net statement, differing
only in how the accuracy is parameterised (`Real.ofReal (η ^ 2)` against `Real.ofReal δ`).
This module records the equivalence, so the outstanding proof obligation for the external is
exactly the internal low-frequency statement, and any producer of the latter yields the
external by `.mpr`.

The equivalence is a change of variable: the map `η ↦ η ^ 2` is a bijection of `(0, ∞)` onto
itself, with inverse `δ ↦ Real.sqrt δ`, and `Real.sq_sqrt` rewrites `(Real.sqrt δ) ^ 2 = δ`.
-/
import LatticeProb.Analysis.Sobolev.RellichEstimate

open MeasureTheory
open scoped ENNReal FourierTransform

namespace LatticeProb.Sobolev

/-- The external `RellichKondrachovNegSobolev` is logically equivalent to the internal
finite-net statement `rkLowFrequencyStatement`: rename the accuracy `δ = η ^ 2`
(equivalently `η = Real.sqrt δ`). -/
theorem rellichKondrachov_iff_rkLowFrequencyStatement :
    LatticeProb.External.RellichKondrachovNegSobolev ↔ rkLowFrequencyStatement := by
  constructor
  · intro h d D hD s₀ s hss δ hδ
    obtain ⟨N, ψ, hψ, hnet⟩ :=
      h d D hD s₀ s hss (Real.sqrt δ) (Real.sqrt_pos_of_pos hδ)
    refine ⟨N, ψ, hψ, fun φ hφ h1 => ?_⟩
    obtain ⟨i, hi⟩ := hnet φ hφ h1
    exact ⟨i, by simpa [Real.sq_sqrt hδ.le] using hi⟩
  · intro h d D hD s₀ s hss η hη
    obtain ⟨N, ψ, hψ, hnet⟩ :=
      h d D hD s₀ s hss (η ^ 2) (by positivity)
    exact ⟨N, ψ, hψ, fun φ hφ h1 => hnet φ hφ h1⟩

/-- **The external, from a producer of the internal low-frequency statement.**  This is the
one missing declaration: once `rkLowFrequencyStatement` is proved, the external is discharged
here and the `Compact` / `TightTransfer` chain loses its hypothesis. -/
theorem rellichKondrachov_of_rkLowFrequencyStatement
    (h : rkLowFrequencyStatement) : LatticeProb.External.RellichKondrachovNegSobolev :=
  rellichKondrachov_iff_rkLowFrequencyStatement.mpr h

end LatticeProb.Sobolev
