/-
# The mollification estimate: the residual of the Fréchet–Kolmogorov route

`FrechetKolmogorovMollify` (`FrechetKolmogorovReduce.lean:34`) states that a family supported in a
compact set and uniformly translation-continuous in the `H^s` norm is approximated, uniformly, by
convolution with a single smooth compactly supported mollifier.  This file isolates the analytic
content of that statement, and it proves that the content yields `FrechetKolmogorovMollify`.

The statement `FrechetKolmogorovMollify` carries a tightness hypothesis `tsupport f ⊆ K`, which its
proof cannot use; the estimate `SobolevMollificationEstimate` below is the same estimate without
that hypothesis.  Because the estimate has fewer hypotheses, it is the stronger statement, and the
theorem `frechetKolmogorovMollify_of_sobolevMollificationEstimate` derives
`FrechetKolmogorovMollify` from it by ignoring the tightness.

The estimate is a genuine theorem of analysis and not a missing binding: the standard proof
expresses `f - f ⋆ ρ` as the average `∫ y, ρ y • (fun x => f (x + y) - f x)` when `ρ` has total mass
one, and bounds the `H^s` norm of that average by the `L¹`-average of the translation errors, then
chooses `ρ` supported inside the radius where the translation-continuity hypothesis makes those
errors smaller than the accuracy.  The bounding step is the Young convolution inequality for the
weighted `L²` norm, which Mathlib does not contain: the library records this absence at
`LatticeProb/Analysis/Sobolev/BandLimitedCmBound.lean:187` and at
`LatticeProb/Analysis/Sobolev/TestFnApprox.lean:45`.  Those two references are citations of the
Mathlib gap only.  They are not a route, and this file does not mention or use
`BandLimitedTestFnApproxOnDomain`, `BandCentreSupportRepair`, `rkUniformCmNet` or `BandLimitedCmNet`,
all of which are refuted on the record; the hypotheses of this file are the uniform
translation-continuity, which is already proved as `sobolevNormSq_translate_sub_le`, and the
convolution structure of `convReal`.  This file registers nothing.
-/
import LatticeProb.Analysis.Sobolev.FrechetKolmogorovReduce

open MeasureTheory Filter Set
open scoped ENNReal FourierTransform Topology

namespace LatticeProb.Sobolev

/-- **The tightness-free mollification estimate.**  For every natural number `d`, real number `s`,
and family `S` of functions, if the family is uniformly translation-continuous in the `H^s` norm,
then for every positive accuracy there is one smooth compactly supported function `ρ` whose
convolution approximates every member of `S` in the `H^s` norm to that accuracy.  This estimate omits
the tightness hypothesis of `FrechetKolmogorovMollify`, so it is the stronger statement; it is the
analytic residual of the Fréchet–Kolmogorov route. -/
def SobolevMollificationEstimate : Prop :=
  ∀ (d : ℕ) (s : ℝ) (S : Set (Space d → ℝ)),
    (∀ (η : ℝ), 0 < η → ∃ (δ : ℝ), 0 < δ ∧ ∀ (h : Space d), ‖h‖ < δ →
      ∀ f ∈ S, sobolevNormSq d s (fun x => f (x + h) - f x) ≤ ENNReal.ofReal η) →
    ∀ (η : ℝ), 0 < η → ∃ ρ : Space d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) ρ ∧ HasCompactSupport ρ ∧
      ∀ f ∈ S, sobolevNormSq d s (fun x => f x - convReal f ρ x) ≤ ENNReal.ofReal η

/-- **The reduction.**  `FrechetKolmogorovMollify` follows from the tightness-free estimate
`SobolevMollificationEstimate` by discarding the tightness hypothesis, which the estimate does not
need.  Hence the residual of the mollification step is the estimate, and nothing else. -/
theorem frechetKolmogorovMollify_of_sobolevMollificationEstimate
    (h : SobolevMollificationEstimate) : FrechetKolmogorovMollify := by
  intro d _K _hK s S _htight htrans η hη
  exact h d s S htrans η hη

end LatticeProb.Sobolev

