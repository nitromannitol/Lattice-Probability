/-
# The mollification estimate for integrable families

`SobolevMollificationEstimate` states that an integrable family which is uniformly
translation-continuous in the `H^s` norm is approximated, uniformly, by convolution with one smooth
compactly supported function.  It carries no tightness hypothesis.  The estimate is proved as
`sobolevMollificationEstimate_holds` in `FrechetKolmogorovMollifyProved.lean`, where
`FrechetKolmogorovMollify` is derived as well.
-/
import LatticeProb.Analysis.Sobolev.FrechetKolmogorovReduce

open MeasureTheory Filter Set
open scoped ENNReal FourierTransform Topology

namespace LatticeProb.Sobolev

/-- **The mollification estimate.**  For every natural number `d`, real number `s`, and family `S`
of integrable functions that is uniformly translation-continuous in the `H^s` norm, for every
positive accuracy there is one smooth compactly supported function `ρ` whose convolution
approximates every member of `S` in the `H^s` norm to that accuracy. -/
def SobolevMollificationEstimate : Prop :=
  ∀ (d : ℕ) (s : ℝ) (S : Set (Space d → ℝ)),
    (∀ f ∈ S, Integrable f) →
    (∀ (η : ℝ), 0 < η → ∃ (δ : ℝ), 0 < δ ∧ ∀ (h : Space d), ‖h‖ < δ →
      ∀ f ∈ S, sobolevNormSq d s (fun x => f (x + h) - f x) ≤ ENNReal.ofReal η) →
    ∀ (η : ℝ), 0 < η → ∃ ρ : Space d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) ρ ∧ HasCompactSupport ρ ∧
      ∀ f ∈ S, sobolevNormSq d s (fun x => f x - convReal f ρ x) ≤ ENNReal.ofReal η

end LatticeProb.Sobolev
