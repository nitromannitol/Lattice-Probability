/-
# Assembly of the Rellich low-frequency net from the landed pieces

`rkLowFreqNet` is the residual of the Rellich–Kondrachov external.  Its inputs are, by now,
landed separately:

* the band-limited **Bernstein bound** (`BandLimitedBernstein.lean`, `BandLimitedCmBound.lean`):
  the truncation `P_Λ φ` of an `H^s`-unit-ball test function has all derivatives up to order `m`
  uniformly bounded, for `s ≥ 0`;
* the **Arzelà–Ascoli net form** (`RellichCmNetReduction.lean`): a uniformly bounded, uniformly
  Lipschitz family of continuous functions on a compact space has a finite sup-net with centres in
  the family;
* the **quantitative residual** `rkResidual_diff_bound` (`RellichNet.lean`), converting
  `C^m`-closeness into `H^{s₀}`-closeness.

What is still needed is the step that turns those into a finite net of **test functions** on `D`:
the truncation `P_Λ φ` is band-limited and hence not compactly supported, so its real part must be
replaced by a test function with a controlled `C^m` error — the *support repair*.  This module
carries that as the single explicit hypothesis `BandLimitedCmNet` and composes it with the
reduction `rkLowFreqNet_of_uniformCmNet` to obtain `rkLowFreqNet`, and hence the external
`RellichKondrachovNegSobolev`.

The producer `BandLimitedCmNet` itself (Bernstein + Arzelà–Ascoli on the truncation jet + support
repair) is `latprob-ds4` / `cerw-ds1`'s side of the work and is not re-proved here.
-/
import LatticeProb.Analysis.Sobolev.BandLimitedBernstein
import LatticeProb.Analysis.Sobolev.BandTruncReal
import LatticeProb.Analysis.Sobolev.RellichCmNetReduction
import LatticeProb.Analysis.Sobolev.RellichLowFreqNet

open MeasureTheory
open scoped ENNReal FourierTransform SchwartzMap

namespace LatticeProb.Sobolev

/-- **The support-repair input.**  The band-limited truncations of the low-frequency family
cannot be used as net centres directly: they are not compactly supported.  This `Prop` is the
exact remaining input — a finite family of test functions on `D` that is `ε`-close in the `C^m`
norm to every low-frequency `φ` in the `H^s` unit ball.  It is what the band-limited Bernstein
bound plus Arzelà–Ascoli plus the mollification of the centres produce. -/
def BandLimitedCmNet : Prop := rkUniformCmNet

/-- **The assembly.**  The support-repair input discharges `rkLowFreqNet` through the reduction
`rkLowFreqNet_of_uniformCmNet`, which converts the `C^m`-net of test functions into the
`H^{s₀}`-net using the quantitative residual `rkResidual_diff_bound`. -/
theorem rkLowFreqNet_of_bandLimitedCmNet (h : BandLimitedCmNet) : rkLowFreqNet :=
  rkLowFreqNet_of_uniformCmNet h

/-- **The external, from the support-repair input.**  Composing the assembly with the glue
`rellichKondrachovNegSobolev_of_lowfreqNet` discharges `RellichKondrachovNegSobolev` from the one
remaining hypothesis. -/
theorem rellichKondrachovNegSobolev_of_bandLimitedCmNet (h : BandLimitedCmNet) :
    LatticeProb.External.RellichKondrachovNegSobolev :=
  rellichKondrachovNegSobolev_of_lowfreqNet (rkLowFreqNet_of_bandLimitedCmNet h)

end LatticeProb.Sobolev
