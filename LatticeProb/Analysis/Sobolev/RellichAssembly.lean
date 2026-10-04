/-
# Assembly of the negative-index Rellich–Kondrachov compact embedding

This file collects the pieces of the Rellich–Kondrachov compact-embedding
argument, `LatticeProb.External.RellichKondrachovNegSobolev`
(`LatticeProb/External/RellichKondrachovNegSobolev.lean`), and presents the
final reduction to a single named residual, `rkLowFreqNet`.

## The three steps and where each piece lives

1. **High frequency is uniformly small.**  `HighFrequency.lean` proves
   `sobolevNormSqHigh_le` (the tail is at most the weight ratio
   `(1 + (2πΛ)²)^{s₀-s}` times the full `H^s` norm) and
   `tendsto_weight_atTop_zero` (`s₀ < s` makes the ratio vanish); `Truncation.lean`
   packages this as `exists_sobolevNormSqHigh_le_truncation`: beyond a cutoff `Λ`,
   the high-frequency `H^{s₀}` content of every `H^s`-unit test function is at
   most `δ/2`.  `BandLimited.lean` records the compatible band-limited predicates.

2. **The low-frequency remainder is totally bounded.**  This is the single
   remaining analytic input, isolated as `rkLowFreqNet` in
   `RellichLowFreqNet.lean`: for the unit ball of `H^s(D)` restricted to functions
   whose high-frequency `H^{s₀}` content is small, there is a finite net in the
   `H^{s₀}(D)` norm with test-function centres.

3. **Assembly.**  `RellichLowFreqNet.lean` converts `rkLowFreqNet` into the
   internal finite-net statement `rkLowFrequencyStatement`
   (`rkLowFrequencyStatement_of_rkLowFreqNet`) using step 1, and `RellichEquiv.lean`
   identifies that statement with the external
   (`rellichKondrachov_iff_rkLowFrequencyStatement`,
   `rellichKondrachov_of_rkLowFrequencyStatement`).

## Supporting analytic pieces

* `RellichLowFreq.lean` (topological): convolution with a compactly supported
  smooth kernel maps `IsTestFn D` to `IsTestFn D'` when `tsupport φ + tsupport K ⊆ D'`.
* `RellichMollify.lean` (quantitative): the real-convolution Fourier identity and
  the multiplier bound
  `sobolevNormSq d s₀ (φ - φ ⋆ K) ≤ ofReal (c²) * sobolevNormSq d s φ`
  whenever `‖1 - 𝓕K ξ‖ ≤ c` and `s₀ ≤ s`; this is the analytic core of any
  mollification-based construction of the low-frequency net.
* `Additivity.lean` (quadratic norm inequality): `sobolevNormSq_add_le` and
  `sobolevNormSq_sub_le`, the triangle-type estimates that convert a finite net
  of approximations into a finite net for the original family.
* `RellichEstimate.lean` / `RellichNet.lean` (finite-net step): `rkResidual_holds`
  (the quantitative Fourier-decay bound) and `rk_finite_net_of_Cm_net`, which turns
  a finite `C^m`-net into a finite `sobolevNormSq d s₀`-net.
* `RellichBandLimited.lean` records the older band-limited `C^m`-net residual
  `rkBandLimitedCmNet`; its docstring records that this statement is too strong
  (the `H^s` unit ball is not `C^m`-bounded for `s < m`), so the corrected
  `rkLowFreqNet` is the one the assembly uses.

## The single remaining input

`rkLowFreqNet` is a `Prop` (a `def`), not a `sorry`: it is the only unproved
declaration this file leaves.  Everything else is discharged from the library.
-/
import LatticeProb.Analysis.Sobolev.RellichLowFreq
import LatticeProb.Analysis.Sobolev.RellichMollify
import LatticeProb.Analysis.Sobolev.Additivity
import LatticeProb.Analysis.Sobolev.HighFrequency
import LatticeProb.Analysis.Sobolev.Truncation
import LatticeProb.Analysis.Sobolev.BandLimited
import LatticeProb.Analysis.Sobolev.RellichEstimate
import LatticeProb.Analysis.Sobolev.RellichNet
import LatticeProb.Analysis.Sobolev.RellichEquiv
import LatticeProb.Analysis.Sobolev.RellichLowFreqNet
import LatticeProb.Analysis.Sobolev.RellichBandLimited

open MeasureTheory
open scoped ENNReal FourierTransform

namespace LatticeProb.Sobolev

/-- **Assembled low-frequency statement.**  The corrected low-frequency residual
`rkLowFreqNet` yields the internal finite-net statement: choose the cutoff `Λ`
from the (proved) high-frequency step and apply the residual at that `Λ`. -/
theorem rkLowFrequencyStatement_assembled (h : rkLowFreqNet) : rkLowFrequencyStatement :=
  rkLowFrequencyStatement_of_rkLowFreqNet h

/-- **Assembled external.**  With `rkLowFreqNet`, the external
`LatticeProb.External.RellichKondrachovNegSobolev` is discharged unconditionally
through its equivalence with the internal finite-net statement. -/
theorem rellichKondrachov_of_rkLowFreqNet (h : rkLowFreqNet) :
    LatticeProb.External.RellichKondrachovNegSobolev :=
  rellichKondrachov_of_rkLowFrequencyStatement (rkLowFrequencyStatement_assembled h)

/-- **The trivial converse.**  A finite net for the whole `H^s` unit ball of test
functions on `D` is in particular a finite net for the subfamily with small
high-frequency `H^{s₀}` content, so the full low-frequency statement implies the
residual.  This records that `rkLowFreqNet` is not stronger than the theorem it
assembles; the substantive direction is `rkLowFrequencyStatement_assembled`. -/
theorem rkLowFreqNet_of_rkLowFrequencyStatement (h : rkLowFrequencyStatement) : rkLowFreqNet := by
  intro d D hD s₀ s hss Λ hΛ δ hδ
  obtain ⟨N, ψ, hψ, hnet⟩ := h d D hD s₀ s hss δ hδ
  exact ⟨N, ψ, hψ, fun φ hφ hφn _ => hnet φ hφ hφn⟩

/-- **The band-limited route** (recorded for reference).  `RellichBandLimited.lean`
reduces the external to `rkBandLimitedCmNet`; that residual is stronger than the
corrected `rkLowFreqNet` and is documented there as false for `s < m`, so this is
not the route used above. -/
theorem rellichKondrachov_of_rkBandLimitedCmNet_assembled (h : rkBandLimitedCmNet) :
    LatticeProb.External.RellichKondrachovNegSobolev :=
  rellichKondrachov_of_rkBandLimitedCmNet h

end LatticeProb.Sobolev
