/-
# Rellich–Kondrachov: the low-frequency net, corrected

The Rellich–Kondrachov argument on a bounded domain `D` has three steps:
truncate in frequency, cover the band-limited remainder by a finite net, and
assemble with the triangle inequality.  The frequency-truncation step
(`exists_sobolevNormSqHigh_le_truncation`, `Truncation.lean`) and the
quantitative Fourier-decay residual that converts `C^m`-closeness into
`H^{s₀}`-closeness (`rkResidual_holds`, `RellichEstimate.lean`) are proved.

## Erratum: the `C^m`-net residual of `RellichBandLimited.lean` is false

`rkBandLimitedCmNet` asserts that the whole unit ball of `H^s(D)` admits a finite
`C^m`-net of test functions on `D`, for every `m`.  That is false for every
`s < m`: the `H^s` unit ball is *not* `C^m`-bounded.  Take a fixed nonnegative
`ρ ∈ C_c^∞(D)` with `ρ = 1` on a small ball and `∫ ρ ≠ 0`, and put
`u_N(x) = N^{-M} sin (N x₁) ρ(x)`.  Its Fourier transform is concentrated at
`‖ξ‖ ≈ N`, so `‖u_N‖_{H^s} ≈ N^{s - M} → 0` once `M > s`, while
`‖∂₁^m u_N‖_∞ ≈ N^{m - M} → ∞` once `M < m`.  Choosing `s < M < m` gives an
`H^s`-bounded family that is unbounded in `C^m`, so no finite `C^m`-net can
exist.  (In particular the family need not be band-limited, and adding an
`IsBandLimited` hypothesis does not repair the statement: a nonzero compactly
supported function has an entire Fourier transform and cannot vanish on the open
complement of a ball, so it would be band-limited only if it were zero.)

The reduction `rkLowFrequencyStatement_of_rkBandLimitedCmNet` is therefore a
valid implication from a false premise, and its docstring's claim that
`rkBandLimitedCmNet` is "exactly the compactness input" is not correct.

## The corrected residual

The content the classical proof actually needs is *low-frequency compactness*:
once a cutoff `Λ` has made the high-frequency part of the `H^{s₀}` norm small,
the remaining (low-frequency) part of the unit ball is totally bounded.  This is
stated below as `rkLowFreqNet`, without the false `C^m` demand and without
requiring the net centres to be band-limited: the centres are test functions on
`D`, and only the inputs of the finite net are constrained to have small
high-frequency part.  `rkLowFrequencyStatement_of_rkLowFreqNet` is the glue: it
chooses `Λ` from the (proved) frequency-truncation step and appeals to the
residual, and `rellichKondrachovNegSobolev_of_lowfreqNet` reduces the external
to it.

The residual itself is the genuinely missing analytic content: the frequency
truncation operator `P_Λ`, the band-limited Bernstein/`H^s → C^m` bound, the
Arzelà–Ascoli net, and the support/mollification repair that replaces the
non-compactly-supported band-limited centres by test functions on `D`.
-/
import LatticeProb.Analysis.Sobolev.RellichEquiv
import LatticeProb.Analysis.Sobolev.Truncation
import LatticeProb.Analysis.Sobolev.BandLimited

open MeasureTheory
open scoped ENNReal FourierTransform

namespace LatticeProb.Sobolev

/-- **The low-frequency net residual.**  For a bounded domain `D`, orders
`s₀ < s`, a cutoff `Λ ≥ 0` and an accuracy `δ > 0`, the set of test functions on
`D` whose `H^s` norm is at most `1` and whose high-frequency `H^{s₀}` content is
at most `δ/2` is covered by finitely many `δ`-balls in the `H^{s₀}` norm, with
centres that are test functions on `D`.

This is the corrected form of the low-frequency step: the hypothesis bounds the
part of the norm that the truncation step discards, and the conclusion is exactly
the low-frequency compactness that the finite-net assembly consumes.  It is
strictly weaker than `rkLowFrequencyStatement` (the high-frequency smallness is
an extra hypothesis) and it does not demand any `C^m` bound, so it is not
refuted by the oscillating family that kills `rkBandLimitedCmNet`. -/
def rkLowFreqNet : Prop :=
  ∀ (d : ℕ) (D : Set (Space d)), IsDomain D → ∀ (s₀ s : ℝ), s₀ < s →
    ∀ Λ : ℝ, 0 ≤ Λ → ∀ δ : ℝ, 0 < δ →
      ∃ (N : ℕ) (ψ : Fin N → Space d → ℝ), (∀ i, IsTestFn D (ψ i)) ∧
        ∀ φ : Space d → ℝ, IsTestFn D φ → sobolevNormSq d s φ ≤ 1 →
          sobolevNormSqHigh d s₀ Λ φ ≤ ENNReal.ofReal (δ / 2) →
            ∃ i, sobolevNormSq d s₀ (fun x => φ x - ψ i x) ≤ ENNReal.ofReal δ

/-- **The glue.**  The low-frequency net residual implies the internal
finite-net statement: choose the cutoff `Λ` that makes the high-frequency part of
the `H^{s₀}` norm at most `δ/2` on the unit ball of `H^s`, and apply the residual
at that `Λ`. -/
theorem rkLowFrequencyStatement_of_rkLowFreqNet (h : rkLowFreqNet) :
    rkLowFrequencyStatement := by
  intro d D hD s₀ s hss δ hδ
  obtain ⟨Λ, hΛ, htail⟩ := exists_sobolevNormSqHigh_le_truncation
    (d := d) (s₀ := s₀) (s := s) hss (Real.sqrt (δ / 2))
    (Real.sqrt_pos_of_pos (by positivity))
  obtain ⟨N, ψ, hψ, hnet⟩ := h d D hD s₀ s hss Λ hΛ δ hδ
  refine ⟨N, ψ, hψ, fun φ hφ hφn => ?_⟩
  refine hnet φ hφ hφn ?_
  refine (htail φ hφn).trans ?_
  rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ δ / 2)]

/-- **The external, from a producer of the low-frequency net.**  With
`rkLowFreqNet` the external `RellichKondrachovNegSobolev` is discharged
unconditionally through the equivalence with `rkLowFrequencyStatement`. -/
theorem rellichKondrachovNegSobolev_of_lowfreqNet (h : rkLowFreqNet) :
    LatticeProb.External.RellichKondrachovNegSobolev :=
  rellichKondrachov_of_rkLowFrequencyStatement (rkLowFrequencyStatement_of_rkLowFreqNet h)

end LatticeProb.Sobolev
