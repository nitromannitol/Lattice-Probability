/-
# The Rellich low-frequency glue: quarantined

`rellichKondrachovNegSobolev_of_lowfreqNet` (`RellichLowFreqNet.lean`) reduces the external
`RellichKondrachovNegSobolev` to the residual `rkLowFreqNet`.  The route to `rkLowFreqNet` that
does *not* go through the false `rkUniformCmNet` (`RellichCmNetReduction.lean`; it asks the rough
fields `φ` themselves to be `C^m`-close to test functions, which fails once `s < m`) runs through
the **low-frequency projection** `P_Λ φ = bandProj d Λ …`.

**Quarantine.**  The residual `BandLimitedTestFnApprox` defined below is **false as stated**: it
ranges over *every* compactly supported `φ` while demanding a *fixed* `D`-supported net, so a bump
translated to infinity has no centre (its projected `H^{s₀}` norm stays at a fixed positive value
while the pairing with any fixed `D`-supported `ψ` tends to `0`).  The two implications that used
this premise, `rkLowFreqNet_of_truncation_and_supportRepair` and
`rellichKondrachovNegSobolev_of_truncation_and_supportRepair`, have therefore been **removed** and
are no longer registered.  The refutation and the corrected residual
`BandLimitedTestFnApproxOnDomain`, with the sound composition `rkLowFreqNet_of_domainSupportRepair`,
are in `SupportRepair.lean`.  The `def BandLimitedTestFnApprox` is kept only because
`bandLimitedTestFnApproxOnDomain_of_approx` (`SupportRepair.lean`) records that this (failed)
unrestricted residual would imply the restricted one; it must not be used as a hypothesis.

The genuine truncation identity is the registered lemma `sobolevNormSq_sub_bandProj_le`
(`BandProjectionConsume.lean`), used through the one-line alias `bandProjHighFreq` below.
-/
import LatticeProb.Analysis.Sobolev.Additivity
import LatticeProb.Analysis.Sobolev.BandProjectionConsume
import LatticeProb.Analysis.Sobolev.FejerLimit
import LatticeProb.Analysis.Sobolev.RellichLowFreqNet

open MeasureTheory Set
open scoped ENNReal FourierTransform

namespace LatticeProb.Sobolev

/-- **The truncation identity (one-line alias).**  The `H^s` error of the real projection
`P_Λ φ` is controlled by the high-frequency part of `φ`.  This is the registered lemma
`sobolevNormSq_sub_bandProj_le` (`BandProjectionConsume.lean`); it is kept as a one-line alias for
consumers and is deliberately **not** registered in the axioms audit. -/
def BandProjHighFreq : Prop :=
  ∀ (d : ℕ) (s : ℝ) (Λ : ℝ) (hΛ : 0 < Λ),
    ∀ (φ : Space d → ℝ) (hcont : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hcs : HasCompactSupport φ),
      sobolevNormSq d s (fun x => φ x - bandProj d Λ hΛ.ne' φ hcont hcs x)
        ≤ sobolevNormSqHigh d s Λ φ

/-- One-line alias of the registered `sobolevNormSq_sub_bandProj_le`. -/
theorem bandProjHighFreq : BandProjHighFreq :=
  fun d s Λ hΛ φ hcont hcs => sobolevNormSq_sub_bandProj_le d Λ hΛ φ hcont hcs s

/-- **The support-repair input — REFUTED, do not use as a hypothesis.**  The real projections of
the `H^s` unit ball are `H^{s₀}`-approximated by test functions on `D`.

This is **false as stated**: it quantifies over every compactly supported `φ` (no
`tsupport φ ⊆ D`) while demanding a *fixed* `D`-supported net, so a bump translated to infinity is
not covered.  It
is kept only as the (failed) unrestricted analogue of `BandLimitedTestFnApproxOnDomain`
(`SupportRepair.lean`), from which `bandLimitedTestFnApproxOnDomain_of_approx` derives the
restricted residual. -/
def BandLimitedTestFnApprox : Prop :=
  ∀ (d : ℕ) (D : Set (Space d)), IsDomain D → ∀ (s₀ s : ℝ), s₀ < s →
    ∀ (Λ : ℝ) (hΛ : 0 < Λ) (δ : ℝ), 0 < δ →
      ∃ (N : ℕ) (ψ : Fin N → Space d → ℝ), (∀ i, IsTestFn D (ψ i)) ∧
        ∀ (φ : Space d → ℝ) (hcont : ContDiff ℝ (⊤ : ℕ∞) φ)
          (hcs : HasCompactSupport φ),
          sobolevNormSq d s φ ≤ 1 →
            ∃ i, sobolevNormSq d s₀
                (fun x => bandProj d Λ hΛ.ne' φ hcont hcs x - ψ i x)
              ≤ ENNReal.ofReal δ

end LatticeProb.Sobolev
