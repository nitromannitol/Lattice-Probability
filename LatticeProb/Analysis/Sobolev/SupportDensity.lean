/-
# The support/mollification density repair and the `BoundedContinuousFunction` packaging

Two gaps stood between the landed Rellich–Kondrachov glue
(`RellichLowFreqGlue.lean`, `rkLowFreqNet_of_truncation_and_supportRepair`) and the external:

1. **the density of test functions in `H^s(D)`** — the support repair `BandLimitedTestFnApprox`;
2. **the `BoundedContinuousFunction` packaging** — Arzelà–Ascoli
   (`exists_finite_supNet_of_uniformLip`, `RellichCmNetReduction.lean:43`) consumes a set of
   bounded continuous functions, whereas the low-frequency family is a set of bare functions.

This module lands the largest closed pieces of both, on top of the already-landed
`peetre_le`, `sobolevNormSq_le_of_fourier_norm_le` and `tendsto_sobolevNormSq_of_fourier_factor`
(`TestFnApprox.lean`, commits `7d443cd`, `73f528b`) and the uniform Lipschitz bound
`exists_uniform_lipschitz_bandTrunc` (`BandLimitedLip.lean`, commit `04bf10e`).

* `fourier_convolution_lift` — the `ℂ`-valued convolution theorem
  `𝓕 (u ⋆ v) = 𝓕 u * 𝓕 v` for integrable `u v` (Mathlib's
  `Real.fourier_mul_convolution_eq`).  This is the Fourier input named missing in
  `TestFnApprox.lean`; it identifies `𝓕 (u - χ_ε * u)` with `𝓕 u * (1 - 𝓕 χ_ε)`.
* `exists_testFn_approx_of_fourier_tendsto` — **the density theorem, fully reduced**: once the
  mollification errors `w n` carry the factor form `𝓕 (lift (w n)) = 𝓕 (lift u) · c n` with
  `‖c n‖ ≤ 1`, `c n ξ → 0`, and each `u - w n` is a test function, the `H^s` error tends to `0`
  and `ψ := u - w n` is the wanted approximant.  Both `hid` and `hw` are named residual
  hypotheses; the construction of the approximate identity `χ_ε` with `𝓕 χ_ε → 1` is not in
  Mathlib.
* `bandProjBCF` — the real low-frequency projection `bandProj` packaged as a
  `BoundedContinuousFunction (Space d) ℝ`, the first half of the Arzelà–Ascoli input.

## The remaining, exactly-named gaps

* `MollifierFourierTendsto` — a sequence of `C_c^∞` mollifiers `χ_n` with `𝓕 χ_n → 1` pointwise
  and `‖𝓕 χ_n‖ ≤ 1`.  Mathlib has `ContDiffBump` and the Fourier scaling/translation lemmas, but
  no packaged approximate identity, and no `𝓕 χ_n ξ → ∫ χ_n` for a rescaled bump.
* the compact carrier: `Space d` is **not** compact, so `exists_finite_supNet_of_uniformLip` must
  be applied to the restriction of the family to `closure D` (compact, `D` a bounded domain) and
  the resulting net centres extended back to `Space d`; the extension is where the
  compactly-supported cut-off of the support repair is needed.
* the `C^m` (jet) form of the net: `exists_finite_supNet_of_uniformLip` is stated for
  `BoundedContinuousFunction α ℝ` and gives a **sup**-net; the jet `x ↦ (f x, f' x, …)` of
  `rkBandLimitedJetNet` (`RellichCmNetSupply.lean:78`) is `ℂ`-valued, so a general-codomain
  Arzelà–Ascoli is required.  It is not re-derived here.
-/
import LatticeProb.Analysis.Sobolev.TestFnApprox
import LatticeProb.Analysis.Sobolev.BandLimitedLip

open MeasureTheory Filter Set
open scoped ENNReal FourierTransform Topology SchwartzMap

namespace LatticeProb.Sobolev

/-- **The convolution theorem for the `ℂ`-valued Fourier transform.**  For integrable
`u v : Space d → ℂ`, `𝓕 (u ⋆ v) = 𝓕 u * 𝓕 v`.  This is Mathlib's
`Real.fourier_mul_convolution_eq`; it is the missing input named in the header of
`TestFnApprox.lean`, and it turns the mollification error `u - χ_ε * u` into the factor form
`𝓕 u * (1 - 𝓕 χ_ε)` consumed by `tendsto_sobolevNormSq_of_fourier_factor`. -/
theorem fourier_convolution_lift {d : ℕ} (u v : Space d → ℂ) (hu : Integrable u)
    (hv : Integrable v) :
    𝓕 (convolution u v (ContinuousLinearMap.mul ℂ ℂ) volume) = 𝓕 u * 𝓕 v :=
  funext fun ξ => Real.fourier_mul_convolution_eq hu hv ξ

/-- **The density theorem, fully reduced.**  Let `u` have finite `H^s` norm and let `w n` be a
family of mollification errors with
`𝓕 (lift (w n)) = 𝓕 (lift u) · c n`, `‖c n‖ ≤ 1`, `c n ξ → 0` at every `ξ`, and `u - w n` a test
function on `D`.  Then `u` is approximated in `H^s` by test functions on `D`.

This is the content of `BandLimitedTestFnApprox` with the two construction steps isolated: the
factor identity `hid` is discharged by `fourier_convolution_lift` for `w n = u - χ_n * u` with
`c n = 1 - 𝓕 χ_n`, and `hw` is the compact support of `u - χ_n * u` inside `D`; both are left as
hypotheses here, since the approximate identity `χ_n` itself is not packaged in Mathlib. -/
theorem exists_testFn_approx_of_fourier_tendsto {d : ℕ} {D : Set (Space d)}
    {u : Space d → ℝ} {s : ℝ} (hu : sobolevNormSq d s u < ⊤)
    (w : ℕ → Space d → ℝ) (hw : ∀ n, IsTestFn D (fun x => u x - w n x))
    (c : ℕ → Space d → ℂ)
    (hid : ∀ n ξ, 𝓕 (fun x => (w n x : ℂ)) ξ = 𝓕 (fun x => (u x : ℂ)) ξ * c n ξ)
    (hF : ∀ n, AEMeasurable (fun ξ => ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s *
        (‖𝓕 (fun x => (u x : ℂ)) ξ‖ * ‖c n ξ‖) ^ 2)) volume)
    (hbound : ∀ n ξ, ‖c n ξ‖ ≤ 1)
    (hcv : ∀ ξ, Tendsto (fun n => c n ξ) atTop (𝓝 0))
    {η : ℝ} (hη : 0 < η) :
    ∃ ψ : Space d → ℝ, IsTestFn D ψ ∧
      sobolevNormSq d s (fun x => u x - ψ x) ≤ ENNReal.ofReal η := by
  have ht := tendsto_sobolevNormSq_of_fourier_factor hu hid hF hbound hcv
  have hlt : ∀ᶠ n in atTop, sobolevNormSq d s (w n) < ENNReal.ofReal η :=
    (tendsto_order.1 ht).2 (ENNReal.ofReal η) (ENNReal.ofReal_pos.mpr hη)
  obtain ⟨n, hn⟩ := hlt.exists
  refine ⟨fun x => u x - w n x, hw n, ?_⟩
  have hfun : (fun x => u x - (fun x => u x - w n x) x) = w n := by
    funext x; ring
  rw [hfun]
  exact le_of_lt hn

/-- The real low-frequency projection `bandProj` packaged as a bounded continuous function on
`Space d`.  This is the first half of the Arzelà–Ascoli packaging: the net lemma
`exists_finite_supNet_of_uniformLip` consumes a `Set (BoundedContinuousFunction α ℝ)`, and the
family of projections has to be delivered in that type. -/
noncomputable def bandProjBCF {d : ℕ} (Λ : ℝ) (hΛ : 0 < Λ) (φ : Space d → ℝ)
    (hcont : ContDiff ℝ (⊤ : ℕ∞) φ) (hcs : HasCompactSupport φ) :
    BoundedContinuousFunction (Space d) ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (bandProj d Λ hΛ.ne' φ hcont hcs)
    (by
      have h : Continuous fun x =>
          (bandTrunc d Λ hΛ.ne' (realToComplexSchwartz d φ hcont hcs) x).re :=
        Complex.continuous_re.comp
          (bandTrunc d Λ hΛ.ne' (realToComplexSchwartz d φ hcont hcs)).continuous
      exact h)
    ‖(bandTrunc d Λ hΛ.ne' (realToComplexSchwartz d φ hcont hcs)).toBoundedContinuousFunction‖
    (by
      intro x
      rw [Real.norm_eq_abs]
      set F : 𝓢(Space d, ℂ) :=
        bandTrunc d Λ hΛ.ne' (realToComplexSchwartz d φ hcont hcs) with hF
      calc |bandProj d Λ hΛ.ne' φ hcont hcs x|
          = |(F x).re| := by rw [bandProj, ← hF]
        _ ≤ ‖F x‖ := Complex.abs_re_le_norm _
        _ = ‖F.toBoundedContinuousFunction x‖ := by
            rw [SchwartzMap.toBoundedContinuousFunction_apply]
        _ ≤ ‖F.toBoundedContinuousFunction‖ := BoundedContinuousFunction.norm_coe_le_norm _ x)

/-- The packaged projection agrees with `bandProj` pointwise. -/
@[simp] theorem bandProjBCF_apply {d : ℕ} (Λ : ℝ) (hΛ : 0 < Λ) (φ : Space d → ℝ)
    (hcont : ContDiff ℝ (⊤ : ℕ∞) φ) (hcs : HasCompactSupport φ) (x : Space d) :
    bandProjBCF Λ hΛ φ hcont hcs x = bandProj d Λ hΛ.ne' φ hcont hcs x := rfl

/-- **The packaged family is uniformly Lipschitz.**  The bound of
`exists_uniform_lipschitz_bandTrunc` transfers to the `BoundedContinuousFunction` packaging; this
is the `hlip` hypothesis of `exists_finite_supNet_of_uniformLip`. -/
theorem dist_bandProjBCF_le {d : ℕ} {s : ℝ} (hs : 0 ≤ s) {Λ : ℝ} (hΛ : 0 < Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : Space d → ℝ) (hcont : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hcs : HasCompactSupport φ), sobolevNormSq d s φ ≤ 1 →
      ∀ x y : Space d,
        dist (bandProjBCF Λ hΛ φ hcont hcs x) (bandProjBCF Λ hΛ φ hcont hcs y)
          ≤ C * dist x y := by
  obtain ⟨C, hCpos, hC⟩ := exists_uniform_lipschitz_bandTrunc (d := d) Λ hΛ hs
  refine ⟨C, hCpos.le, fun φ hcont hcs hφ x y => ?_⟩
  have h := hC φ hcont hcs x y hφ
  have hre : dist (bandProjBCF Λ hΛ φ hcont hcs x) (bandProjBCF Λ hΛ φ hcont hcs y)
      ≤ dist (bandTrunc d Λ hΛ.ne' (realToComplexSchwartz d φ hcont hcs) x)
          (bandTrunc d Λ hΛ.ne' (realToComplexSchwartz d φ hcont hcs) y) := by
    rw [bandProjBCF_apply, bandProjBCF_apply, bandProj, bandProj, Real.dist_eq,
      Complex.dist_eq, ← Complex.sub_re]
    exact Complex.abs_re_le_norm _
  exact hre.trans h

end LatticeProb.Sobolev
