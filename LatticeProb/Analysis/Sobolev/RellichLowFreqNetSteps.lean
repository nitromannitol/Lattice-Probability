/-
# The low-frequency net residual, reduced to its named sub-pieces

`rkLowFreqNet` (`RellichLowFreqNet.lean`) is the corrected low-frequency compactness
step of the Rellich–Kondrachov argument: the low-frequency part of the `H^s(D)`
unit ball is covered by finitely many `H^{s₀}`-balls with test-function centres.
This file isolates its genuinely open analytic content as the single named
proposition `rkLowFreqCmNet` and proves the bounded conversions around it.

## The decomposition

`rkLowFreqCmNet` is the `C^m` form of the residual: the same low-frequency set
admits, for every order `m` and accuracy `ε`, a finite `C^m`-net with centres that
are test functions on `D`.  It bundles the analytic inputs the classical proof
needs and that Mathlib does not supply:

* a frequency-truncation operator `P_Λ` whose low-frequency part is an honest
  band-limited function;
* the band-limited Bernstein / `H^s → C^m` bound, uniformly over the low-frequency
  set;
* Arzelà–Ascoli, turning that uniform bound into a finite `C^m`-net; and
* the support/mollification repair, replacing the non-compactly-supported
  band-limited centres by test functions on `D`.  The algebraic core of that
  repair is already proved: `sobolevNormSq_sub_convolution_le_of_fourier_close`
  (`RellichMollify.lean`) bounds the mollification error by `c²` times the `H^s`
  norm once the kernel is `c`-close to `1` in the Fourier sense.  What is missing
  is the scaled-kernel limit `c(Λ) → 0` and the band-limited concentration that
  lets a cutoff supported in `D` be inserted.

## What is reduced here

* `sobolevNormSqLow_le_sobolevNormSq`: for `s₀ ≤ s` the low-frequency part of the
  `H^{s₀}` norm is at most the full `H^s` norm, so the low-frequency set is
  `H^{s₀}`-bounded.
* `sobolevNormSq_le_of_lowFreq`: consequently a low-frequency test function in the
  `H^s` unit ball has `H^{s₀}` norm at most `1 + δ/2`.
* `rkLowFreqNet_of_rkLowFreqCmNet`: the quantitative Fourier-decay residual
  `rkResidual_diff_bound` (`RellichNet.lean`) converts the `C^m`-net into the
  `H^{s₀}`-net of `rkLowFreqNet`, at the same centres.
* `rkLowFrequencyStatement_of_rkLowFreqCmNet` and
  `rellichKondrachov_of_rkLowFreqCmNet`: the composition with the existing glue
  (`rkLowFrequencyStatement_of_rkLowFreqNet`, `rellichKondrachovNegSobolev_of_lowfreqNet`).

Nothing here is frozen or registered; this is a separate reduction beside
`RellichLowFreqNet.lean`.
-/
import LatticeProb.Analysis.Sobolev.RellichLowFreqNet
import LatticeProb.Analysis.Sobolev.RellichNet
import LatticeProb.Analysis.Sobolev.RellichMollify

open MeasureTheory
open scoped ENNReal FourierTransform

namespace LatticeProb.Sobolev

/-- **The low-frequency `C^m`-net residual** (the single genuinely open input).
For a bounded domain `D`, orders `s₀ < s`, a cutoff `Λ ≥ 0`, an accuracy `δ > 0`,
an order `m` and a `C^m` accuracy `ε > 0`, the set of test functions on `D` whose
`H^s` norm is at most `1` and whose high-frequency `H^{s₀}` content is at most
`δ/2` is covered by finitely many `ε`-balls in the `C^m` norm, with centres that
are test functions on `D`.

This is the corrected, low-frequency form of `rkBandLimitedCmNet`: it does not
claim a `C^m`-net for the whole `H^s` unit ball (which is false), only for the part
whose high frequencies are already small.  It is where the frequency-truncation
operator, the band-limited Bernstein bound, Arzelà–Ascoli and the
support/mollification repair are needed. -/
def rkLowFreqCmNet : Prop :=
  ∀ (d : ℕ) (D : Set (Space d)), IsDomain D → ∀ (s₀ s : ℝ), s₀ < s →
    ∀ Λ : ℝ, 0 ≤ Λ → ∀ δ : ℝ, 0 < δ →
      ∀ (m : ℕ) (ε : ℝ), 0 < ε →
        ∃ (N : ℕ) (ψ : Fin N → Space d → ℝ),
          (∀ i, IsTestFn D (ψ i)) ∧
          ∀ φ : Space d → ℝ, IsTestFn D φ → sobolevNormSq d s φ ≤ 1 →
            sobolevNormSqHigh d s₀ Λ φ ≤ ENNReal.ofReal (δ / 2) →
              ∃ i, ∀ k ≤ m, ∀ x : Space d,
                ‖iteratedFDeriv ℝ k (fun x => φ x - ψ i x) x‖ ≤ ε

/-! ### Bounded supporting lemmas -/

/-- **The low-frequency part is dominated by the full higher-order norm.**  For
`s₀ ≤ s` the weight `(1 + (2π‖ξ‖)²)^{s₀}` is at most `(1 + (2π‖ξ‖)²)^s`, so the
low-frequency integral at `s₀` is at most the full `H^s` norm. -/
theorem sobolevNormSqLow_le_sobolevNormSq {d : ℕ} {s₀ s Λ : ℝ} (hss : s₀ ≤ s)
    (φ : Space d → ℝ) :
    sobolevNormSqLow d s₀ Λ φ ≤ sobolevNormSq d s φ := by
  have hpoint : ∀ ξ : Space d,
      ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s₀
          * ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2)
        ≤ ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s
          * ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2) := by
    intro ξ
    refine ENNReal.ofReal_le_ofReal ?_
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    exact Real.rpow_le_rpow_of_exponent_le
      (le_add_of_nonneg_right (sq_nonneg _)) hss
  unfold sobolevNormSqLow sobolevNormSq
  calc ∫⁻ ξ in {ξ : Space d | Λ < ‖ξ‖}ᶜ,
        ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s₀
          * ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2)
      ≤ ∫⁻ ξ in {ξ : Space d | Λ < ‖ξ‖}ᶜ,
          ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s
            * ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2) :=
        lintegral_mono hpoint
    _ ≤ ∫⁻ ξ : Space d,
          ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s
            * ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2) := by
        simpa using lintegral_mono_set (μ := volume)
          (f := fun ξ : Space d => ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s
            * ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2))
          (Set.subset_univ ({ξ : Space d | Λ < ‖ξ‖}ᶜ))

/-- **The low-frequency set is `H^{s₀}`-bounded.**  A test function in the `H^s`
unit ball whose high-frequency `H^{s₀}` content is at most `δ/2` has `H^{s₀}` norm
at most `1 + δ/2`: the low-frequency part is at most the full `H^s` norm
(`sobolevNormSqLow_le_sobolevNormSq`) and the parts add up. -/
theorem sobolevNormSq_le_of_lowFreq {d : ℕ} {s₀ s Λ δ : ℝ} (hss : s₀ ≤ s)
    {φ : Space d → ℝ} (hφ : sobolevNormSq d s φ ≤ 1)
    (hhigh : sobolevNormSqHigh d s₀ Λ φ ≤ ENNReal.ofReal (δ / 2)) :
    sobolevNormSq d s₀ φ ≤ 1 + ENNReal.ofReal (δ / 2) := by
  calc sobolevNormSq d s₀ φ
      = sobolevNormSqLow d s₀ Λ φ + sobolevNormSqHigh d s₀ Λ φ :=
        (sobolevNormSqLow_add_high d s₀ Λ φ).symm
    _ ≤ sobolevNormSq d s φ + ENNReal.ofReal (δ / 2) :=
        add_le_add (sobolevNormSqLow_le_sobolevNormSq hss φ) hhigh
    _ ≤ 1 + ENNReal.ofReal (δ / 2) := add_le_add hφ le_rfl

/-! ### The reductions -/

/-- **The `C^m`-net gives the low-frequency net.**  Choose `m` and `C` from the
quantitative Fourier-decay residual `rkResidual_diff_bound` on the compact
`closure D`, take the `C^m`-net at accuracy `ε = √(δ/(C+1))` so that `C ε² ≤ δ`,
and convert it back to `sobolevNormSq d s₀` closeness with the residual.  This is
the same conversion as the false `rkBandLimitedCmNet` reduction, applied to the
corrected low-frequency hypothesis. -/
theorem rkLowFreqNet_of_rkLowFreqCmNet (h : rkLowFreqCmNet) : rkLowFreqNet := by
  intro d D hD s₀ s hss Λ hΛ δ hδ
  have hbdd : Bornology.IsBounded D := hD.2.1
  obtain ⟨m, C, hC0, hres⟩ :=
    rkResidual_diff_bound (d := d) (K := closure D) hbdd.isCompact_closure s₀
  have hCp1 : (0 : ℝ) < C + 1 := by linarith
  set ε : ℝ := Real.sqrt (δ / (C + 1)) with hεdef
  have hεpos : 0 < ε := Real.sqrt_pos_of_pos (by positivity)
  have hεδ : C * ε ^ 2 ≤ δ := by
    have h1 : ε ^ 2 = δ / (C + 1) := by
      rw [hεdef, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ δ / (C + 1))]
    rw [h1]
    have h2 : C * (δ / (C + 1)) = δ * (C / (C + 1)) := by ring
    rw [h2]
    have h3 : C / (C + 1) ≤ 1 := by
      rw [div_le_one hCp1]
      linarith
    calc δ * (C / (C + 1)) ≤ δ * 1 := mul_le_mul_of_nonneg_left h3 hδ.le
      _ = δ := mul_one _
  obtain ⟨N, ψ, hψ, hnet⟩ := h d D hD s₀ s hss Λ hΛ δ hδ m ε hεpos
  refine ⟨N, ψ, hψ, fun φ hφ hφn hφhigh => ?_⟩
  obtain ⟨i, hi⟩ := hnet φ hφ hφn hφhigh
  refine ⟨i, ?_⟩
  have hsub : tsupport (fun x => φ x - ψ i x) ⊆ closure D :=
    (tsupport_sub φ (ψ i)).trans
      ((Set.union_subset hφ.2.2 (hψ i).2.2).trans subset_closure)
  have hdiff : ContDiff ℝ (⊤ : ℕ∞) (fun x => φ x - ψ i x) := hφ.1.sub (hψ i).1
  exact (hres (fun x => φ x - ψ i x) hdiff hsub ε hεpos hi).trans
    (ENNReal.ofReal_le_ofReal hεδ)

/-- The low-frequency net residual implies the internal finite-net statement,
through `rkLowFreqNet`. -/
theorem rkLowFrequencyStatement_of_rkLowFreqCmNet (h : rkLowFreqCmNet) :
    rkLowFrequencyStatement :=
  rkLowFrequencyStatement_of_rkLowFreqNet (rkLowFreqNet_of_rkLowFreqCmNet h)

/-- The external `LatticeProb.External.RellichKondrachovNegSobolev` from a producer
of the low-frequency `C^m`-net. -/
theorem rellichKondrachov_of_rkLowFreqCmNet (h : rkLowFreqCmNet) :
    LatticeProb.External.RellichKondrachovNegSobolev :=
  rellichKondrachovNegSobolev_of_lowfreqNet (rkLowFreqNet_of_rkLowFreqCmNet h)

end LatticeProb.Sobolev
