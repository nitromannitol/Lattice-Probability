/-
# Fréchet–Kolmogorov precompactness for the `H^s` unit ball of test functions

The support-repair residuals `BandLimitedTestFnApproxOnDomain` and `BandCentreSupportRepair` are
false (`LatticeProbAudit/RELLICH-LOWFREQ-SUPPORT-REPAIR.md`, `f73b92a`).  This module replaces them
with the **sound** low-frequency residual `BandLimitedPrecompact`, which approximates the test
function `φ` itself:

  `∀ φ, IsTestFn D φ → sobolevNormSq d s φ ≤ 1 →
      ∃ i, sobolevNormSq d s₀ (fun x => φ x - ψ i x) ≤ ofReal δ`,

and assembles it from the classical Fréchet–Kolmogorov compactness input:

* `FrechetKolmogorovH` — bounded + tight + uniformly translation-continuous `⟹` a finite
  net with
  centres in the family (this is the classical theorem, stated as a sound input);
* `BandLimitedTranslationContinuous` — the uniform translation-continuity of the `H^s` unit ball,
  the quantitative half opened by `TranslationContinuity.lean` (`fourier_comp_add_right_lift`);
* `bandLimitedPrecompact_of_frechetKolmogorov` — the assembly, using boundedness
  (`sobolevNormSq d s₀ ≤ sobolevNormSq d s` for `s₀ ≤ s`) and tightness
  (`tsupport φ ⊆ closure D`);
* `rkLowFreqNet_of_bandLimitedPrecompact` — the sound glue to `rkLowFreqNet`.
-/
import LatticeProb.Analysis.Sobolev.TranslationContinuity
import LatticeProb.Analysis.Sobolev.RellichLowFreqNet
import LatticeProb.Analysis.Sobolev.Basic

open MeasureTheory Filter Set
open scoped ENNReal FourierTransform Topology

namespace LatticeProb.Sobolev

/-- **The sound low-frequency residual.**  The `H^s` unit ball of test functions on `D` admits, for
every accuracy, a finite net of test functions on `D` in the `H^{s₀}` norm (`s₀ < s`).  This
is the
genuine Rellich–Kondrachov precompactness of `C_c^∞(D)`, replacing the false
`BandLimitedTestFnApproxOnDomain` (which demanded approximation of the *projection*). -/
def BandLimitedPrecompact : Prop :=
  ∀ (d : ℕ) (D : Set (Space d)), IsDomain D → ∀ (s₀ s : ℝ), s₀ < s →
    ∀ δ : ℝ, 0 < δ →
      ∃ (N : ℕ) (ψ : Fin N → Space d → ℝ), (∀ i, IsTestFn D (ψ i)) ∧
        ∀ (φ : Space d → ℝ), IsTestFn D φ → sobolevNormSq d s φ ≤ 1 →
          ∃ i, sobolevNormSq d s₀ (fun x => φ x - ψ i x) ≤ ENNReal.ofReal δ

/-- **Fréchet–Kolmogorov, `H^s` form.**  A subset of `H^s` that is bounded, supported in a fixed
compact set, and uniformly translation-continuous is totally bounded, with centres in the family.
This is the classical compactness theorem, stated as a sound input. -/
def FrechetKolmogorovH : Prop :=
  ∀ (d : ℕ) (K : Set (Space d)), IsCompact K → ∀ (s : ℝ) (S : Set (Space d → ℝ)),
    (∀ f ∈ S, tsupport f ⊆ K) →
    (∃ C : ℝ, ∀ f ∈ S, sobolevNormSq d s f ≤ ENNReal.ofReal C) →
    (∀ (η : ℝ), 0 < η → ∃ (δ : ℝ), 0 < δ ∧ ∀ (h : Space d), ‖h‖ < δ →
      ∀ f ∈ S, sobolevNormSq d s (fun x => f (x + h) - f x) ≤ ENNReal.ofReal η) →
    ∀ δ : ℝ, 0 < δ →
      ∃ (N : ℕ) (g : Fin N → Space d → ℝ), (∀ i, g i ∈ S) ∧
        ∀ f ∈ S, ∃ i, sobolevNormSq d s (fun x => f x - g i x) ≤ ENNReal.ofReal δ

/-- **Uniform translation-continuity of the `H^s` unit ball.**  The quantitative half of the
Fréchet–Kolmogorov route, fed by `fourier_comp_add_right_lift`: for `s₀ < s` and every
`η > 0` there
is `δ > 0` with `sobolevNormSq d s₀ (φ(·+h) - φ) ≤ η` for every `‖h‖ < δ` and every
`H^s`-unit test
function `φ`. -/
def BandLimitedTranslationContinuous : Prop :=
  ∀ (d : ℕ) (D : Set (Space d)), IsDomain D → ∀ (s₀ s : ℝ), s₀ < s →
    ∀ (η : ℝ), 0 < η → ∃ (δ : ℝ), 0 < δ ∧ ∀ (h : Space d), ‖h‖ < δ →
      ∀ (φ : Space d → ℝ), IsTestFn D φ → sobolevNormSq d s φ ≤ 1 →
        sobolevNormSq d s₀ (fun x => φ (x + h) - φ x) ≤ ENNReal.ofReal η

/-- **The assembly.**  Boundedness (`sobolevNormSq d s₀ ≤ sobolevNormSq d s`), tightness
(`tsupport φ ⊆ closure D`, `D` bounded), and uniform translation-continuity feed the
Fréchet–Kolmogorov input, giving `BandLimitedPrecompact`. -/
theorem bandLimitedPrecompact_of_frechetKolmogorov (hFK : FrechetKolmogorovH)
    (htrans : BandLimitedTranslationContinuous) : BandLimitedPrecompact := by
  intro d D hD s₀ s hss δ hδ
  set S : Set (Space d → ℝ) := {f | IsTestFn D f ∧ sobolevNormSq d s f ≤ 1} with hSdef
  have ht : ∀ f ∈ S, tsupport f ⊆ closure D :=
    fun f hf => hf.1.2.2.trans subset_closure
  have hb : ∃ C : ℝ, ∀ f ∈ S, sobolevNormSq d s₀ f ≤ ENNReal.ofReal C :=
    ⟨1, fun f hf => (sobolevNormSq_mono hss.le f).trans (by simpa using hf.2)⟩
  have hc : ∀ (η : ℝ), 0 < η → ∃ (δ : ℝ), 0 < δ ∧ ∀ (h : Space d),
      ‖h‖ < δ →
      ∀ f ∈ S, sobolevNormSq d s₀ (fun x => f (x + h) - f x) ≤ ENNReal.ofReal η := by
    intro η hη
    obtain ⟨δ, hδ, hδ'⟩ := htrans d D hD s₀ s hss η hη
    exact ⟨δ, hδ, fun h hh f hf => hδ' h hh f hf.1 hf.2⟩
  obtain ⟨N, g, hgS, hcov⟩ :=
    hFK d (closure D) hD.2.1.isCompact_closure s₀ S ht hb hc δ hδ
  exact ⟨N, g, fun i => (hgS i).1, fun φ hφ hφs => hcov φ ⟨hφ, hφs⟩⟩

/-- **The sound glue.**  `BandLimitedPrecompact` discharges `rkLowFreqNet` (the high-frequency
hypothesis is not needed). -/
theorem rkLowFreqNet_of_bandLimitedPrecompact (h : BandLimitedPrecompact) : rkLowFreqNet := by
  intro d D hD s₀ s hss Λ hΛ δ hδ
  obtain ⟨N, ψ, hψ, hnet⟩ := h d D hD s₀ s hss δ hδ
  exact ⟨N, ψ, hψ, fun φ hφ hφs _ => hnet φ hφ hφs⟩

end LatticeProb.Sobolev
