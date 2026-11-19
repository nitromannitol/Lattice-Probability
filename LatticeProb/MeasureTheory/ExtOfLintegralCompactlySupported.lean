import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.NNReal
import Mathlib.Topology.UrysohnsLemma

/-!
# Measures determined by integrals of continuous compactly supported functions

Let `X` be a locally compact, σ-compact, pseudo-metrizable Hausdorff space with its Borel σ-algebra, and
let `μ` be a locally finite measure on `X`. A second measure `ν` is NOT assumed to be locally finite.

* `isLocallyFiniteMeasure_of_lintegral_le_of_hasCompactSupport`: if `∫⁻ f ∂ν ≤ ∫⁻ f ∂μ` for every
  continuous compactly supported `f : X → ℝ≥0`, then `ν` is locally finite. Each point has a compact
  neighbourhood `K`, and an Urysohn function `f` with `f = 1` on `K` and values in `[0, 1]` gives
  `ν K ≤ ∫⁻ f ∂ν ≤ ∫⁻ f ∂μ ≤ μ (tsupport f) < ∞`.
* `ext_of_lintegral_eq_of_hasCompactSupport`: if `∫⁻ f ∂ν = ∫⁻ f ∂μ` for every continuous compactly
  supported `f : X → ℝ≥0`, then `ν = μ`. Both measures are then locally finite, hence regular, and the
  uniqueness half of the Riesz–Markov–Kakutani theorem applies.
* `ext_of_lintegral_ofReal_eq_of_hasCompactSupport`: the same with real-valued `f ≥ 0` and
  `ENNReal.ofReal`.

The lower Lebesgue integral is essential in the hypotheses: with Bochner integrals the statement fails
for `ν = ∞ • volume`, whose Bochner integrals of nonzero `f ≥ 0` all vanish (non-integrable integrands).
-/

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal

namespace LatticeProb

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [PseudoMetrizableSpace X]
  [MeasurableSpace X] [BorelSpace X]

/-- A measure whose lower integrals of continuous compactly supported functions `f ≥ 0` are bounded by
those of a locally finite measure is locally finite. -/
theorem isLocallyFiniteMeasure_of_lintegral_le_of_hasCompactSupport {μ ν : Measure X}
    [IsLocallyFiniteMeasure μ]
    (h : ∀ f : X → ℝ≥0, Continuous f → HasCompactSupport f →
      ∫⁻ x, (f x : ℝ≥0∞) ∂ν ≤ ∫⁻ x, (f x : ℝ≥0∞) ∂μ) :
    IsLocallyFiniteMeasure ν := by
  refine ⟨fun x => ?_⟩
  obtain ⟨K, hKc, hKx⟩ := exists_compact_mem_nhds x
  obtain ⟨f, hf1, -, hfc, hf01⟩ :=
    exists_continuous_one_zero_of_isCompact hKc isClosed_empty (disjoint_empty K)
  set g : X → ℝ≥0 := fun y => Real.toNNReal (f y) with hg_def
  have hg : Continuous g := continuous_real_toNNReal.comp f.continuous
  have hgc : HasCompactSupport g := hfc.comp_left Real.toNNReal_zero
  have hg1 : ∀ y, (g y : ℝ≥0∞) ≤ 1 := fun y => by
    rw [ENNReal.coe_le_one_iff, hg_def, Real.toNNReal_le_one]
    exact (hf01 y).2
  have hS : MeasurableSet {y | (1 : ℝ≥0) ≤ g y} :=
    (isClosed_le continuous_const hg).measurableSet
  refine ⟨K, hKx, ?_⟩
  calc ν K ≤ ν {y | (1 : ℝ≥0) ≤ g y} := measure_mono fun y hy =>
        show (1 : ℝ≥0) ≤ g y by simp [hg_def, hf1 hy]
    _ = ∫⁻ y, {y | (1 : ℝ≥0) ≤ g y}.indicator 1 y ∂ν := (lintegral_indicator_one hS).symm
    _ ≤ ∫⁻ y, (g y : ℝ≥0∞) ∂ν := lintegral_mono fun y => by
        by_cases hy : (1 : ℝ≥0) ≤ g y
        · rw [indicator_of_mem (show y ∈ {y | (1 : ℝ≥0) ≤ g y} from hy), Pi.one_apply]
          exact ENNReal.one_le_coe_iff.2 hy
        · rw [indicator_of_notMem (show y ∉ {y | (1 : ℝ≥0) ≤ g y} from hy)]
          exact zero_le
    _ ≤ ∫⁻ y, (g y : ℝ≥0∞) ∂μ := h g hg hgc
    _ ≤ ∫⁻ y, (tsupport g).indicator 1 y ∂μ := lintegral_mono fun y => by
        by_cases hy : y ∈ tsupport g
        · rw [indicator_of_mem hy, Pi.one_apply]
          exact hg1 y
        · rw [image_eq_zero_of_notMem_tsupport hy, ENNReal.coe_zero]
          exact zero_le
    _ = μ (tsupport g) := lintegral_indicator_one (isClosed_tsupport g).measurableSet
    _ < ⊤ := hgc.isCompact.measure_lt_top

variable [T2Space X] [SigmaCompactSpace X]

/-- Two measures, one of them locally finite, with the same lower integrals of all continuous compactly
supported functions `f ≥ 0` are equal. -/
theorem ext_of_lintegral_eq_of_hasCompactSupport {μ ν : Measure X} [IsLocallyFiniteMeasure μ]
    (h : ∀ f : X → ℝ≥0, Continuous f → HasCompactSupport f →
      ∫⁻ x, (f x : ℝ≥0∞) ∂ν = ∫⁻ x, (f x : ℝ≥0∞) ∂μ) :
    ν = μ := by
  have : IsLocallyFiniteMeasure ν :=
    isLocallyFiniteMeasure_of_lintegral_le_of_hasCompactSupport (μ := μ)
      fun f hf hfc => (h f hf hfc).le
  refine Measure.ext_of_integral_eq_on_compactlySupported_nnreal fun f => ?_
  have key : ∀ m : Measure X, ∫ x, (f x : ℝ) ∂m = (∫⁻ x, (f x : ℝ≥0∞) ∂m).toReal := fun m => by
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun x => (f x : ℝ))
      (Eventually.of_forall fun x => NNReal.coe_nonneg (f x))
      (map_continuous f).measurable.coe_nnreal_real.aestronglyMeasurable]
    simp_rw [ENNReal.ofReal_coe_nnreal]
  rw [key, key, h f (map_continuous f) f.hasCompactSupport]

/-- Real-valued form of `ext_of_lintegral_eq_of_hasCompactSupport`: two measures, one of them locally
finite, with the same lower integrals `∫⁻ ENNReal.ofReal ∘ f` of all continuous compactly supported
`f : X → ℝ` with `0 ≤ f` are equal. -/
theorem ext_of_lintegral_ofReal_eq_of_hasCompactSupport {μ ν : Measure X} [IsLocallyFiniteMeasure μ]
    (h : ∀ f : X → ℝ, Continuous f → HasCompactSupport f → 0 ≤ f →
      ∫⁻ x, ENNReal.ofReal (f x) ∂ν = ∫⁻ x, ENNReal.ofReal (f x) ∂μ) :
    ν = μ :=
  ext_of_lintegral_eq_of_hasCompactSupport fun f hf hfc => by
    have := h (fun x => (f x : ℝ)) (NNReal.continuous_coe.comp hf)
      (hfc.comp_left NNReal.coe_zero) (fun x => (f x).2)
    simpa only [ENNReal.ofReal_coe_nnreal] using this

end LatticeProb
