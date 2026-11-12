import LatticeProb.LQG.MatingOfTreesCouplingSegments

/-!
# Cell-size functionals of a mating-of-trees coupling

The cell moments of a mating-of-trees coupling are integrals of suprema over uncountably many
parameters. A supremum over a Borel set of parameters of a jointly measurable function has analytic
strict superlevel sets, so it is almost everywhere measurable for every finite Borel measure on a
Polish space; this is enough to transfer the integrals through the law of the curve.

* `MeasureTheory.aemeasurable_biSup_of_measurable_uncurry`;
* `ContinuousMap.measurable_diam_image`: `f ↦ diam (f '' K)` is measurable for compact nonempty `K`;
* `measurable_uncurry_diamAreaRatio`, `aemeasurable_diamAreaSup`: the supremum over `s ∈ [0, 1]` of
  `diam (c([s - 1, s]))² / |c([s - 1, s])|`;
* `IsCouplingData.lintegral_diamAreaSup_rpow_of_map_eq`, `IsCouplingData.diamAreaSup_moments_of_map_eq`:
  the first cell-moment clause of a mating-of-trees coupling holds for every measurable random
  element of the data space with the law of a coupling.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace MeasureTheory

/-- A supremum over a Borel set of parameters of a jointly measurable `ℝ≥0∞`-valued function is
almost everywhere measurable for every finite measure on a Polish space: its strict superlevel sets
are projections of Borel sets, hence analytic, hence null-measurable. -/
theorem aemeasurable_biSup_of_measurable_uncurry {X Y : Type*} [TopologicalSpace X]
    [PolishSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y] [PolishSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] {f : X → Y → ℝ≥0∞} (hf : Measurable (Function.uncurry f))
    {K : Set Y} (hK : MeasurableSet K) (μ : Measure X) [IsFiniteMeasure μ] :
    AEMeasurable (fun x => ⨆ y ∈ K, f x y) μ := by
  refine NullMeasurable.aemeasurable ?_
  refine measurable_of_Ioi fun t => ?_
  have hset : (fun x => ⨆ y ∈ K, f x y) ⁻¹' Ioi t =
      Prod.fst '' {p : X × Y | p.2 ∈ K ∧ t < f p.1 p.2} := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, hlt⟩ := lt_biSup_iff.1 (show t < ⨆ y ∈ K, f x y from hx)
      exact ⟨(x, y), ⟨hy, hlt⟩, rfl⟩
    · rintro ⟨⟨x', y⟩, ⟨hy, hlt⟩, rfl⟩
      exact lt_biSup_iff.2 ⟨y, hy, hlt⟩
  have hA : AnalyticSet ((fun x => ⨆ y ∈ K, f x y) ⁻¹' Ioi t) := by
    rw [hset]
    exact ((measurable_snd hK).inter (measurableSet_lt measurable_const hf)).analyticSet
      |>.image_of_continuous continuous_fst
  exact LatticeProb.AnalyticSet.nullMeasurableSet μ hA

end MeasureTheory

namespace ContinuousMap

/-- For compact nonempty `K ⊆ ℝ`, the diameter of the image of `K` is a measurable function of the
curve. -/
theorem measurable_diam_image {E : Type*} [PseudoMetricSpace E] {K : Set ℝ} (hK : IsCompact K)
    (hne : K.Nonempty) : Measurable fun f : C(ℝ, E) => diam (f '' K) :=
  measurable_of_Ici fun _ => ((isClosed_setOf_le_diam_image hK hne).preimage
    (continuous_id.prodMk continuous_const)).measurableSet

end ContinuousMap

namespace MatedCRTHarmonic

namespace MatedCRT

open ContinuousMap

/-- The ratio `diam (c([s - 1, s]))² / |c([s - 1, s])|` is jointly measurable in the curve and `s`. -/
theorem measurable_uncurry_diamAreaRatio :
    Measurable (Function.uncurry fun (c : C(ℝ, ℂ)) (s : ℝ) =>
      ENNReal.ofReal (diam (c '' Icc (s - 1) s) ^ 2) / volume (c '' Icc (s - 1) s)) := by
  have hG : Continuous fun p : C(ℝ, ℂ) × ℝ => segmentReparam (p.1, p.2 - 1, p.2) :=
    segmentReparam.continuous.comp
      (continuous_fst.prodMk ((continuous_snd.sub continuous_const).prodMk continuous_snd))
  have heq : (Function.uncurry fun (c : C(ℝ, ℂ)) (s : ℝ) =>
      ENNReal.ofReal (diam (c '' Icc (s - 1) s) ^ 2) / volume (c '' Icc (s - 1) s)) =
      fun p : C(ℝ, ℂ) × ℝ =>
        ENNReal.ofReal (diam (segmentReparam (p.1, p.2 - 1, p.2) '' Icc 0 1) ^ 2) /
          volume (segmentReparam (p.1, p.2 - 1, p.2) '' Icc 0 1) := by
    funext p
    obtain ⟨c, s⟩ := p
    simp only [Function.uncurry_apply_pair]
    rw [segmentReparam_image_Icc c (by linarith : s - 1 ≤ s)]
  rw [heq]
  have hd := measurable_diam_image (E := ℂ) isCompact_Icc (nonempty_Icc.2 (zero_le_one' ℝ))
  exact ((ENNReal.measurable_ofReal.comp (hd.pow_const 2)).comp hG.measurable).div
    ((measurable_measure_image volume isCompact_Icc).comp hG.measurable)

/-- The supremum `diamAreaSup` is almost everywhere measurable for every finite Borel measure on
`C(ℝ, ℂ)`. -/
theorem aemeasurable_diamAreaSup (μ : Measure C(ℝ, ℂ)) [IsFiniteMeasure μ] :
    AEMeasurable diamAreaSup μ := by
  have : PolishSpace C(ℝ, ℂ) := LQGMetric.polishSpace_continuousMap ℝ ℂ
  show AEMeasurable (fun c : C(ℝ, ℂ) => ⨆ s ∈ Icc (0 : ℝ) 1,
    ENNReal.ofReal (diam (c '' Icc (s - 1) s) ^ 2) / volume (c '' Icc (s - 1) s)) μ
  exact aemeasurable_biSup_of_measurable_uncurry measurable_uncurry_diamAreaRatio measurableSet_Icc μ

variable {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
  {γ : ℝ} {V : Ω → CouplingData} {V' : Ω' → CouplingData}

open CouplingData

/-- The moments of `diamAreaSup` of the curve `η₀` agree for two measurable random elements of the
data space with the same law under a finite measure. -/
theorem lintegral_diamAreaSup_rpow_of_map_eq [IsFiniteMeasure P] (hV : Measurable V)
    (hV' : Measurable V') (hlaw : P'.map V' = P.map V) (p : ℝ) :
    ∫⁻ ω, diamAreaSup (V' ω).η₀ ^ p ∂P' = ∫⁻ ω, diamAreaSup (V ω).η₀ ^ p ∂P := by
  have hlaw₀ : P'.map (fun ω => (V' ω).η₀) = P.map (fun ω => (V ω).η₀) :=
    map_comp_of_map_eq hV hV' hlaw measurable_η₀
  exact lintegral_comp_of_map_eq (F := fun c => diamAreaSup c ^ p) (measurable_η₀.comp hV)
    (measurable_η₀.comp hV') hlaw₀ ((aemeasurable_diamAreaSup _).pow_const p)

/-- The first cell-moment clause (finite moments of `diamAreaSup` of `η₀`) holds for a measurable
random element of the data space with the law of a coupling. -/
theorem IsCouplingData.diamAreaSup_moments_of_map_eq (hC : IsCouplingData γ P V)
    (hV : Measurable V) (hV' : Measurable V') (hlaw : P'.map V' = P.map V) :
    ∀ p : ℝ, 1 ≤ p → ∫⁻ ω, diamAreaSup (V' ω).η₀ ^ p ∂P' < ⊤ := by
  have hCP := (show IsMatingOfTreesCoupling _ _ _ _ _ _ _ _ _ _ _ _ _ _ from hC)
  have := hCP.isProbabilityMeasure
  intro p hp
  rw [lintegral_diamAreaSup_rpow_of_map_eq hV hV' hlaw p]
  exact hCP.cellMoments.1 p hp

end MatedCRT

end MatedCRTHarmonic

end
