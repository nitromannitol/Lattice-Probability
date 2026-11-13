import LatticeProb.LQG.MatingOfTreesCouplingIgMap

/-!
# The imaginary-geometry clause of a mating-of-trees coupling passes through the law

The `igMap` clause of a mating-of-trees coupling says that the space-filling curve `η_L` is a
measurable function `Φ` of the circle-average process `(ρ, w) ↦ h^IG_ρ(w) + U` of the shifted
imaginary geometry field, that `Φ` reads only the positive radii, that it satisfies the coordinate
change rule of imaginary geometry for the maps `w ↦ z₀ + s e^{iφ} w` (the curve re-rooted at its
hitting time of `z₀`), and that the excursion segments of the curve in a bounded open set `W` are
determined by the circle averages inside a `δ`-neighbourhood of `W` (locality).

This file shows that the whole clause passes from a coupling `V` to every measurable random element
`V'` of the data space with the same law (possibly on another probability space), given two facts
about continuous curves that do not involve the coupling: the re-rooted curve `affineReroot z₀ s φ c`
and the excursion segments `excursionSegment c W z` are measurable functions of the curve `c`.

* `ae_igPullback_eq_affineReroot_of_map_eq`: the coordinate-change rule passes, with the same `Φ`.
* `ae_excursionSegment_eq_of_map_eq`: the locality rule passes, with the witness `g` replaced by
  its dyadic regularization (an identity of functions of time is an event only through its values
  at dyadic times; continuity of the excursion segments recovers the rest).
* `IsCouplingData.igMap_of_map_eq`: the `igMap` clause of `V'`, in the form of the coupling.
-/

noncomputable section

open MeasureTheory Set Filter Topology Metric

namespace MatedCRTHarmonic
namespace MatedCRT

open CouplingData

variable {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
  {V : Ω → CouplingData} {V' : Ω' → CouplingData}

/-- **The coordinate-change rule passes through the law.** If almost surely
`Φ(ψ^*(h^IG + U)) = ψ⁻¹ ∘ η_L` re-rooted at the hitting time of `z₀ = ψ(0)`, for
`ψ w = z₀ + s e^{iφ} w` and a measurable `Φ`, the same holds for every random element of the data
space with the same law, provided the re-rooting is a measurable map of curves. -/
theorem ae_igPullback_eq_affineReroot_of_map_eq (hV : Measurable V) (hV' : Measurable V')
    (hlaw : P'.map V' = P.map V) {Φ : (ℝ → ℂ → ℝ) → C(ℝ, ℂ)} (hΦ : Measurable Φ) (γ : ℝ)
    (z₀ : ℂ) (s φ : ℝ) (hR : Measurable (affineReroot z₀ s φ))
    (h : ∀ᵐ ω ∂P, Φ (igPullback γ z₀ s φ (V ω).igCircleAvg) = affineReroot z₀ s φ (V ω).ηL) :
    ∀ᵐ ω ∂P', Φ (igPullback γ z₀ s φ (V' ω).igCircleAvg) = affineReroot z₀ s φ (V' ω).ηL :=
  ae_comp_of_map_eq hV hV' hlaw
    (measurableSet_eq_fun ((hΦ.comp (measurable_igPullback γ z₀ s φ)).comp measurable_igCircleAvg)
      (hR.comp measurable_ηL)) h

/-- **The locality rule passes through the law.** If almost surely the excursion segments of `η_L`
in `W` from the rational points of `W` are the values `g(h^IG + U |_{W_δ})` of a measurable family
`g` at the circle averages inside the `δ`-neighbourhood `W_δ` of `W`, then the same holds for every
random element of the data space with the same law, with `g` replaced by its dyadic
regularization, provided the excursion segments are measurable functions of the curve. -/
theorem ae_excursionSegment_eq_of_map_eq (hV : Measurable V) (hV' : Measurable V')
    (hlaw : P'.map V' = P.map V) {W : Set ℂ} (δ : ℝ)
    (hE : ∀ z : ℂ, Measurable fun c : C(ℝ, ℂ) => excursionSegment c W z)
    {g : (ℝ → ℂ → ℝ) → (ℚ × ℚ → ℝ → ℂ)} (hg : Measurable g)
    (h : ∀ᵐ ω ∂P, ∀ q : ℚ × ℚ, ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I) ∈ W →
      excursionSegment (V ω).ηL W ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I) =
        g (restrictCircles (thickening δ W) (V ω).igCircleAvg) q) :
    ∀ᵐ ω ∂P', ∀ q : ℚ × ℚ, ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I) ∈ W →
      excursionSegment (V' ω).ηL W ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I) =
        dyadicRegularize g (restrictCircles (thickening δ W) (V' ω).igCircleAvg) q := by
  let S : CouplingData → ℚ × ℚ → ℝ → ℂ := fun v q =>
    excursionSegment v.ηL W ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I)
  let G : CouplingData → ℝ → ℂ → ℝ := fun v => restrictCircles (thickening δ W) v.igCircleAvg
  have hS : ∀ (q : ℚ × ℚ) (u : ℝ), Measurable fun v => S v q u := fun q u =>
    ((measurable_pi_apply u).comp (hE ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I))).comp measurable_ηL
  have hSc : ∀ (v : CouplingData) (q : ℚ × ℚ), Continuous (S v q) := fun v q =>
    continuous_excursionSegment v.ηL W ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I)
  have hG : Measurable G := (measurable_restrictCircles _).comp measurable_igCircleAvg
  have h' : ∀ᵐ ω ∂P, ∀ q : ℚ × ℚ, ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I) ∈ W →
      S (V ω) q = g (G (V ω)) q := h
  exact ae_eq_dyadicRegularize_of_map_eq hV hV' hlaw hS hSc hG hg
    (fun q : ℚ × ℚ => ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I) ∈ W) h'

/-- **The imaginary-geometry clause of a mating-of-trees coupling passes through the law.** If `V`
is a mating-of-trees coupling and `V'` is a measurable random element of the data space with the
law of `V`, then `V'` satisfies the `igMap` clause of a coupling (same witness `Φ`; the locality
witnesses are the dyadic regularizations of those of `V`), provided the re-rooted curves
`affineReroot z₀ s φ` (`s > 0`) and the excursion segments in bounded open sets are measurable
functions of the curve. -/
theorem IsCouplingData.igMap_of_map_eq {γ : ℝ} (hC : IsCouplingData γ P V) (hV : Measurable V)
    (hV' : Measurable V') (hlaw : P'.map V' = P.map V)
    (hR : ∀ (z₀ : ℂ) (s φ : ℝ), 0 < s → Measurable (affineReroot z₀ s φ))
    (hE : ∀ W : Set ℂ, IsOpen W → Bornology.IsBounded W → ∀ z : ℂ,
      Measurable fun c : C(ℝ, ℂ) => excursionSegment c W z) :
    ∃ Φ : (ℝ → ℂ → ℝ) → C(ℝ, ℂ), Measurable Φ ∧
      (∀ K K' : ℝ → ℂ → ℝ, (∀ ρ : ℝ, 0 < ρ → K ρ = K' ρ) → Φ K = Φ K') ∧
      (∀ᵐ ω ∂P', (V' ω).ηL = Φ (fun ρ w => LQGMetric.circleAvg (V' ω).hIG ρ w + (V' ω).U)) ∧
      (∀ (z₀ : ℂ) (s φ : ℝ), 0 < s → ∀ᵐ ω ∂P',
        Φ (igPullback γ z₀ s φ (fun ρ w => LQGMetric.circleAvg (V' ω).hIG ρ w + (V' ω).U)) =
          affineReroot z₀ s φ (V' ω).ηL) ∧
      (∀ (W : Set ℂ), IsOpen W → Bornology.IsBounded W → ∀ δ : ℝ, 0 < δ →
        ∃ g : (ℝ → ℂ → ℝ) → (ℚ × ℚ → ℝ → ℂ), Measurable g ∧ ∀ᵐ ω ∂P', ∀ q : ℚ × ℚ,
          ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I) ∈ W →
            excursionSegment (V' ω).ηL W ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I) =
              g (restrictCircles (thickening δ W)
                (fun ρ w => LQGMetric.circleAvg (V' ω).hIG ρ w + (V' ω).U)) q) := by
  obtain ⟨Φ, hΦ, hpos, hae, hcc, hloc⟩ :=
    (show IsMatingOfTreesCoupling _ _ _ _ _ _ _ _ _ _ _ _ _ _ from hC).igMap
  refine ⟨Φ, hΦ, hpos, ae_ηL_eq_igCircleAvg_of_map_eq hV hV' hlaw hΦ hae,
    fun z₀ s φ hs => ae_igPullback_eq_affineReroot_of_map_eq hV hV' hlaw hΦ γ z₀ s φ
      (hR z₀ s φ hs) (hcc z₀ s φ hs), fun W hW hWb δ hδ => ?_⟩
  obtain ⟨g, hg, hgae⟩ := hloc W hW hWb δ hδ
  exact ⟨dyadicRegularize g, measurable_dyadicRegularize hg,
    ae_excursionSegment_eq_of_map_eq hV hV' hlaw δ (hE W hW hWb) hg hgae⟩

end MatedCRT
end MatedCRTHarmonic
