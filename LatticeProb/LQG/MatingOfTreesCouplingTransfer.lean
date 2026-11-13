import LatticeProb.LQG.MatingOfTreesCouplingAreaLaw
import LatticeProb.LQG.MatingOfTreesCouplingBoundaryLength
import LatticeProb.LQG.MatingOfTreesCouplingDegrees
import LatticeProb.LQG.MatingOfTreesCouplingMerge
import LatticeProb.LQG.MatingOfTreesCouplingMergeScaling
import LatticeProb.LQG.MatingOfTreesCouplingPathwise
import LatticeProb.LQG.MatingOfTreesCouplingSegments
import LatticeProb.LQG.MatingOfTreesCouplingVisits

/-!
# A mating-of-trees coupling is carried by its law, up to three clauses

Let `V` be a mating-of-trees coupling, i.e. a measurable random element of the data space whose
coordinates satisfy every clause of `IsMatingOfTreesCoupling` (`IsCouplingData γ P V`), and let `V'`
be a measurable random element, on a possibly different probability space, with the same law.

Each clause of the coupling except three is already known to pass from `V` to `V'`: the laws and
independence statements of the fields and paths (`MatingOfTreesCouplingLaw`), the space-filling,
coverage, segment, visit and cell-moment clauses, the boundary-length clause and the merge property
(Duplantier-Miller-Sheffield, Lemma 8.8). The area-parametrization clauses pass as well as soon as
the LQG area measures of the two quantum cones of `V` exist almost surely as vague limits.

* `IsCouplingData.of_map_eq`: `V'` is a mating-of-trees coupling, given the almost sure existence of
  the two LQG area measures for `V`, the imaginary-geometry clause for `V'` and the only-merge
  property of `V'` (Duplantier-Miller-Sheffield, Lemmas 8.9 and 8.14). The latter is not a property
  of the law in any evident way: the complement of a generated equivalence relation is only
  coanalytic.
* `IsCouplingData.of_map_eq_of_ae_rescale`: on one probability space, if the curve and the
  boundary-length pair of `V'` are almost surely the Brownian rescalings `t ↦ R⁻¹ η(bt)` and
  `t ↦ b^{-1/2} w(bt)` of those of `V`, the only-merge property of `V'` holds pathwise, so `V'` is a
  mating-of-trees coupling given the area measures of `V` and the imaginary-geometry clause of `V'`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

open CouplingData

variable {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
  {γ : ℝ}

/-- **Transfer of a mating-of-trees coupling along equality of laws.** If `V` is a mating-of-trees
coupling for `0 < γ < 2` and `V'` is a measurable random element with the law of `V`, then `V'` is
a mating-of-trees coupling, provided the LQG area measures of the two quantum cones of `V` exist
almost surely as vague limits, and `V'` satisfies the imaginary-geometry clause and the only-merge
property. -/
theorem IsCouplingData.of_map_eq {V : Ω → CouplingData} {V' : Ω' → CouplingData}
    (hC : IsCouplingData γ P V) (hγ : 0 < γ) (hγ2 : γ < 2) (hV : Measurable V)
    (hV' : Measurable V') (hlaw : P'.map V' = P.map V)
    (hex : ∀ᵐ ω ∂P, ∃ μ, IsVagueLimitC
      (lqgAreaApprox γ (coneField (V ω).X (coneRadial γ γ (V ω).B (V ω).B'))) μ)
    (hex₀ : ∀ᵐ ω ∂P, ∃ μ, IsVagueLimitC
      (lqgAreaApprox γ (coneField (V ω).X₀ (coneRadial γ 0 (V ω).B₀ (V ω).B₀'))) μ)
    (hIg : ∃ Φ : (ℝ → ℂ → ℝ) → C(ℝ, ℂ), Measurable Φ ∧
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
                (fun ρ w => LQGMetric.circleAvg (V' ω).hIG ρ w + (V' ω).U)) q))
    (hOnly : ∀ᵐ ω ∂P', ∀ s t : ℝ, (V' ω).η s = (V' ω).η t →
      Relation.EqvGen (fun a c => DirectRel (fun u => lrCoord 0 u (V' ω).bm) a c ∨
        DirectRel (fun u => lrCoord 1 u (V' ω).bm) a c) s t) :
    IsCouplingData γ P' V' := by
  have hCP := (show IsMatingOfTreesCoupling _ _ _ _ _ _ _ _ _ _ _ _ _ _ from hC)
  have : IsProbabilityMeasure P := hCP.isProbabilityMeasure
  have hbm := hC.bm_of_map_eq hV hV' hlaw
  have hind := hC.indep_cone_of_map_eq hV hV' hlaw
  have hmerge := ae_merge_of_map_eq (V := fun ω => ((V ω).η, (V ω).bm))
    (V' := fun ω => ((V' ω).η, (V' ω).bm))
    ((measurable_η.comp hV).prodMk (measurable_bm.comp hV))
    ((measurable_η.comp hV').prodMk (measurable_bm.comp hV'))
    (map_comp_of_map_eq hV hV' hlaw (measurable_η.prodMk measurable_bm)) hCP.merge
  unfold IsCouplingData
  exact
    { isProbabilityMeasure := hC.isProbabilityMeasure_of_map_eq hV hV' hlaw
      gff := hC.gff_of_map_eq hV hV' hlaw
      gff₀ := hC.gff₀_of_map_eq hV hV' hlaw
      bm_B := hbm.1
      bm_B' := hbm.2.1
      bm_B₀ := hbm.2.2.1
      bm_B₀' := hbm.2.2.2
      indep_cone := hind.1
      indep_cone₀ := hind.2
      igField := hC.igField_of_map_eq hV hV' hlaw
      indep_curve := hC.indep_curve_of_map_eq hV hV' hlaw
      measurable_curves := ⟨measurable_ηL.comp hV', measurable_η.comp hV', measurable_η₀.comp hV',
        measurable_bm.comp hV'⟩
      igMap := hIg
      spaceFilling := hC.spaceFilling_of_map_eq hV hV' hlaw
      areaParam := hC.areaParam_of_map_eq_of_ae_exists hγ hγ2 hV hV' hlaw hex
      areaParam₀ := hC.areaParam₀_of_map_eq_of_ae_exists hγ hγ2 hV hV' hlaw hex₀
      segmentsContainBalls := hC.segmentsContainBalls_of_map_eq hV hV' hlaw
      coverage := hC.coverage_of_map_eq hV hV' hlaw
      cellMoments := hC.cellMoments_of_map_eq hV hV' hlaw
      boundaryLawBM := hC.boundaryLawBM_of_map_eq hV hV' hlaw
      boundaryLength := hC.boundaryLength_of_map_eq hV hV' hlaw (hC.ae_radGood hγ hγ2)
      merge := hmerge
      onlyMerge := hOnly
      visitBound := hC.visitBound_of_map_eq hV hV' hlaw }

/-- **A rescaled copy of a mating-of-trees coupling.** On one probability space, let `V` be a
mating-of-trees coupling for `0 < γ < 2` and `V'` a measurable random element with the law of `V`
whose curve and boundary-length pair are almost surely `t ↦ R⁻¹ η(bt)` (with `R ≠ 0` almost surely)
and `t ↦ b^{-1/2} w(bt)` for the curve `η` and pair `w` of `V`. Then `V'` is a mating-of-trees
coupling, provided the LQG area measures of the two quantum cones of `V` exist almost surely as vague
limits and `V'` satisfies the imaginary-geometry clause. -/
theorem IsCouplingData.of_map_eq_of_ae_rescale {V V' : Ω → CouplingData}
    (hC : IsCouplingData γ P V) (hγ : 0 < γ) (hγ2 : γ < 2) (hV : Measurable V)
    (hV' : Measurable V') (hlaw : P.map V' = P.map V)
    (hex : ∀ᵐ ω ∂P, ∃ μ, IsVagueLimitC
      (lqgAreaApprox γ (coneField (V ω).X (coneRadial γ γ (V ω).B (V ω).B'))) μ)
    (hex₀ : ∀ᵐ ω ∂P, ∃ μ, IsVagueLimitC
      (lqgAreaApprox γ (coneField (V ω).X₀ (coneRadial γ 0 (V ω).B₀ (V ω).B₀'))) μ)
    (hIg : ∃ Φ : (ℝ → ℂ → ℝ) → C(ℝ, ℂ), Measurable Φ ∧
      (∀ K K' : ℝ → ℂ → ℝ, (∀ ρ : ℝ, 0 < ρ → K ρ = K' ρ) → Φ K = Φ K') ∧
      (∀ᵐ ω ∂P, (V' ω).ηL = Φ (fun ρ w => LQGMetric.circleAvg (V' ω).hIG ρ w + (V' ω).U)) ∧
      (∀ (z₀ : ℂ) (s φ : ℝ), 0 < s → ∀ᵐ ω ∂P,
        Φ (igPullback γ z₀ s φ (fun ρ w => LQGMetric.circleAvg (V' ω).hIG ρ w + (V' ω).U)) =
          affineReroot z₀ s φ (V' ω).ηL) ∧
      (∀ (W : Set ℂ), IsOpen W → Bornology.IsBounded W → ∀ δ : ℝ, 0 < δ →
        ∃ g : (ℝ → ℂ → ℝ) → (ℚ × ℚ → ℝ → ℂ), Measurable g ∧ ∀ᵐ ω ∂P, ∀ q : ℚ × ℚ,
          ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I) ∈ W →
            excursionSegment (V' ω).ηL W ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I) =
              g (restrictCircles (thickening δ W)
                (fun ρ w => LQGMetric.circleAvg (V' ω).hIG ρ w + (V' ω).U)) q))
    {b : ℝ} (hb : 0 < b) {R : Ω → ℝ} (hR : ∀ᵐ ω ∂P, R ω ≠ 0)
    (hη : ∀ᵐ ω ∂P, (V' ω).η = coneRescaleCurve (R ω) b (V ω).η)
    (hw : ∀ᵐ ω ∂P, (V' ω).bm = brownRescale b (V ω).bm) :
    IsCouplingData γ P V' :=
  hC.of_map_eq hγ hγ2 hV hV' hlaw hex hex₀ hIg (hC.onlyMerge_of_ae_rescale hb hR hη hw)

end MatedCRT

end MatedCRTHarmonic
