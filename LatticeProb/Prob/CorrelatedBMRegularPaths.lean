import LatticeProb.Prob.CorrelatedBMLadderRegular
import LatticeProb.Prob.CorrelatedBMCoordinatesDistinct
import LatticeProb.Prob.CorrelatedBMStart
import LatticeProb.Analysis.HolderImageNull

/-!
# Regular sample paths of a correlated two-sided Brownian pair

For a correlated two-sided Brownian pair `(L, R)` with correlation parameter `0 < γ < 2`, we collect in one predicate
`IsRegularCoordinatePair` the path properties that hold almost surely and are used in contour-pair rigidity
arguments for the mating-of-trees encoding:

* both coordinates are ladder regular on the rational anchors;
* the two coordinate paths are distinct;
* both coordinates vanish at time `0`;
* for every `α < 1/2`, each coordinate is `α`-Hölder on a neighbourhood of every time.

## Main results
* `volume_image_eq_zero_of_forall_holder_lt_half`: a path that is locally `α`-Hölder for every `α < 1/2` maps every
  set that is countable or of Hausdorff dimension `< 1/2` onto a Lebesgue-null set.
* `IsRegularCoordinatePair.volume_image_eq_zero`: the same for the coordinates of a regular pair.
* `ae_isRegularCoordinatePair`: a correlated Brownian pair is almost surely regular, given the descent and
  excursion-count conditions almost surely at each rational time.
-/

set_option autoImplicit false

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace LatticeProb.CorrelatedBM

open MatedCRTHarmonic.MatedCRT LatticeProb.LadderSet

/-- **Hölder images of small sets are null.** If `X` is, for every `α < 1/2`, locally `α`-Hölder, and `Z` is countable
or has Hausdorff dimension at most some `d < 1/2`, then `X '' Z` is Lebesgue-null. -/
theorem volume_image_eq_zero_of_forall_holder_lt_half {X : ℝ → ℝ} {Z : Set ℝ}
    (hX : ∀ α : ℝ≥0, (α : ℝ) < 1 / 2 → ∀ x : ℝ, ∃ C : ℝ≥0, ∃ U ∈ 𝓝 x, HolderOnWith C α X U)
    (hZ : Z.Countable ∨ ∃ d : ℝ≥0∞, dimH Z ≤ d ∧ d < 1 / 2) : volume (X '' Z) = 0 := by
  rcases hZ with hZ | ⟨d, hZd, hd⟩
  · exact volume_image_eq_zero_of_countable X hZ
  · obtain ⟨α, hdα, hα2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hd
    have hα0 : 0 < α := ENNReal.coe_pos.1 (lt_of_le_of_lt zero_le hdα)
    have hαr : (α : ℝ) < 1 / 2 := by
      have h2 : ((α : ℝ≥0∞)) < ((2⁻¹ : ℝ≥0) : ℝ≥0∞) := by
        simpa [one_div, ENNReal.coe_inv two_ne_zero] using hα2
      have h3 : α < 2⁻¹ := ENNReal.coe_lt_coe.1 h2
      have h4 : (α : ℝ) < ((2⁻¹ : ℝ≥0) : ℝ) := NNReal.coe_lt_coe.2 h3
      simpa [one_div] using h4
    refine volume_image_eq_zero_of_countable_or_dimH hα0 (hX α hαr) (Or.inr ⟨d, hZd, ?_⟩)
    exact ENNReal.div_lt_of_lt_mul (by rwa [one_mul])

/-- **Regular coordinate pair.** The path properties of a correlated two-sided Brownian pair used in contour-pair
rigidity: ladder regularity of both coordinates on the rational anchors, distinct coordinate paths, start at the
origin, and local `α`-Hölder continuity of both coordinates for every `α < 1/2`. -/
def IsRegularCoordinatePair (ω : Path2) : Prop :=
  (∀ i : Fin 2, IsLadderRegularOn (fun t => lrCoord i t ω) (range ((↑) : ℚ → ℝ))) ∧
    (fun t => lrCoord 0 t ω) ≠ (fun t => lrCoord 1 t ω) ∧
    (∀ i : Fin 2, lrCoord i 0 ω = 0) ∧
    ∀ i : Fin 2, ∀ α : ℝ≥0, (α : ℝ) < 1 / 2 → ∀ x : ℝ, ∃ C : ℝ≥0, ∃ U ∈ 𝓝 x,
      HolderOnWith C α (fun t => lrCoord i t ω) U

/-- **Null level images for a regular pair.** For a regular coordinate pair, each coordinate maps every set of times
that is countable or of Hausdorff dimension `< 1/2` onto a Lebesgue-null set of levels. -/
theorem IsRegularCoordinatePair.volume_image_eq_zero {ω : Path2} (h : IsRegularCoordinatePair ω) (i : Fin 2)
    {Z : Set ℝ} (hZ : Z.Countable ∨ ∃ d : ℝ≥0∞, dimH Z ≤ d ∧ d < 1 / 2) :
    volume ((fun t => lrCoord i t ω) '' Z) = 0 :=
  volume_image_eq_zero_of_forall_holder_lt_half (h.2.2.2 i) hZ

variable {γ : ℝ} {μ : Measure Path2}

/-- **A correlated Brownian pair is almost surely regular** for `0 < γ < 2`, given the descent and excursion-count
conditions almost surely at each rational time (the hypotheses of `ae_forall_isLadderRegularOn_rat`). -/
theorem ae_isRegularCoordinatePair (hμ : IsCorrelatedBM2 γ μ) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hdesc : ∀ i : Fin 2, ∀ q : ℚ, ∀ᵐ ω ∂μ,
      (∀ u < (q : ℝ), ∃ w ∈ Ioo u (q : ℝ), lrCoord i w ω < lrCoord i q ω) ∧
        ∀ u, (q : ℝ) < u → ∃ w ∈ Ioo (q : ℝ) u, lrCoord i w ω < lrCoord i q ω)
    (hexc : ∀ i : Fin 2, ∀ q : ℚ, ∀ᵐ ω ∂μ,
      (∀ t, (q : ℝ) ≤ t → Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
        (excursionCount (forwardLadderSet (fun s => lrCoord i s ω) q) q t ε : ℝ)) (𝓝[>] 0)
          (𝓝 (lrCoord i q ω - sInf ((fun s => lrCoord i s ω) '' Icc (q : ℝ) t)))) ∧
      ∀ t, t ≤ (q : ℝ) → Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
        (excursionCount (backwardLadderSet (fun s => lrCoord i s ω) q) t q ε : ℝ)) (𝓝[>] 0)
          (𝓝 (lrCoord i q ω - sInf ((fun s => lrCoord i s ω) '' Icc t (q : ℝ))))) :
    ∀ᵐ ω ∂μ, IsRegularCoordinatePair ω := by
  filter_upwards [ae_forall_isLadderRegularOn_rat hμ hdesc hexc, ae_coordinatePaths_ne_of_lt_two hμ hγ0 hγ2,
    ae_forall_lrCoord_zero_eq_zero hμ,
    ae_all_iff.2 fun i => hμ.ae_forall_exists_nhds_holderOnWith i] with ω h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

end LatticeProb.CorrelatedBM
