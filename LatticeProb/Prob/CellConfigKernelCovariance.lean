import LatticeProb.Prob.CellConfigSelectedSquare
import LatticeProb.Prob.CellConfigSimilarity
import LatticeProb.Prob.DyadicSystemInvariance
import LatticeProb.Prob.DyadicOffGrid

/-!
# Covariance of the uniform-average transport kernel of the capped squares

Let `H` be a cell configuration (Gwynne, Miller and Sheffield, *Harmonic functions on mated-CRT
maps*, arXiv 1807.07511, Definition 1.15) and let `S_m^w` be the capped square of cell mass `m`
around `w` of the uniform dyadic system of the plane (Gwynne, Miller and Sheffield, *An invariance
principle for ergodic scale-free random environments*, arXiv 1807.07515, (2.1)). For a nonnegative
function `G` of the configuration and a point, the transport kernel of (B.6) there is
`F(H, w₀, w₁) = E[|S_m^{w₀}|⁻¹ 1(w₁ ∈ S_m^{w₀})] G(H, w₁)`, the expectation over the dyadic system.

We show that the law of the dyadic system is invariant under the transformation of its
coordinates induced by a positive similarity `z ↦ s (z - u)`, that the uniform-average kernel of
the similar configuration `C(H - u)` at the transformed points is almost surely `s⁻²` times the
kernel of `H`, and hence that `F` has the covariance
`F(C(H - u), C(w₀ - u), C(w₁ - u)) = s⁻² F(H, w₀, w₁)` of the mass-transport principle
(arXiv 1807.07511, Definition 1.2(4)) when `G` is invariant under the similarities.

## Main statements

* `LatticeProb.CellConfigCappedSquare.measurePreserving_similarityCoord`: the transformed dyadic
  coordinates have the law of the dyadic coordinates.
* `LatticeProb.CellConfigCappedSquare.ae_averageKernel_similarity`: almost-sure covariance of the
  uniform-average kernel.
* `LatticeProb.CellConfigCappedSquare.cappedTransportKernel_similarity`: covariance of the
  transport kernel.
-/

open MeasureTheory Set
open scoped ENNReal

namespace LatticeProb.CellConfigCappedSquare

open ReflectedGMS ReflectedGMS.GMS CellMass CappedSquare DyadicOffset

/-- The coordinates `z ↦ s • z + b` of the similarity `z ↦ s (z - u)` of `Plane`, read through
`planeCoord⁻¹`. -/
theorem planeCoord_symm_positiveSimilarity (s : ℝ) (u w : Plane) :
    planeCoord.symm (positiveSimilarity s u w) =
      s • planeCoord.symm w + similarityOffset s u := by
  apply planeCoord.injective
  rw [LinearIsometryEquiv.apply_symm_apply, planeCoord_smul_add_similarityOffset,
    LinearIsometryEquiv.apply_symm_apply]

theorem measurable_two_rpow_neg_mul (a : ℝ) : Measurable fun r : ℝ => (2 : ℝ) ^ (-r) * a :=
  (measurable_const.pow measurable_id.neg).mul_const a

/-- **The law of the uniform dyadic system is invariant under the similarities**: the transformed
coordinates `similarityCoord s u q` have the law `unifIco 1 ⊗ offsetLaw ⊗ offsetLaw` of `q`. -/
theorem measurePreserving_similarityCoord (s : ℝ) (u : Plane) :
    MeasurePreserving (similarityCoord s u) ((unifIco 1).prod (offsetLaw.prod offsetLaw))
      ((unifIco 1).prod (offsetLaw.prod offsetLaw)) := by
  have := isProbabilityMeasure_unifIco (zero_lt_one' ℝ)
  exact (measurePreserving_shiftSkew₂ (μ := unifIco 1)
      (measurable_two_rpow_neg_mul (similarityOffset s u).re)
      (measurable_two_rpow_neg_mul (similarityOffset s u).im)).comp
    (measurePreserving_dilateScale₂ (Real.logb 2 s))

/-- The uniform-average kernel is measurable in the dyadic coordinates. -/
theorem measurable_averageKernel_dyadic (m : ℝ≥0∞) (H : GMSSpace) (w₀ w₁ : ℂ) :
    Measurable fun q : DyadicCoord => averageKernel m (H, (q, w₀), w₁) :=
  (measurable_averageKernel m).comp
    (measurable_const.prodMk ((measurable_id.prodMk measurable_const).prodMk measurable_const))

/-- **Almost-sure covariance of the uniform-average kernel**: if `H'` is `C(H - u)`, then almost
surely in the dyadic system, for every mass `m ∈ (0, ∞)` and every `w₁`, the kernel of `H'` for
the transformed coordinates at `(T w₀, T w₁)` is `s⁻²` times the kernel of `H` at `(w₀, w₁)`, where
`T z = s • z + b`. -/
theorem ae_averageKernel_similarity {s : ℝ} {u : Plane} {hs : 0 < s} {H H' : GMSSpace}
    (hHH' : IsSimilar s u hs H H') (w₀ : ℂ) :
    ∀ᵐ q ∂(unifIco 1).prod (offsetLaw.prod offsetLaw), ∀ m : ℝ≥0∞, m ≠ 0 → m ≠ ∞ → ∀ w₁ : ℂ,
      averageKernel m (H', (similarityCoord s u q, s • w₀ + similarityOffset s u),
          s • w₁ + similarityOffset s u) =
        ENNReal.ofReal ((s ^ 2)⁻¹) * averageKernel m (H, (q, w₀), w₁) := by
  have hB := (measurePreserving_similarityCoord s u).quasiMeasurePreserving.ae
    (ae_averageKernel_eq H' (s • w₀ + similarityOffset s u))
  filter_upwards [ae_averageKernel_eq H w₀, hB, ae_isCompatible_system] with q hq hq' hc
  intro m hm0 hmtop w₁
  rw [hq' m hm0 hmtop, hq m hm0 hmtop w₁, ENNReal.ofReal_inv_of_pos (pow_pos hs 2)]
  have hH' : H'.1 = H.1.similarity s u hs := hHH'
  rw [hH']
  exact uniformDensity_cappedSquare_similarity s u hs q hc.1 hc.2 m w₀ w₁

/-- **The transport kernel of the capped squares** ((B.6) of arXiv 1807.07515):
`F(H, w₀, w₁) = E[|S_m^{w₀}|⁻¹ 1(w₁ ∈ S_m^{w₀})] G(H, w₁)`, the expectation over the uniform
dyadic system, for points of `Plane` read in the coordinates `ℂ`. -/
noncomputable def cappedTransportKernel (m : ℝ≥0∞) (G : GMSSpace × ℂ → ℝ≥0∞)
    (p : GMSSpace × Plane × Plane) : ℝ≥0∞ :=
  (∫⁻ q, averageKernel m (p.1, (q, planeCoord.symm p.2.1), planeCoord.symm p.2.2)
      ∂(unifIco 1).prod (offsetLaw.prod offsetLaw)) * G (p.1, planeCoord.symm p.2.2)

/-- **Covariance of the transport kernel**: if `H'` is `C(H - u)` and `G` is invariant under the
similarity, `G(H', T w) = G(H, w)`, then
`F(H', C(w₀ - u), C(w₁ - u)) = s⁻² F(H, w₀, w₁)` for every mass `m ∈ (0, ∞)`. -/
theorem cappedTransportKernel_similarity {m : ℝ≥0∞} (hm0 : m ≠ 0) (hmtop : m ≠ ∞)
    {G : GMSSpace × ℂ → ℝ≥0∞} {s : ℝ} {u : Plane} {hs : 0 < s} {H H' : GMSSpace}
    (hHH' : IsSimilar s u hs H H')
    (hG : ∀ w : ℂ, G (H', s • w + similarityOffset s u) = G (H, w)) (w₀ w₁ : Plane) :
    cappedTransportKernel m G (H', positiveSimilarity s u w₀, positiveSimilarity s u w₁) =
      ENNReal.ofReal ((s ^ 2)⁻¹) * cappedTransportKernel m G (H, w₀, w₁) := by
  simp only [cappedTransportKernel, planeCoord_symm_positiveSimilarity]
  have h1 : ∫⁻ q, averageKernel m (H', (q, s • planeCoord.symm w₀ + similarityOffset s u),
        s • planeCoord.symm w₁ + similarityOffset s u)
        ∂(unifIco 1).prod (offsetLaw.prod offsetLaw) =
      ∫⁻ q, averageKernel m (H', (similarityCoord s u q,
          s • planeCoord.symm w₀ + similarityOffset s u),
        s • planeCoord.symm w₁ + similarityOffset s u)
        ∂(unifIco 1).prod (offsetLaw.prod offsetLaw) :=
    ((measurePreserving_similarityCoord s u).lintegral_comp
      (measurable_averageKernel_dyadic m H' _ _)).symm
  have h2 : ∫⁻ q, averageKernel m (H', (similarityCoord s u q,
          s • planeCoord.symm w₀ + similarityOffset s u),
        s • planeCoord.symm w₁ + similarityOffset s u)
        ∂(unifIco 1).prod (offsetLaw.prod offsetLaw) =
      ∫⁻ q, ENNReal.ofReal ((s ^ 2)⁻¹) *
          averageKernel m (H, (q, planeCoord.symm w₀), planeCoord.symm w₁)
        ∂(unifIco 1).prod (offsetLaw.prod offsetLaw) :=
    lintegral_congr_ae ((ae_averageKernel_similarity hHH' (planeCoord.symm w₀)).mono
      fun q hq => hq m hm0 hmtop (planeCoord.symm w₁))
  rw [h1, h2, lintegral_const_mul _ (measurable_averageKernel_dyadic m H _ _), hG, mul_assoc]

end LatticeProb.CellConfigCappedSquare
