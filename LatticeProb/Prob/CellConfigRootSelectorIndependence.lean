import LatticeProb.Prob.CellConfigCellDiameterSublinear
import LatticeProb.Prob.CellConfigContainingCell

/-! # Origin-cell selection and finite expectation

Mass transport makes the cell containing the origin almost surely unique. Consequently the
finite-expectation hypothesis may use the canonical measurable selector. -/

open MeasureTheory
open scoped ENNReal
open ReflectedGMS ReflectedGMS.GMS
open LatticeProb.CellConfigCappedSquare LatticeProb.CellConfigContainingCell

namespace LatticeProb.CellConfigRootSelectorIndependence

/-- Any two selections of an origin-containing cell agree almost surely. -/
theorem ae_eq_origin_selectors {μ : Measure GMSSpace} (hMT : MassTransport μ)
    {f g : GMSSpace → Cell}
    (hf : ∀ H, f H ∈ H.1.cells ∧ (0 : Plane) ∈ (f H : Set Plane))
    (hg : ∀ H, g H ∈ H.1.cells ∧ (0 : Plane) ∈ (g H : Set Plane)) :
    f =ᵐ[μ] g := by
  filter_upwards [ae_zero_notMem_frontier hMT] with H hH
  exact eq_of_zero_mem hH (hf H).1 (hg H).1 (hf H).2 (hg H).2

/-- Under mass transport, finite expectation is independent of the choice of root cell. -/
theorem finiteExpectation_iff_canonical {μ : Measure GMSSpace} (hMT : MassTransport μ) :
    FiniteExpectation μ ↔
      (∫⁻ H, ENNReal.ofReal (Metric.diam (containingCell (H, 0) : Set Plane) ^ 2 /
        CellConfig.area (containingCell (H, 0)) * H.1.pi (containingCell (H, 0))) ∂μ) < ∞ ∧
      (∫⁻ H, ENNReal.ofReal (Metric.diam (containingCell (H, 0) : Set Plane) ^ 2 /
        CellConfig.area (containingCell (H, 0)) * H.1.piStar (containingCell (H, 0))) ∂μ) < ∞ := by
  let root : GMSSpace → Cell := fun H => containingCell (H, 0)
  have hroot : ∀ H, root H ∈ H.1.cells ∧ (0 : Plane) ∈ (root H : Set Plane) :=
    fun H => ⟨containingCell_mem (H, 0), mem_containingCell (H, 0)⟩
  constructor
  · rintro ⟨f, hf, hpi, hstar⟩
    have heq := ae_eq_origin_selectors hMT hf hroot
    have h1 := lintegral_congr_ae (heq.mono fun H h => by dsimp only; rw [h])
      (f := fun H => ENNReal.ofReal (Metric.diam (f H : Set Plane) ^ 2 /
        CellConfig.area (f H) * H.1.pi (f H)))
      (g := fun H => ENNReal.ofReal (Metric.diam (root H : Set Plane) ^ 2 /
        CellConfig.area (root H) * H.1.pi (root H)))
    have h2 := lintegral_congr_ae (heq.mono fun H h => by dsimp only; rw [h])
      (f := fun H => ENNReal.ofReal (Metric.diam (f H : Set Plane) ^ 2 /
        CellConfig.area (f H) * H.1.piStar (f H)))
      (g := fun H => ENNReal.ofReal (Metric.diam (root H : Set Plane) ^ 2 /
        CellConfig.area (root H) * H.1.piStar (root H)))
    exact ⟨h1 ▸ hpi, h2 ▸ hstar⟩
  · intro h
    exact ⟨root, hroot, h.1, h.2⟩

end LatticeProb.CellConfigRootSelectorIndependence
