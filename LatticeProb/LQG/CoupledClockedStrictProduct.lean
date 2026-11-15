import LatticeProb.Analysis.ClockedCellWindowStrict
import LatticeProb.Analysis.CorrelatedBMHolder
import LatticeProb.Bonanno.MatedCRTHarmonic.MatedCRT.BrownianG0
import LatticeProb.LQG.CoupledClockedBrownianPath

/-! # Strict cell windows for clocked Brownian paths -/

set_option autoImplicit false

open MeasureTheory Set MatedCRTHarmonic MatedCRTHarmonic.MatedCRT LatticeProb.CorrelatedBM
open scoped NNReal

namespace LatticeProb

/-- A coordinate of a continuous planar path, as a continuous real path. -/
def lrCoordPath (k : Fin 2) (p : Path2) : C(ℝ, ℝ) :=
  ⟨fun t => lrCoord k t p, continuous_lrCoord_time k p⟩

/-- Coordinate projection is measurable on continuous-path space. -/
theorem measurable_lrCoordPath (k : Fin 2) : Measurable (lrCoordPath k) := by
  apply ContinuousMap.measurable_iff_eval.2
  intro t
  exact measurable_lrCoord_path k t

/-- At a fixed positive mesh, independent absolutely continuous phases give
strict cell-window comparisons in both coordinates of the coupled clocked path. -/
theorem exists_coupled_clocked_brownian_strict_product
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (hC : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hf : AEMeasurable (fun ω => coneField (X ω)
      (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω))) P)
    (ε : ℝ) (hε : 0 < ε) (Q : Measure ℝ) [SFinite Q] (hQ : Q ≪ volume) :
    ∃ (F : Ω → C(ℝ, ℝ)) (G : Ω → Path2), Measurable F ∧ Measurable G ∧
      (∀ᵐ ω ∂P, ∃ ψ : ℝ ≃o ℝ, ψ 0 = 0 ∧
        (∀ t, η₀ ω t = η ω (ψ t)) ∧
        (∀ t, F ω t = ψ t) ∧ ∀ t, G ω t = bm ω (ψ t)) ∧
      ∀ᵐ p ∂P.prod Q, ∀ k : Fin 2, cellWindowStrict ε (lrCoordPath k (G p.1)) p.2 := by
  have : IsProbabilityMeasure P := hC.isProbabilityMeasure
  obtain ⟨F, G, hF, hG, hclock⟩ :=
    exists_measurable_coupled_clocked_brownian_path hC hγ hf
  refine ⟨F, G, hF, hG, hclock, ?_⟩
  have hmin := ae_of_ae_map hC.measurable_curves.2.2.2.aemeasurable
    (ae_locMinDistinct hC.boundaryLawBM)
  have hsections (k : Fin 2) :
      ∀ᵐ ω ∂P, {θ : ℝ | ¬ cellWindowStrict ε (lrCoordPath k (G ω)) θ}.Countable := by
    filter_upwards [hmin, hclock] with ω hω hψ
    obtain ⟨ψ, _, _, _, heq⟩ := hψ
    have hp : lrCoordPath k (G ω) =
        ⟨fun t => lrCoord k (ψ t) (bm ω),
          (continuous_lrCoord_time k (bm ω)).comp ψ.continuous⟩ := by
      ext t
      change lrCoord k t (G ω) = lrCoord k (ψ t) (bm ω)
      simp only [lrCoord, heq t]
    rw [hp]
    exact countable_cellWindowStrict_failures_comp_orderIso
      (lrCoordPath k (bm ω)) ψ ε hε (hω k)
  apply ae_all_iff.2
  intro k
  exact ae_prod_cellWindowStrict_of_countable
    (fun ω => lrCoordPath k (G ω)) ((measurable_lrCoordPath k).comp hG) ε Q hQ
    (hsections k)

end LatticeProb
