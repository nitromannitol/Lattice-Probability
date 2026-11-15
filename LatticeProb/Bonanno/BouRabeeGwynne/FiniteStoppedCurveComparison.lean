/- Adapted from Leonardo Bonanno lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.FiniteStoppedCurveComparison at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BoundaryStoppingGeometry
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianInnerExit
import LatticeProb.Bonanno.BouRabeeGwynne.UnitCurveOscillation

/-! The deterministic middle comparison uses the actual measurable first-exit
parameters and the finite Brownian representative's boundary oscillation. -/

open Set Metric
open scoped unitInterval ENNReal

namespace BouRabeeGwynne

theorem curveSpace_edist_prefix_unitExit_le_of_not_bad {d : ℕ}
    {U : Set (Euc d)} (hU : IsOpen U)
    (f g : C(unitInterval, Euc d)) (a : unitInterval)
    {ε mesh δ η : ℝ} (hε : 0 < ε) (hmesh : 0 ≤ mesh) (hbuffer : ε + mesh < δ)
    (hclose : ∀ t, dist (f t) (g t) ≤ ε)
    (hfpre : ∀ t < a, f t ∈ cthickening mesh U) (hfout : f a ∉ U)
    (hgexit : ∃ t, g t ∉ thickening δ U)
    (hgood : g ∉ unitCurveExitOscillationBad (innerDomain U ε) (thickening δ U) η) :
    edist (CurveSpace.project (prefixUnitCurve f a)) (unitCurveExitProjection U g) ≤
      ENNReal.ofReal (ε + η) := by
  have hδ : 0 < δ := (add_pos_of_pos_of_nonneg hε hmesh).trans hbuffer
  have hexU : ∃ t, g t ∉ U := by
    obtain ⟨t, ht⟩ := hgexit
    exact ⟨t, fun h ↦ ht (self_subset_thickening hδ U h)⟩
  have hout : g (unitCurveExitTime (thickening δ U) g) ∉
      cthickening (ε + mesh) U := by
    intro h
    exact (unitCurveExitTime_not_mem_of_exists isOpen_thickening hgexit)
      (cthickening_subset_thickening' hδ hbuffer U h)
  have hinner : ∀ t < unitCurveExitTime (innerDomain U ε) g,
      closedBall (g t) ε ⊆ U := by
    intro t ht
    exact closedBall_subset_of_mem_innerDomain (mem_of_lt_unitCurveExitTime ht)
  change edist (CurveSpace.project (prefixUnitCurve f a))
    (CurveSpace.project (prefixUnitCurve g (unitCurveExitTime U g))) ≤ _
  exact curveSpace_edist_prefixes_le_of_vertexExit f g (OrderIso.refl unitInterval) U
    a (unitCurveExitTime U g) (unitCurveExitTime (innerDomain U ε) g)
    (unitCurveExitTime (thickening δ U) g) hε.le hmesh hclose hfpre hfout
    (fun _ ht ↦ mem_of_lt_unitCurveExitTime ht)
    (unitCurveExitTime_not_mem_of_exists hU hexU) hinner hout
    (fun _ hs _ ht ↦ unitCurve_oscillation_le_of_not_bad hgood hs ht)

theorem curveSpace_edist_prefix_unitExit_le_of_endpoint_outside {d : ℕ}
    {U : Set (Euc d)} (hU : IsOpen U)
    (f g : C(unitInterval, Euc d)) (a : unitInterval)
    {ε mesh δ η : ℝ} (hε : 0 < ε) (hmesh : 0 ≤ mesh) (hbuffer : ε + mesh < δ)
    (hclose : ∀ t, dist (f t) (g t) ≤ ε)
    (hfpre : ∀ t < a, f t ∈ cthickening mesh U) (hfout : f a ∉ U)
    (hgexit : g 1 ∉ thickening δ U)
    (hgood : g ∉ unitCurveExitOscillationBad (innerDomain U ε) (thickening δ U) η) :
    edist (CurveSpace.project (prefixUnitCurve f a)) (unitCurveExitProjection U g) ≤
      ENNReal.ofReal (ε + η) :=
  curveSpace_edist_prefix_unitExit_le_of_not_bad hU f g a hε hmesh hbuffer hclose
    hfpre hfout ⟨1, hgexit⟩ hgood

end BouRabeeGwynne
