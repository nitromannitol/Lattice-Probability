import LatticeProb.Prob.FirstHitFiniteExit
import LatticeProb.Prob.PlanarAreaTimeScaling

/-! # Forward paths rooted at the origin -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Metric Filter
open scoped NNReal Topology

namespace LatticeProb

/-- A first hit at time zero identifies the rooted and forward paths. -/
theorem firstHitNonnegativeCurve_zero_eq_planarForwardPath
    (c : C(ℝ, ℂ)) (h : MatedCRTHarmonic.MatedCRT.firstHit c 0 = 0) :
    firstHitNonnegativeCurve c 0 = planarForwardPath c := by
  have hh : MatedCRTHarmonic.GMS4b.hitTime c 0 = 0 := h
  ext t : 1
  simp only [firstHitNonnegativeCurve, firstHitCenteredCurve, centeredEuclideanCurve,
    MatedCRTHarmonic.GMS4b.curveShift, planarForwardPath, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, hh, zero_add, sub_zero]

/-- The first-hit and forward paths of the area-time curve agree almost surely. -/
theorem ae_firstHitNonnegativeCurve_zero_eq_planarForwardPath
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRTHarmonic.MatedCRT.Path2}
    (hC : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀
      B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, firstHitNonnegativeCurve (ηL ω) 0 = planarForwardPath (ηL ω) := by
  filter_upwards [MatedCRTHarmonic.IGLaw.IsMatingOfTreesCoupling.ae_firstHit_zero_of_igMapPositiveRadii
    hC (MatedCRTHarmonic.IGLaw.IsMatingOfTreesCoupling.igMapPositiveRadii hC)] with ω hω
  exact firstHitNonnegativeCurve_zero_eq_planarForwardPath (ηL ω) hω

/-- The first-hit path law has the same fixed area-time scaling as the forward path law. -/
theorem map_firstHitNonnegativeCurve_normalize_of_matingOfTrees
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRTHarmonic.MatedCRT.Path2}
    (hC : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀
      B B' B₀ B₀' U ηL η η₀ bm) (s : ℝ≥0) (hs : 0 < s) :
    (P.map (fun ω => firstHitNonnegativeCurve (ηL ω) 0)).map
      (fun w => ((⟨ballNormalize 0 s hs, (ballNormalize 0 s hs).continuous⟩ :
        C(EuclideanSpace ℝ (Fin 2), EuclideanSpace ℝ (Fin 2))).comp w).comp
          ⟨areaTimeScale s hs, (areaTimeScale s hs).continuous⟩) =
      P.map (fun ω => firstHitNonnegativeCurve (ηL ω) 0) := by
  rw [Measure.map_congr (ae_firstHitNonnegativeCurve_zero_eq_planarForwardPath hC)]
  exact map_planarForwardPath_normalize_of_matingOfTrees hC s hs

/-- The first-hit path exits every ball in finite time almost surely. -/
theorem ae_firstHitNonnegativeCurve_exit_of_matingOfTrees
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRTHarmonic.MatedCRT.Path2}
    (hC : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀
      B B' B₀ B₀' U ηL η η₀ bm) (R : ℝ) :
    ∀ᵐ w ∂(P.map (fun ω => firstHitNonnegativeCurve (ηL ω) 0)),
      openExitTime (fun t w => w t) (ball (0 : EuclideanSpace ℝ (Fin 2)) R) w ≠ ⊤ := by
  apply ae_firstHitNonnegativeCurve_openExitTime_ne_top P ηL hC.measurable_curves.1 0 _ R
  filter_upwards [hC.spaceFilling] with ω hω
  exact hω.2.1

/-- The first-hit path law starts at the origin almost surely. -/
theorem ae_firstHitNonnegativeCurve_start_of_matingOfTrees
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRTHarmonic.MatedCRT.Path2}
    (hC : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀
      B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ w ∂(P.map (fun ω => firstHitNonnegativeCurve (ηL ω) 0)), w 0 = 0 := by
  have hm : Measurable (fun ω => firstHitNonnegativeCurve (ηL ω) 0) := by
    change Measurable ((fun q : C(ℝ, ℂ) × ℂ => firstHitNonnegativeCurve q.1 q.2) ∘
      (fun ω => (ηL ω, (0 : ℂ))))
    exact measurable_firstHitNonnegativeCurve.comp
      (hC.measurable_curves.1.prodMk measurable_const)
  apply (ae_map_iff hm.aemeasurable
    (measurableSet_singleton 0 |>.preimage
      (((continuous_eval : Continuous (fun p : C(ℝ≥0, EuclideanSpace ℝ (Fin 2)) × ℝ≥0 =>
        p.1 p.2)).comp (continuous_id.prodMk continuous_const)).measurable))).2
  filter_upwards [hC.spaceFilling] with ω hω
  exact firstHitCenteredCurve_zero hω.2.1 (hω.1 0)

end LatticeProb
