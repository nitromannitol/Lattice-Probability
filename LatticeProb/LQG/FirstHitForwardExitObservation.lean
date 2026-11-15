import LatticeProb.Prob.FirstHitForwardAreaTime
import LatticeProb.Prob.SpatialExitObservation
import LatticeProb.Prob.AELeSigma

/-! # First-hit and forward exit observations -/

set_option autoImplicit false

open MeasureTheory Filter Set Metric
open scoped ENNReal NNReal

namespace LatticeProb

/-- At a zero first-hit time, the Euclidean first-hit observation is the
coordinate image of the complex forward observation. This includes infinite
exit clocks and arbitrary radii. -/
theorem firstHit_stoppedPath_eq_forward_coordinates
    (c : C(ℝ, ℂ)) (h : MatedCRTHarmonic.MatedCRT.firstHit c 0 = 0) (r : ℝ) :
    let w : C(ℝ≥0, ℂ) := c.comp ⟨fun t => (t : ℝ), NNReal.continuous_coe⟩
    let v := firstHitNonnegativeCurve c 0
    let J : C(ℂ, EuclideanSpace ℝ (Fin 2)) :=
      ⟨Complex.orthonormalBasisOneI.repr, Complex.orthonormalBasisOneI.repr.continuous⟩
    stoppedPath (openExitTime (fun t (_ : Unit) => v t) (ball 0 r) ()) v =
      J.comp (stoppedPath (openExitTime (fun t (_ : Unit) => w t) (ball 0 r) ()) w) := by
  dsimp only
  rw [firstHitNonnegativeCurve_zero_eq_planarForwardPath c h]
  let J : C(ℂ, EuclideanSpace ℝ (Fin 2)) :=
    ⟨Complex.orthonormalBasisOneI.repr, Complex.orthonormalBasisOneI.repr.continuous⟩
  let w : C(ℝ≥0, ℂ) := c.comp ⟨fun t => (t : ℝ), NNReal.continuous_coe⟩
  have hball : J ⁻¹' (ball 0 r) = ball (0 : ℂ) r := by
    ext z
    change Complex.orthonormalBasisOneI.repr z ∈ ball 0 r ↔ z ∈ ball 0 r
    simpa only [mem_ball, map_zero, Complex.orthonormalBasisOneI.repr.dist_map] using
      (show dist (Complex.orthonormalBasisOneI.repr z)
        (Complex.orthonormalBasisOneI.repr 0) < r ↔ dist z 0 < r by
          rw [Complex.orthonormalBasisOneI.repr.dist_map])
  change stoppedPath (openExitTime (fun t (_ : Unit) => (J.comp w) t) (ball 0 r) ())
    (J.comp w) = J.comp (stoppedPath (openExitTime (fun t (_ : Unit) => w t)
      (ball 0 r) ()) w)
  simpa only [hball, ContinuousMap.coe_comp, Function.comp_apply] using
    stoppedPath_openExit_comp_spatial w J (ball 0 r)

/-- The first-hit Euclidean observation and the complex forward observation
of a coupled curve generate the same events up to null sets. -/
theorem aeLeSigma_firstHit_forward_exit_observations
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRTHarmonic.MatedCRT.Path2}
    (hC : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀
      B B' B₀ B₀' U ηL η η₀ bm) (r : ℝ) :
    let A := fun ω =>
      let w : C(ℝ≥0, ℂ) := (ηL ω).comp ⟨fun t => (t : ℝ), NNReal.continuous_coe⟩
      stoppedPath (openExitTime (fun t (_ : Unit) => w t) (ball 0 r) ()) w
    let B := fun ω =>
      let v := firstHitNonnegativeCurve (ηL ω) 0
      stoppedPath (openExitTime (fun t (_ : Unit) => v t) (ball 0 r) ()) v
    AELeSigma (MeasurableSpace.comap B inferInstance) (MeasurableSpace.comap A inferInstance) P ∧
    AELeSigma (MeasurableSpace.comap A inferInstance) (MeasurableSpace.comap B inferInstance) P := by
  dsimp only
  let A : Ω → C(ℝ≥0, ℂ) := fun ω =>
    let w : C(ℝ≥0, ℂ) := (ηL ω).comp ⟨fun t => (t : ℝ), NNReal.continuous_coe⟩
    stoppedPath (openExitTime (fun t (_ : Unit) => w t) (ball 0 r) ()) w
  let B : Ω → C(ℝ≥0, EuclideanSpace ℝ (Fin 2)) := fun ω =>
    let v := firstHitNonnegativeCurve (ηL ω) 0
    stoppedPath (openExitTime (fun t (_ : Unit) => v t) (ball 0 r) ()) v
  let J : C(ℂ, EuclideanSpace ℝ (Fin 2)) :=
    ⟨Complex.orthonormalBasisOneI.repr, Complex.orthonormalBasisOneI.repr.continuous⟩
  let K : C(EuclideanSpace ℝ (Fin 2), ℂ) :=
    ⟨Complex.orthonormalBasisOneI.repr.symm, Complex.orthonormalBasisOneI.repr.symm.continuous⟩
  have hBA : B =ᵐ[P] fun ω => J.comp (A ω) := by
    filter_upwards [MatedCRTHarmonic.IGLaw.IsMatingOfTreesCoupling.ae_firstHit_zero_of_igMapPositiveRadii
      hC (MatedCRTHarmonic.IGLaw.IsMatingOfTreesCoupling.igMapPositiveRadii hC)] with ω hω
    exact firstHit_stoppedPath_eq_forward_coordinates (ηL ω) hω r
  have hAB : A =ᵐ[P] fun ω => K.comp (B ω) := by
    filter_upwards [hBA] with ω hω
    rw [hω]
    ext t
    simp only [ContinuousMap.coe_comp, Function.comp_apply, J, K, ContinuousMap.coe_mk,
      Complex.orthonormalBasisOneI.repr.symm_apply_apply]
  change AELeSigma (MeasurableSpace.comap B _) (MeasurableSpace.comap A _) P ∧
    AELeSigma (MeasurableSpace.comap A _) (MeasurableSpace.comap B _) P
  exact ⟨AELeSigma.comap_of_ae_eq
      ((ContinuousMap.continuous_postcomp J).measurable.comp (comap_measurable A)) hBA,
    AELeSigma.comap_of_ae_eq
      ((ContinuousMap.continuous_postcomp K).measurable.comp (comap_measurable B)) hAB⟩

end LatticeProb
