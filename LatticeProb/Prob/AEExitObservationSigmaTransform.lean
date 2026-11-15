import LatticeProb.Prob.CombinedExitTransform
import LatticeProb.Prob.AELeSigma

/-! # Almost-sure transport of exit observations -/

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace LatticeProb

/-- Fixed invertible spatial and clock transformations preserve the stopped-path
observation sigma algebras up to null sets when the open exit is almost surely finite. -/
theorem aeLeSigma_stoppedPath_openExit_comp_spatial_orderIso
    {Ω E F : Type*} [MeasurableSpace Ω] [TopologicalSpace E] [TopologicalSpace F]
    (μ : Measure Ω) (w : Ω → C(ℝ≥0, E)) (e : E ≃ₜ F) (φ : ℝ≥0 ≃o ℝ≥0)
    (V : Set F) (hV : IsOpen V)
    (hfin : ∀ᵐ ω ∂μ, openExitTime (fun t (_ : Unit) => w ω t) (e ⁻¹' V) () ≠ ⊤) :
    let A := fun ω => stoppedPath
      (openExitTime (fun t (_ : Unit) => w ω t) (e ⁻¹' V) ()) (w ω)
    let B := fun ω => stoppedPath
      (openExitTime (fun t (_ : Unit) => e (w ω (φ t))) V ())
      (((⟨e, e.continuous⟩ : C(E, F)).comp (w ω)).comp ⟨φ, φ.continuous⟩)
    AELeSigma (MeasurableSpace.comap B inferInstance) (MeasurableSpace.comap A inferInstance) μ ∧
    AELeSigma (MeasurableSpace.comap A inferInstance) (MeasurableSpace.comap B inferInstance) μ := by
  dsimp only
  let A : Ω → C(ℝ≥0, E) := fun ω => stoppedPath
    (openExitTime (fun t (_ : Unit) => w ω t) (e ⁻¹' V) ()) (w ω)
  let B : Ω → C(ℝ≥0, F) := fun ω => stoppedPath
    (openExitTime (fun t (_ : Unit) => e (w ω (φ t))) V ())
    (((⟨e, e.continuous⟩ : C(E, F)).comp (w ω)).comp ⟨φ, φ.continuous⟩)
  let H : C(ℝ≥0, E) → C(ℝ≥0, F) := fun q =>
    ((⟨e, e.continuous⟩ : C(E, F)).comp q).comp ⟨φ, φ.continuous⟩
  let K : C(ℝ≥0, F) → C(ℝ≥0, E) := fun q =>
    ((⟨e.symm, e.symm.continuous⟩ : C(F, E)).comp q).comp ⟨φ.symm, φ.symm.continuous⟩
  have hH : Measurable H := by
    apply Continuous.measurable
    exact (ContinuousMap.continuous_precomp ⟨φ, φ.continuous⟩).comp
      (ContinuousMap.continuous_postcomp (⟨e, e.continuous⟩ : C(E, F)))
  have hK : Measurable K := by
    apply Continuous.measurable
    exact (ContinuousMap.continuous_precomp ⟨φ.symm, φ.symm.continuous⟩).comp
      (ContinuousMap.continuous_postcomp (⟨e.symm, e.symm.continuous⟩ : C(F, E)))
  have hBA : B =ᵐ[μ] H ∘ A := by
    filter_upwards [hfin] with ω hω
    exact stoppedPath_openExit_comp_spatial_orderIso (w ω)
      (⟨e, e.continuous⟩ : C(E, F)) φ V hV hω
  have hAB : A =ᵐ[μ] K ∘ B := by
    filter_upwards [hBA] with ω hω
    change A ω = K (B ω)
    rw [hω]
    ext t
    simp only [Function.comp_apply, H, K, ContinuousMap.coe_comp,
      ContinuousMap.coe_mk, e.symm_apply_apply, φ.apply_symm_apply]
  change AELeSigma (MeasurableSpace.comap B _) (MeasurableSpace.comap A _) μ ∧
    AELeSigma (MeasurableSpace.comap A _) (MeasurableSpace.comap B _) μ
  exact ⟨AELeSigma.comap_of_ae_eq (hH.comp (comap_measurable A)) hBA,
    AELeSigma.comap_of_ae_eq (hK.comp (comap_measurable B)) hAB⟩

end LatticeProb
