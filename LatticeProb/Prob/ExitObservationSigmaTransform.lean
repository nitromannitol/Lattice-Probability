import LatticeProb.Prob.CombinedExitTransform

/-! # Sigma algebras of transformed exit observations -/

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace LatticeProb

/-- Fixed invertible spatial and clock transformations preserve the sigma algebra
of a continuous path stopped at a finite open-set exit. -/
theorem comap_stoppedPath_openExit_comp_spatial_orderIso
    {Ω E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    (w : Ω → C(ℝ≥0, E)) (e : E ≃ₜ F) (φ : ℝ≥0 ≃o ℝ≥0)
    (V : Set F) (hV : IsOpen V)
    (hfin : ∀ ω, openExitTime (fun t (_ : Unit) => w ω t) (e ⁻¹' V) () ≠ ⊤) :
    MeasurableSpace.comap
      (fun ω => stoppedPath
        (openExitTime (fun t (_ : Unit) => e (w ω (φ t))) V ())
        (((⟨e, e.continuous⟩ : C(E, F)).comp (w ω)).comp ⟨φ, φ.continuous⟩)) inferInstance =
    MeasurableSpace.comap
      (fun ω => stoppedPath
        (openExitTime (fun t (_ : Unit) => w ω t) (e ⁻¹' V) ()) (w ω)) inferInstance := by
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
  have hBA : B = H ∘ A := by
    funext ω
    exact stoppedPath_openExit_comp_spatial_orderIso (w ω) (⟨e, e.continuous⟩ : C(E, F)) φ V hV (hfin ω)
  have hAB : A = K ∘ B := by
    rw [hBA]
    funext ω
    ext t
    simp only [Function.comp_apply, H, K, ContinuousMap.coe_comp,
      ContinuousMap.coe_mk, e.symm_apply_apply, φ.apply_symm_apply]
  change MeasurableSpace.comap B _ = MeasurableSpace.comap A _
  exact le_antisymm (MeasurableSpace.comap_le_comap_of_eq_comp H hH hBA)
    (MeasurableSpace.comap_le_comap_of_eq_comp K hK hAB)

end LatticeProb
