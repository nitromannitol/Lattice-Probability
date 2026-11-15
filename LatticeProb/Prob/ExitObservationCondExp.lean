import LatticeProb.Prob.AEExitObservationSigmaTransform
import LatticeProb.Prob.CompletedHistoryCondExp

/-! # Conditional expectations under transformed exit observations -/

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace LatticeProb

/-- Almost surely equivalent ambient sub-sigma-algebras give the same conditional
expectation of an integrable real function. -/
theorem condExp_ae_eq_of_mutual_aeLeSigma
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    {F G : MeasurableSpace Ω} (hF : F ≤ m) (hG : G ≤ m)
    (hFG : AELeSigma F G μ) (hGF : AELeSigma G F μ)
    {f : Ω → ℝ} (hf : Integrable f μ) :
    μ[f | F] =ᵐ[μ] μ[f | G] := by
  have hJF : AELeSigma (F ⊔ G) F μ :=
    AELeSigma.sup (AELeSigma.of_le le_rfl) hGF
  have hJG : AELeSigma (F ⊔ G) G μ :=
    AELeSigma.sup hFG (AELeSigma.of_le le_rfl)
  exact (condExp_ae_eq_of_aeLeSigma (le_sup_left : F ≤ F ⊔ G)
    (sup_le hF hG) hJF hf).trans
      (condExp_ae_eq_of_aeLeSigma (le_sup_right : G ≤ F ⊔ G)
        (sup_le hF hG) hJG hf).symm

/-- A fixed homeomorphism and increasing bijective clock preserve conditional
expectations given the stopped-path observation, when the exit is finite almost
surely and both observations are measurable on the ambient space. -/
theorem condExp_stoppedPath_openExit_comp_spatial_orderIso
    {Ω E F : Type*} [m : MeasurableSpace Ω] [TopologicalSpace E] [TopologicalSpace F]
    (μ : Measure Ω) [IsFiniteMeasure μ] (w : Ω → C(ℝ≥0, E))
    (e : E ≃ₜ F) (φ : ℝ≥0 ≃o ℝ≥0) (V : Set F) (hV : IsOpen V)
    (hfin : ∀ᵐ ω ∂μ, openExitTime (fun t (_ : Unit) => w ω t) (e ⁻¹' V) () ≠ ⊤)
    (hA : Measurable fun ω => stoppedPath
      (openExitTime (fun t (_ : Unit) => w ω t) (e ⁻¹' V) ()) (w ω))
    (hB : Measurable fun ω => stoppedPath
      (openExitTime (fun t (_ : Unit) => e (w ω (φ t))) V ())
      (((⟨e, e.continuous⟩ : C(E, F)).comp (w ω)).comp ⟨φ, φ.continuous⟩))
    {f : Ω → ℝ} (hf : Integrable f μ) :
    let A := fun ω => stoppedPath
      (openExitTime (fun t (_ : Unit) => w ω t) (e ⁻¹' V) ()) (w ω)
    let B := fun ω => stoppedPath
      (openExitTime (fun t (_ : Unit) => e (w ω (φ t))) V ())
      (((⟨e, e.continuous⟩ : C(E, F)).comp (w ω)).comp ⟨φ, φ.continuous⟩)
    μ[f | MeasurableSpace.comap A inferInstance] =ᵐ[μ]
      μ[f | MeasurableSpace.comap B inferInstance] := by
  dsimp only
  obtain ⟨hBA, hAB⟩ :=
    aeLeSigma_stoppedPath_openExit_comp_spatial_orderIso μ w e φ V hV hfin
  apply condExp_ae_eq_of_mutual_aeLeSigma (m := m) (μ := μ)
    (F := MeasurableSpace.comap (fun ω => stoppedPath
      (openExitTime (fun t (_ : Unit) => w ω t) (e ⁻¹' V) ()) (w ω)) inferInstance)
    (G := MeasurableSpace.comap (fun ω => stoppedPath
      (openExitTime (fun t (_ : Unit) => e (w ω (φ t))) V ())
      (((⟨e, e.continuous⟩ : C(E, F)).comp (w ω)).comp ⟨φ, φ.continuous⟩)) inferInstance)
    hA.comap_le hB.comap_le hAB hBA hf

end LatticeProb
