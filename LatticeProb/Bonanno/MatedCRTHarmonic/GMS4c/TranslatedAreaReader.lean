/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4c.TranslatedAreaReader at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.TranslatedArea
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.BundleAreaReader

/-! A common Borel local GMC reader for the translated gamma and zero cones. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace MatedCRTHarmonic.GMS4c

open LQGMetric MatedCRTHarmonic.MatedCRT

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field}
  {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- The translated gamma field satisfies the measurable GMC certificate. -/
theorem ae_gamma_translated_shiftedLocalAreaCert_law
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀
      B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (V : TopologicalSpace.Opens ℂ) (hVb : Bornology.IsBounded (V : Set ℂ))
    {δ : ℝ} (hδ : 0 < δ) (z₀ : ℂ) (J : ℂ ≃ₜ ℂ)
    (hJb : Bornology.IsBounded (J '' (V : Set ℂ))) :
    ∀ᵐ T ∂P.map (restrictTo (thickOpen V δ) ∘
        GMS4b.l46tTranslatedField z₀ (BundleSec4.coneFieldVersion D)),
      shiftedLocalAreaCert γ V δ J T := by
  let f : Ω → DistOn (thickOpen V δ) :=
    restrictTo (thickOpen V δ) ∘
      GMS4b.l46tTranslatedField z₀ (BundleSec4.coneFieldVersion D)
  have hf : Measurable f :=
    (measurable_restrictTo (thickOpen V δ)).comp
      ((measurable_affineComp 1 (-z₀)).comp (BundleSec4.measurable_coneFieldVersion D))
  apply (ae_map_iff hf.aemeasurable
    (measurableSet_shiftedLocalAreaCert γ V δ J)).2
  filter_upwards [ae_gamma_translated_shiftedLocalAreaCert D hγ V hVb hδ z₀ J hJb,
    (BundleSec4.coneFieldVersion_ae_eq D hγ).symm] with ω hc heq
  change shiftedLocalAreaCert γ V δ J
    (restrictTo (thickOpen V δ)
      (GMS4b.l46tTranslatedField z₀ (BundleSec4.coneFieldVersion D) ω))
  unfold GMS4b.l46tTranslatedField
  rw [heq]
  simpa only [MoTInput.cellModelOfCoupling, MesoModel.FrozenIdentities.coneField_eq_cellScaling,
    MesoModel.FrozenIdentities.coneRadial_eq_cellScaling] using hc

/-- Under the gamma law the local selector equals the translated area measure. -/
theorem ae_gamma_translated_localAreaVagueSelectionLoc_correct
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀
      B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (V : TopologicalSpace.Opens ℂ) (hVb : Bornology.IsBounded (V : Set ℂ))
    {δ : ℝ} (hδ : 0 < δ) (z₀ : ℂ) (J : ℂ ≃ₜ ℂ)
    (hJb : Bornology.IsBounded (J '' (V : Set ℂ)))
    (hJH : J '' (V : Set ℂ) ⊆ QuantumZipper.H)
    (hJc : (J '' (V : Set ℂ))ᶜ.Nonempty) :
    ∀ᵐ ω ∂P,
      localAreaVagueSelectionLoc γ V δ
        (restrictTo (thickOpen V δ)
          (GMS4b.l46tTranslatedField z₀ (MoTInput.cellModelOfCoupling D hγ).field ω)) =
      ((CellScaling.lqgArea γ ((MoTInput.cellModelOfCoupling D hγ).field ω)).map
        (fun x => x + z₀)).restrict V := by
  filter_upwards [ae_gamma_translated_shiftedLocalAreaCert D hγ V hVb hδ z₀ J hJb,
    ae_gamma_translated_localDyadicGood D hγ V hVb hδ z₀,
    ae_gamma_translated_localAreaVagueSelection_correct D hγ V hVb hδ z₀]
      with ω hc hg heq
  exact (localAreaVagueSelectionLoc_eq_selected hJH hJc hc hg).trans heq

/-- One Borel GMC reader works for the translated gamma field and the zero
cone on a bounded local region. -/
theorem exists_borel_translated_bundle_localAreaReader
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀
      B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (V : TopologicalSpace.Opens ℂ) (hVb : Bornology.IsBounded (V : Set ℂ))
    (hVc : (V : Set ℂ)ᶜ.Nonempty)
    {δ : ℝ} (hδ : 0 < δ) (z₀ : ℂ) (J : ℂ ≃ₜ ℂ)
    (hJb : Bornology.IsBounded (J '' (V : Set ℂ)))
    (hJH : J '' (V : Set ℂ) ⊆ QuantumZipper.H)
    (hJc : (J '' (V : Set ℂ))ᶜ.Nonempty) :
    ∃ F : DistOn (thickOpen V δ) → Measure ℂ,
      Measurable F ∧
      (∀ᵐ ω ∂P,
        F (restrictTo (thickOpen V δ)
          (GMS4b.l46tTranslatedField z₀ (MoTInput.cellModelOfCoupling D hγ).field ω)) =
          ((CellScaling.lqgArea γ ((MoTInput.cellModelOfCoupling D hγ).field ω)).map
            (fun x => x + z₀)).restrict V) ∧
      (∀ᵐ ω ∂P,
        F (restrictTo (thickOpen V δ) ((GMS4b.l46tZeroConeCellModel D hγ).field ω)) =
          (CellScaling.lqgArea γ ((GMS4b.l46tZeroConeCellModel D hγ).field ω)).restrict V) := by
  let fγ : Ω → DistOn (thickOpen V δ) :=
    restrictTo (thickOpen V δ) ∘
      GMS4b.l46tTranslatedField z₀ (BundleSec4.coneFieldVersion D)
  let f₀ : Ω → DistOn (thickOpen V δ) :=
    restrictTo (thickOpen V δ) ∘ GMS4b.l46tZeroConeFieldVersion D
  have hmγ : Measurable fγ :=
    (measurable_restrictTo (thickOpen V δ)).comp
      ((measurable_affineComp 1 (-z₀)).comp (BundleSec4.measurable_coneFieldVersion D))
  have hm₀ : Measurable f₀ :=
    (measurable_restrictTo (thickOpen V δ)).comp
      (GMS4b.l46tZeroConeFieldVersion_measurable D)
  obtain ⟨F, hFm, hFγ, hF₀⟩ :=
    exists_measurable_localAreaVagueSelectionLoc_twoLaws_of_shiftedCert
      γ V hVb hVc δ J hJH hJc (P.map fγ) (P.map f₀)
      (ae_gamma_translated_shiftedLocalAreaCert_law D hγ V hVb hδ z₀ J hJb)
      (ae_zero_shiftedLocalAreaCert_law D hγ V hVb hδ J hJb)
  refine ⟨F, hFm, ?_, ?_⟩
  · filter_upwards [ae_of_ae_map hmγ.aemeasurable hFγ,
      (BundleSec4.coneFieldVersion_ae_eq D hγ).symm,
      ae_gamma_translated_localAreaVagueSelectionLoc_correct D hγ V hVb hδ z₀ J hJb hJH hJc]
      with ω hf heq hs
    change F (fγ ω) = localAreaVagueSelectionLoc γ V δ (fγ ω) at hf
    change BundleSec4.coneFieldVersion D ω = (MoTInput.cellModelOfCoupling D hγ).field ω at heq
    have heqf : fγ ω = restrictTo (thickOpen V δ)
        (GMS4b.l46tTranslatedField z₀ (MoTInput.cellModelOfCoupling D hγ).field ω) := by
      change restrictTo (thickOpen V δ)
        (affineComp 1 (-z₀) (BundleSec4.coneFieldVersion D ω)) = _
      unfold GMS4b.l46tTranslatedField
      rw [heq]
    rw [heqf] at hf
    exact hf.trans hs
  · filter_upwards [ae_of_ae_map hm₀.aemeasurable hF₀,
      (GMS4b.l46tZeroConeFieldVersion_ae_eq_raw D hγ).symm,
      ae_zero_localAreaVagueSelectionLoc_correct D hγ V hVb hδ J hJb hJH hJc]
      with ω hf heq hs
    change F (f₀ ω) = localAreaVagueSelectionLoc γ V δ (f₀ ω) at hf
    change GMS4b.l46tZeroConeFieldVersion D ω =
      (GMS4b.l46tZeroConeCellModel D hγ).field ω at heq
    have heqf : f₀ ω = restrictTo (thickOpen V δ)
        ((GMS4b.l46tZeroConeCellModel D hγ).field ω) := by
      change restrictTo (thickOpen V δ)
        (GMS4b.l46tZeroConeFieldVersion D ω) = _
      rw [heq]
    rw [heqf] at hf
    exact hf.trans hs

end MatedCRTHarmonic.GMS4c

