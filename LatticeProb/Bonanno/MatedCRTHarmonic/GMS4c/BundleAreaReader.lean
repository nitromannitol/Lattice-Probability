/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4c.BundleAreaReader at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.BundleAreaCert
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.LocalAreaSelectionShift
import LatticeProb.Bonanno.MatedCRTHarmonic.BundleSec4.L46TAdapter
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.L46TZeroVersion

/-! A single Borel reader of the restricted GMC area under both measurable
cone-field versions. -/

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

/-- The good-sample condition holds under the law of the measurable
gamma-cone field restriction. -/
theorem ae_gamma_shiftedLocalAreaCert_law
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀
      B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (V : TopologicalSpace.Opens ℂ) (hVb : Bornology.IsBounded (V : Set ℂ))
    {δ : ℝ} (hδ : 0 < δ) (J : ℂ ≃ₜ ℂ)
    (hJb : Bornology.IsBounded (J '' (V : Set ℂ))) :
    ∀ᵐ T ∂P.map (restrictTo (thickOpen V δ) ∘ BundleSec4.coneFieldVersion D),
      shiftedLocalAreaCert γ V δ J T := by
  let f : Ω → DistOn (thickOpen V δ) :=
    restrictTo (thickOpen V δ) ∘ BundleSec4.coneFieldVersion D
  have hf : Measurable f :=
    (measurable_restrictTo (thickOpen V δ)).comp
      (BundleSec4.measurable_coneFieldVersion D)
  apply (ae_map_iff hf.aemeasurable
    (measurableSet_shiftedLocalAreaCert γ V δ J)).2
  filter_upwards [ae_gamma_shiftedLocalAreaCert D hγ V hVb hδ J hJb,
    (BundleSec4.coneFieldVersion_ae_eq D hγ).symm] with ω hc heq
  simpa [f, MoTInput.cellModelOfCoupling, heq] using hc

/-- The same certificate holds under the measurable zero-cone field law. -/
theorem ae_zero_shiftedLocalAreaCert_law
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀
      B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (V : TopologicalSpace.Opens ℂ) (hVb : Bornology.IsBounded (V : Set ℂ))
    {δ : ℝ} (hδ : 0 < δ) (J : ℂ ≃ₜ ℂ)
    (hJb : Bornology.IsBounded (J '' (V : Set ℂ))) :
    ∀ᵐ T ∂P.map (restrictTo (thickOpen V δ) ∘
        GMS4b.l46tZeroConeFieldVersion D),
      shiftedLocalAreaCert γ V δ J T := by
  let f : Ω → DistOn (thickOpen V δ) :=
    restrictTo (thickOpen V δ) ∘ GMS4b.l46tZeroConeFieldVersion D
  have hf : Measurable f :=
    (measurable_restrictTo (thickOpen V δ)).comp
      (GMS4b.l46tZeroConeFieldVersion_measurable D)
  apply (ae_map_iff hf.aemeasurable
    (measurableSet_shiftedLocalAreaCert γ V δ J)).2
  filter_upwards [ae_zero_shiftedLocalAreaCert D hγ V hVb hδ J hJb,
    (GMS4b.l46tZeroConeFieldVersion_ae_eq_raw D hγ).symm] with ω hc heq
  simpa [f, GMS4b.l46tZeroConeCellModel, heq] using hc

theorem ae_gamma_localAreaVagueSelectionLoc_correct
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀
      B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (V : TopologicalSpace.Opens ℂ) (hVb : Bornology.IsBounded (V : Set ℂ))
    {δ : ℝ} (hδ : 0 < δ) (J : ℂ ≃ₜ ℂ)
    (hJb : Bornology.IsBounded (J '' (V : Set ℂ)))
    (hJH : J '' (V : Set ℂ) ⊆ QuantumZipper.H)
    (hJc : (J '' (V : Set ℂ))ᶜ.Nonempty) :
    ∀ᵐ ω ∂P,
      localAreaVagueSelectionLoc γ V δ
        (restrictTo (thickOpen V δ)
          (coneField (X ω) (coneRadial γ γ
            (fun t => B t ω) (fun t => B' t ω)))) =
      (CellScaling.lqgArea γ (coneField (X ω) (coneRadial γ γ
        (fun t => B t ω) (fun t => B' t ω)))).restrict V := by
  filter_upwards [ae_gamma_shiftedLocalAreaCert D hγ V hVb hδ J hJb,
    ae_gamma_localDyadicGood D hγ V hVb hδ,
    ae_gamma_localAreaVagueSelection_correct D hγ V hVb hδ]
      with ω hc hg heq
  exact (localAreaVagueSelectionLoc_eq_selected hJH hJc hc hg).trans heq

theorem ae_zero_localAreaVagueSelectionLoc_correct
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀
      B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (V : TopologicalSpace.Opens ℂ) (hVb : Bornology.IsBounded (V : Set ℂ))
    {δ : ℝ} (hδ : 0 < δ) (J : ℂ ≃ₜ ℂ)
    (hJb : Bornology.IsBounded (J '' (V : Set ℂ)))
    (hJH : J '' (V : Set ℂ) ⊆ QuantumZipper.H)
    (hJc : (J '' (V : Set ℂ))ᶜ.Nonempty) :
    ∀ᵐ ω ∂P,
      localAreaVagueSelectionLoc γ V δ
        (restrictTo (thickOpen V δ)
          (coneField (X₀ ω) (coneRadial γ 0
            (fun t => B₀ t ω) (fun t => B₀' t ω)))) =
      (CellScaling.lqgArea γ (coneField (X₀ ω) (coneRadial γ 0
        (fun t => B₀ t ω) (fun t => B₀' t ω)))).restrict V := by
  filter_upwards [ae_zero_shiftedLocalAreaCert D hγ V hVb hδ J hJb,
    ae_zero_localDyadicGood D hγ V hVb hδ,
    ae_zero_localAreaVagueSelection_correct D hγ V hVb hδ]
      with ω hc hg heq
  exact (localAreaVagueSelectionLoc_eq_selected hJH hJc hc hg).trans heq

/-- **Borel field-to-area reconstruction under both cone laws.** The two
measurable field versions share one reader of the GMC area restricted to `V`.
The equalities are almost sure, as required by. -/
theorem exists_borel_bundle_localAreaReader
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀
      B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (V : TopologicalSpace.Opens ℂ) (hVb : Bornology.IsBounded (V : Set ℂ))
    (hVc : (V : Set ℂ)ᶜ.Nonempty)
    {δ : ℝ} (hδ : 0 < δ) (J : ℂ ≃ₜ ℂ)
    (hJb : Bornology.IsBounded (J '' (V : Set ℂ)))
    (hJH : J '' (V : Set ℂ) ⊆ QuantumZipper.H)
    (hJc : (J '' (V : Set ℂ))ᶜ.Nonempty) :
    ∃ F : DistOn (thickOpen V δ) → Measure ℂ,
      Measurable F ∧
      (∀ᵐ ω ∂P,
        F (restrictTo (thickOpen V δ) (BundleSec4.coneFieldVersion D ω)) =
          (CellScaling.lqgArea γ (coneField (X ω) (coneRadial γ γ
            (fun t => B t ω) (fun t => B' t ω)))).restrict V) ∧
      (∀ᵐ ω ∂P,
        F (restrictTo (thickOpen V δ) (GMS4b.l46tZeroConeFieldVersion D ω)) =
          (CellScaling.lqgArea γ (coneField (X₀ ω) (coneRadial γ 0
            (fun t => B₀ t ω) (fun t => B₀' t ω)))).restrict V) := by
  let fγ : Ω → DistOn (thickOpen V δ) :=
    restrictTo (thickOpen V δ) ∘ BundleSec4.coneFieldVersion D
  let f₀ : Ω → DistOn (thickOpen V δ) :=
    restrictTo (thickOpen V δ) ∘ GMS4b.l46tZeroConeFieldVersion D
  have hmγ : Measurable fγ :=
    (measurable_restrictTo (thickOpen V δ)).comp
      (BundleSec4.measurable_coneFieldVersion D)
  have hm₀ : Measurable f₀ :=
    (measurable_restrictTo (thickOpen V δ)).comp
      (GMS4b.l46tZeroConeFieldVersion_measurable D)
  obtain ⟨F, hFm, hFγ, hF₀⟩ :=
    exists_measurable_localAreaVagueSelectionLoc_twoLaws_of_shiftedCert
      γ V hVb hVc δ J hJH hJc (P.map fγ) (P.map f₀)
      (ae_gamma_shiftedLocalAreaCert_law D hγ V hVb hδ J hJb)
      (ae_zero_shiftedLocalAreaCert_law D hγ V hVb hδ J hJb)
  refine ⟨F, hFm, ?_, ?_⟩
  · filter_upwards [ae_of_ae_map hmγ.aemeasurable hFγ,
      (BundleSec4.coneFieldVersion_ae_eq D hγ).symm,
      ae_gamma_localAreaVagueSelectionLoc_correct D hγ V hVb hδ J hJb hJH hJc]
      with ω hf heq hs
    simp only [fγ, Function.comp_apply, heq, MoTInput.cellModelOfCoupling] at hf
    rw [show BundleSec4.coneFieldVersion D ω = coneField (X ω)
        (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω)) by
          simpa [MoTInput.cellModelOfCoupling] using heq]
    exact hf.trans hs
  · filter_upwards [ae_of_ae_map hm₀.aemeasurable hF₀,
      (GMS4b.l46tZeroConeFieldVersion_ae_eq_raw D hγ).symm,
      ae_zero_localAreaVagueSelectionLoc_correct D hγ V hVb hδ J hJb hJH hJc]
      with ω hf heq hs
    simp only [f₀, Function.comp_apply, heq, GMS4b.l46tZeroConeCellModel] at hf
    rw [show GMS4b.l46tZeroConeFieldVersion D ω = coneField (X₀ ω)
        (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω)) by
          simpa [GMS4b.l46tZeroConeCellModel] using heq]
    exact hf.trans hs

end MatedCRTHarmonic.GMS4c

