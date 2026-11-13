/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4cS.AffineAreaReader at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cS.AffineAreaSelection
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cO.ZeroConeLocality

/-! One Borel GMC reader for the root zero-cone and all admissible recentrings. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped NNReal ENNReal

namespace MatedCRTHarmonic.GMS4cS

open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.L43O
open MatedCRTHarmonic.GMS4c LQGMetric
open LQGMetric (DistOn CONF.resUW CONF.measurable_resUW CONF.resUW_restrictTo)

theorem zeroConeAreaLocality_of_localSelector
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (W V : TopologicalSpace.Opens ℂ)
    (hW : (W : Set ℂ) ⊆ ball (0 : ℂ) 1)
    (hVb : Bornology.IsBounded (V : Set ℂ)) (hVc : (V : Set ℂ)ᶜ.Nonempty)
    {δ : ℝ} (hδ : 0 < δ) (hVW : thickOpen V δ ≤ W)
    (J : ℂ ≃ₜ ℂ) (hJb : Bornology.IsBounded (J '' (V : Set ℂ)))
    (hJH : J '' (V : Set ℂ) ⊆ QuantumZipper.H)
    (hJc : (J '' (V : Set ℂ))ᶜ.Nonempty) :
    ZeroConeAreaLocality D W V := by
  have := D.isProbabilityMeasure
  let T : Ω → DistOn (thickOpen V δ) :=
    fun ω => restrictTo (thickOpen V δ) (zeroConeField γ X₀ B₀ B₀' ω)
  have hTm : AEMeasurable T P :=
    (measurable_restrictTo (thickOpen V δ)).comp_aemeasurable
      (GMS4.aemeasurable_prop48ZeroConeField D)
  have hcert : ∀ᵐ T' ∂P.map T, shiftedLocalAreaCert γ V δ J T' := by
    have hbase := ae_zero_shiftedLocalAreaCert_law D hγ V hVb hδ J hJb
    have hraw : (fun ω => restrictTo (thickOpen V δ)
        (GMS4b.l46tZeroConeFieldVersion D ω)) =ᵐ[P] T := by
      filter_upwards [GMS4b.l46tZeroConeFieldVersion_ae_eq_raw D hγ] with ω hω
      congr 1
      simpa only [T, zeroConeField, GMS4b.l46tZeroConeCellModel] using hω.symm
    change ∀ᵐ T' ∂P.map (fun ω => restrictTo (thickOpen V δ)
      (GMS4b.l46tZeroConeFieldVersion D ω)), shiftedLocalAreaCert γ V δ J T' at hbase
    rwa [Measure.map_congr hraw] at hbase
  have hgood : ∀ᵐ T' ∂P.map T,
      MoTPort.ConeArea4.AreaGood V (localAreaApproxDy γ V δ T') :=
    hcert.mono (fun T' hc => localAreaGood_of_shiftedCert γ V δ J hJH hJc T' hc)
  obtain ⟨F, hFm, hFa⟩ :=
    exists_measurable_localAreaVagueSelectionLoc γ V hVb hVc δ (P.map T) hgood
  let F' : DistOn W → Measure ℂ := fun x => F (CONF.resUW W (thickOpen V δ) x)
  have hF' : Measurable F' := hFm.comp (CONF.measurable_resUW W (thickOpen V δ))
  have hVδ : (thickOpen V δ : Set ℂ) ⊆ ball (0 : ℂ) 1 :=
    fun x hx => hW (hVW hx)
  refine ⟨F', hF', ?_, ?_⟩
  · filter_upwards [ae_of_ae_map hTm hFa,
      ae_zero_localAreaVagueSelectionLoc_correct D hγ V hVb hδ J hJb hJH hJc]
      with ω hF harea
    have hres : F' (restrictTo W (zeroConeField γ X₀ B₀ B₀' ω)) = F (T ω) :=
      congrArg F (CONF.resUW_restrictTo hVW _)
    rw [hres, hF, harea]
    rw [Measure.restrict_restrict V.isOpen.measurableSet, inter_self]
  · intro z r hr hzr
    let T' : Ω → DistOn (thickOpen V δ) :=
      fun ω => restrictTo (thickOpen V δ)
        (IGLaw.affField r 0 z (zeroConeField γ X₀ B₀ B₀' ω))
    have hT'm : AEMeasurable T' P :=
      ((measurable_restrictTo (thickOpen V δ)).comp
        (IGLaw.measurable_affField r 0 z)).comp_aemeasurable
          (GMS4.aemeasurable_prop48ZeroConeField D)
    have hA : AEMeasurable (fun ω => circleAvg (zeroConeField γ X₀ B₀ B₀' ω) r z) P :=
      (measurable_circleAvg_left r z).comp_aemeasurable
        (GMS4.aemeasurable_prop48ZeroConeField D)
    have hmap : P.map T' = P.map T := by
      exact L43O.map_snd_of_map_eq_prod hA hT'm
        (map_circleAvg_restrict_affField_zeroCone D hγ
          hVδ hr hzr)
    have hFae : ∀ᵐ T'' ∂P.map T', F T'' = localAreaVagueSelectionLoc γ V δ T'' := by
      rw [hmap]
      exact hFa
    filter_upwards [ae_of_ae_map hT'm hFae,
      ae_affine_localAreaVagueSelectionLoc_correct D hγ V hVb hδ
        hVδ J hJb hJH hJc hr hzr]
      with ω hF harea
    have hres : F' (restrictTo W
        (IGLaw.affField r 0 z (zeroConeField γ X₀ B₀ B₀' ω))) = F (T' ω) :=
      congrArg F (CONF.resUW_restrictTo hVW _)
    rw [hres, hF, harea]
    rw [Measure.restrict_restrict V.isOpen.measurableSet, inter_self]

end MatedCRTHarmonic.GMS4cS

