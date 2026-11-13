/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4cS.AffineAreaCertificate at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.BundleAreaReader
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cO.Lemma49Core

/-!
# Local GMC certificate after affine recentring

The normalized zero-cone field on a disk strictly inside the unit disk has
The same local law after affine recentring. Thus every measurable local GMC
certificate valid under the root law is valid under the recentred law.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open MeasureTheory Set Metric
open scoped NNReal ENNReal

namespace MatedCRTHarmonic.GMS4cS

open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4c
open MatedCRTHarmonic.L43O LQGMetric

theorem ae_affine_shiftedLocalAreaCert_law
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (V : TopologicalSpace.Opens ℂ) (hVb : Bornology.IsBounded (V : Set ℂ))
    {δ : ℝ} (hδ : 0 < δ)
    (hVδ : (thickOpen V δ : Set ℂ) ⊆ ball (0 : ℂ) 1)
    (J : ℂ ≃ₜ ℂ) (hJb : Bornology.IsBounded (J '' (V : Set ℂ)))
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hzr : closedBall z r ⊆ ball (0 : ℂ) 1) :
    ∀ᵐ T ∂P.map (fun ω => restrictTo (thickOpen V δ)
        (IGLaw.affField r 0 z (zeroConeField γ X₀ B₀ B₀' ω))),
      shiftedLocalAreaCert γ V δ J T := by
  have := D.isProbabilityMeasure
  let W := thickOpen V δ
  let h₀ : Ω → Field := zeroConeField γ X₀ B₀ B₀'
  have hh₀ : AEMeasurable h₀ P := GMS4.aemeasurable_prop48ZeroConeField D
  have ha : AEMeasurable (fun ω => circleAvg (h₀ ω) r z) P :=
    (measurable_circleAvg_left r z).comp_aemeasurable hh₀
  have hb : AEMeasurable (fun ω => restrictTo W (IGLaw.affField r 0 z (h₀ ω))) P :=
    ((measurable_restrictTo W).comp (IGLaw.measurable_affField r 0 z)).comp_aemeasurable hh₀
  have hlaw : P.map (fun ω => restrictTo W (IGLaw.affField r 0 z (h₀ ω))) =
      P.map (fun ω => restrictTo W (h₀ ω)) :=
    map_snd_of_map_eq_prod ha hb
      (map_circleAvg_restrict_affField_zeroCone D hγ hVδ hr hzr)
  have hbase := ae_zero_shiftedLocalAreaCert_law D hγ V hVb hδ J hJb
  have hraw : (fun ω => restrictTo W (GMS4b.l46tZeroConeFieldVersion D ω)) =ᵐ[P]
      fun ω => restrictTo W (h₀ ω) := by
    filter_upwards [GMS4b.l46tZeroConeFieldVersion_ae_eq_raw D hγ] with ω hω
    congr 1
    simpa [h₀, zeroConeField, GMS4b.l46tZeroConeCellModel] using hω.symm
  change (∀ᵐ T ∂P.map (fun ω => restrictTo W
      (GMS4b.l46tZeroConeFieldVersion D ω)), shiftedLocalAreaCert γ V δ J T) at hbase
  rw [Measure.map_congr hraw] at hbase
  change ∀ᵐ T ∂P.map (fun ω => restrictTo W
      (IGLaw.affField r 0 z (h₀ ω))), shiftedLocalAreaCert γ V δ J T
  rw [hlaw]
  exact hbase

theorem ae_affine_shiftedLocalAreaCert
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (V : TopologicalSpace.Opens ℂ) (hVb : Bornology.IsBounded (V : Set ℂ))
    {δ : ℝ} (hδ : 0 < δ)
    (hVδ : (thickOpen V δ : Set ℂ) ⊆ ball (0 : ℂ) 1)
    (J : ℂ ≃ₜ ℂ) (hJb : Bornology.IsBounded (J '' (V : Set ℂ)))
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hzr : closedBall z r ⊆ ball (0 : ℂ) 1) :
    ∀ᵐ ω ∂P, shiftedLocalAreaCert γ V δ J
      (restrictTo (thickOpen V δ)
        (IGLaw.affField r 0 z (zeroConeField γ X₀ B₀ B₀' ω))) := by
  let h₀ : Ω → Field := zeroConeField γ X₀ B₀ B₀'
  have hh₀ : AEMeasurable h₀ P := GMS4.aemeasurable_prop48ZeroConeField D
  have hf : AEMeasurable (fun ω => restrictTo (thickOpen V δ)
      (IGLaw.affField r 0 z (h₀ ω))) P :=
    ((measurable_restrictTo (thickOpen V δ)).comp
      (IGLaw.measurable_affField r 0 z)).comp_aemeasurable hh₀
  exact ae_of_ae_map hf
    (ae_affine_shiftedLocalAreaCert_law D hγ V hVb hδ hVδ J hJb hr hzr)

end MatedCRTHarmonic.GMS4cS

