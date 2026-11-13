/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4cS.AffineAreaSelection at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cS.AffineVague
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cS.AffineAreaCertificate
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.LocalAreaSelectionCorrect

/-! The Borel local GMC selector equals the actual area after affine recentering. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped NNReal ENNReal

namespace MatedCRTHarmonic.GMS4cS

open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.L43O
open LQGMetric

theorem ae_affine_localAreaVagueSelectionLoc_correct
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (V : TopologicalSpace.Opens ℂ) (hVb : Bornology.IsBounded (V : Set ℂ))
    {δ : ℝ} (hδ : 0 < δ)
    (hVδ : (GMS4c.thickOpen V δ : Set ℂ) ⊆ ball (0 : ℂ) 1)
    (J : ℂ ≃ₜ ℂ) (hJb : Bornology.IsBounded (J '' (V : Set ℂ)))
    (hJH : J '' (V : Set ℂ) ⊆ QuantumZipper.H)
    (hJc : (J '' (V : Set ℂ))ᶜ.Nonempty)
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hzr : closedBall z r ⊆ ball (0 : ℂ) 1) :
    ∀ᵐ ω ∂P,
      GMS4c.localAreaVagueSelectionLoc γ V δ
        (restrictTo (GMS4c.thickOpen V δ)
          (IGLaw.affField r 0 z (zeroConeField γ X₀ B₀ B₀' ω))) =
      (CellScaling.lqgArea γ
        (IGLaw.affField r 0 z (zeroConeField γ X₀ B₀ B₀' ω))).restrict V := by
  filter_upwards [ae_affine_shiftedLocalAreaCert D hγ V hVb hδ hVδ J hJb hr hzr,
    ae_affine_zeroCone_localCircle_continuous_eventually D hγ V hδ hr z,
    ae_affine_zeroCone_vague D hγ] with ω hcert hcont hvague
  let h := IGLaw.affField r 0 z (zeroConeField γ X₀ B₀ B₀' ω)
  have hlim := GMS4c.isVagueLimitOn_localAreaApproxDy_of_ae_continuous
    γ V hδ h hcont (hvague r hr z)
  have hgood := GMS4c.localAreaGood_of_shiftedCert γ V δ J hJH hJc _ hcert
  exact QuantumZipper.isVagueLimitOn_unique V.isOpen
    (GMS4c.localAreaVagueSelectionLoc_spec hgood) hlim

end MatedCRTHarmonic.GMS4cS

