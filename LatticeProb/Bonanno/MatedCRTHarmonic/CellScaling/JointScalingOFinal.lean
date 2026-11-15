/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.CellScaling.JointScalingOFinal at commit fdb5cad; imports adapted and documentation omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.JointScalingOMain
import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.OPositiveRadii



set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.CellScaling

namespace JointScalingO

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}


theorem curveDilationLaw_of_coupling
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    CurveDilationLaw P ηL :=
  fun _ hs => IGLaw.IsMatingOfTreesCoupling.map_affineReroot_ηL D 0 hs 0


theorem coneJointScaling_holds
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2) :
    ConeJointScaling (MoTInput.coneRealizationOfCoupling D hstd hγ) :=
  coneJointScaling_of_coupling D hstd hγ (curveDilationLaw_of_coupling D)


theorem matedCRTProposition23GridScalingInput_holds
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2) :
    MesoModel.MatedCRTProposition23GridScalingInput (MoTInput.unitMesoModelOfCoupling D hstd hγ) :=
  matedCRTProposition23GridScalingInput_of_coupling D hstd hγ (curveDilationLaw_of_coupling D)

end Coupling


theorem coneJointScaling_forAllCouplings :
    ∀ (γ : ℝ) (hγ : γ ∈ Ioo 0 2) (Ω : Type) (_ : MeasurableSpace Ω) (hstd : StandardBorelSpace Ω)
      (P : Measure Ω) (X X₀ hIG₀ : Ω → MatedCRT.Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
      (ηL η η₀ : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2)
      (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm),
      ConeJointScaling (MoTInput.coneRealizationOfCoupling D hstd hγ) :=
  fun _ hγ _ _ hstd _ _ _ _ _ _ _ _ _ _ _ _ _ D => coneJointScaling_holds D hstd hγ

end JointScalingO

end MatedCRTHarmonic.CellScaling
