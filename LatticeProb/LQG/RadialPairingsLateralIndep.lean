import LatticeProb.LQG.RadialLateralIndep
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.ReplacedDefs

/-! # Independence of radial pairings and the lateral field -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory LQGMetric
open MatedCRTHarmonic.GMCFacts MatedCRTHarmonic.MoTPort

namespace LatticeProb.LQG

/-- The radial pairings of a continuous centered radial version of a whole-plane
GFF are independent of its lateral field. The version identity is needed only
at each fixed time, and the pairing identities only at each fixed test. -/
theorem IsWholePlaneGFF.indepFun_radialPairings_lateralPart
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → DistC}
    (hX : IsWholePlaneGFF X P) {ρ : Ω → C(ℝ, ℝ)} (hρm : Measurable ρ)
    (hρ : ∀ t, (fun ω => ρ ω t) =ᵐ[P]
      fun ω => circleAvg (X ω) (Real.exp (-t)) 0 - circleAvg (X ω) 1 0)
    {ι : Type*} (ψ : ι → TestC0) :
    IndepFun (fun ω i => pairW (symmTest (ψ i).1) (ρ ω))
      (fun ω => lateralPartC (X ω)) P := by
  have := hX.gaussian.isProbabilityMeasure
  let ψs : ι → TestC0 := fun i => ⟨symmTest (ψ i).1, by
    rw [integral_symmTest]
    exact (ψ i).2⟩
  have hind : IndepFun (fun ω i => X ω (ψs i).1)
      (fun ω => lateralPartC (X ω)) P := by
    apply IsWholePlaneGFF.indepFun_pairing_lateralPart hX ψs
    intro i
    exact isRotInv_rotSymm (ψ i).1
  have hlat : Measurable (fun ω => lateralPartC (X ω)) :=
    MatedCRTHarmonic.ConeScaling.measurable_lateralPart.comp hX.measurable
  have hpair : Measurable (fun ω i => pairW (symmTest (ψ i).1) (ρ ω)) :=
    measurable_pi_iff.2 fun i => (measurable_pairW _).comp hρm
  apply (indepFun_of_forall_ae_eq_apply hlat hpair hind.symm ?_).symm
  intro i
  exact ae_pairW_radialProcess hX hρm hρ (ψ i).2

end LatticeProb.LQG
