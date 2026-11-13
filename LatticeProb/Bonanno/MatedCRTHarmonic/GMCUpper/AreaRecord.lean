/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMCUpper.AreaRecord at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCUpper.ZeroConeMass
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop410Rooting
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.BallMoment
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCUpper.TranslatedMoment
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.JointScalingOPath

/-! The whole-plane area record of Proposition 4.8 identifies the same canonical GMC. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric LQGMetric Filter Topology
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMCUpper

open MatedCRTHarmonic.GMSLemma27

/-- An almost-sure identification of a cell model's area transfers the upper
mass event without requiring equality on null samples. -/
theorem upperMassBound_of_ae_area
    {γ : ℝ} (M : CellModel γ) (μ : M.Ω → Measure ℂ)
    (harea : ∀ᵐ ω ∂M.P, M.area ω = μ ω)
    (hbound : ∃ ξ β : ℝ, 0 < ξ ∧ 0 < β ∧
      ∀ ρ ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, ∀ δ ∈ Ioo (0 : ℝ) 1,
        M.P {ω | ∃ z ∈ ball (0 : ℂ) ρ,
          ENNReal.ofReal (δ ^ ξ) < μ ω (ball z δ)} ≤
          ENNReal.ofReal (C * δ ^ β)) :
    MatedCRTHarmonic.GMS4b.UpperMassBound M := by
  obtain ⟨ξ, β, hξ, hβ, hb⟩ := hbound
  refine ⟨ξ, β, hξ, hβ, ?_⟩
  intro ρ hρ
  obtain ⟨C, hC⟩ := hb ρ hρ
  refine ⟨C, fun δ hδ => ?_⟩
  have hevent : {ω | ∃ z ∈ ball (0 : ℂ) ρ,
        ENNReal.ofReal (δ ^ ξ) < M.area ω (ball z δ)} =ᵐ[M.P]
      {ω | ∃ z ∈ ball (0 : ℂ) ρ,
        ENNReal.ofReal (δ ^ ξ) < μ ω (ball z δ)} := by
    filter_upwards [harea] with ω hω
    simp only [hω]
  exact (measure_congr hevent).le.trans (hC δ hδ)

/-- G4b's upper-mass input for a cell model whose area is the frozen
coupling's zero-cone GMC, up to a null set. -/
theorem upperMassBoundZeroCone_toCellModel
    {γ : ℝ} (M : CellModel γ)
    {X X₀ hIG₀ : M.Ω → MatedCRTHarmonic.MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → M.Ω → ℝ} {U : M.Ω → ℝ}
    {ηL η η₀ : M.Ω → C(ℝ, ℂ)} {bm : M.Ω → MatedCRTHarmonic.MatedCRT.Path2}
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (D : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling
      γ M.P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (harea : ∀ᵐ ω ∂M.P, M.area ω = zeroConeArea γ X₀ B₀ B₀' ω) :
    MatedCRTHarmonic.GMS4b.UpperMassBound M :=
  upperMassBound_of_ae_area M (zeroConeArea γ X₀ B₀ B₀') harea
    (upperMassBoundZeroConeModel_holds hγ D)

end MatedCRTHarmonic.GMCUpper

