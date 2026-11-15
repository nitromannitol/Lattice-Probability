/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source modules MatedCRTHarmonic.Canon.Data and MatedCRTHarmonic.Canon.ClockMeasurable
   at commit fdb5cad17d11550228cf8dbaf6216e69fc3d2d82, lines 36–41, 79–85 and 36–50. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTInput.CellModel
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeMeas2
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCone.AreaBridge

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.Canon

open MatedCRTHarmonic.MatedCRT

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
  {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- The cone's field, GMC area, area-time SLE and boundary Brownian motion. -/
structure ConeSample where
  field : MatedCRT.Field
  area : Measure ℂ
  curve : C(ℝ, ℂ)
  boundary : Path2

def coneSample
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ω : Ω) : ConeSample :=
  { field := (MoTInput.cellModelOfCoupling D hγ).field ω
    area := (MoTInput.cellModelOfCoupling D hγ).area ω
    curve := η ω
    boundary := bm ω }

/-- The cone field is almost surely measurable from the frozen GFF and
radial Brownian paths. -/
theorem aemeasurable_cone_field
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    AEMeasurable (fun ω => (coneSample D hγ ω).field) P := by
  letI : IsProbabilityMeasure P := D.isProbabilityMeasure
  let A : ℝ → Ω → ℝ := fun t ω =>
    LQGCone.motConeRadial γ γ (fun s => B s ω) (fun s => B' s ω) t
  have hA : MoTPort.IsConeProcess γ (QuantumZipper.Qc γ) A P :=
    LQGCone.isConeProcess_motConeRadial D.bm_B D.bm_B' D.indep_cone.2
  have hm := MoTPort.ConeMeas2.aemeasurable_coneField D.gff hA
  refine hm.congr (ae_of_all _ fun ω => ?_)
  exact (LQGCone.coneField_eq_motConeField γ γ (X ω)
    (fun t => B t ω) (fun t => B' t ω)).symm

end MatedCRTHarmonic.Canon
