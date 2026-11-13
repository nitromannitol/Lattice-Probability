/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTInput.AreaDominates at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTInput.CellModel
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.ConeCompare

/-!
# Area domination from the mating bundle

The pathwise cone-versus-whole-plane comparison applies to the cell model induced by the
mating bundle. The cone-area existence theorem supplies `ConeAreaExists`; the GFF, Brownian
motions, independence, and cone-area field identity come from the bundle itself.

`cellModelOfCoupling` takes the parameter condition `hγ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace MatedCRTHarmonic.MoTInput

open MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- the area-domination obligation for the cell model induced by the mating bundle. The cone-area existence
hypothesis is no longer needed (GMCF proves it as `coneAreaExists_holds`); it is kept for API stability and is unused. -/
theorem areaDominatesWholePlaneGFF_of_coupling
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (_hconeArea : GMCFacts.ConeAreaExists γ P X B B') :
    GMSLemma27.AreaDominatesWholePlaneGFF (cellModelOfCoupling D hγ) := by
  apply GMCFacts.areaDominates_of_cone (cellModelOfCoupling D hγ) hγ.1 hγ.2
    D.gff D.bm_B D.bm_B' D.indep_cone ?_
  filter_upwards [] with ω
  rfl

end MatedCRTHarmonic.MoTInput
