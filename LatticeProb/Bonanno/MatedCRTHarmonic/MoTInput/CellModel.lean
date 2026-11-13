/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTInput.CellModel at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTPath2
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTField
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.ConeDefs
import LatticeProb.Bonanno.MatedCRTHarmonic.MesoModel.FrozenIdentities
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.CellModel

/-!
# The LQG cell model carried by the mating-of-trees bundle

This module adapts the γ-cone and area-parametrized curve fields of the mating-of-trees bundle to
the abstract cell-model interface used by [18].

Re-based onto the frozen surface v3. The frozen field `areaParam`
quantifies over every dyadic vague limit of the area approximations (S1Y R1) and the frozen surface
has no `lqgArea`; the area of the model is the non-frozen library definition `CellScaling.lqgArea`
(the chosen vague limit), which is a vague limit almost surely for `γ ∈ (0, 2)` by the closure
anchor NJ1 (`MesoModel.FrozenIdentities.ae_exists_isVagueLimitC_cone`). Hence the new argument
`hγ : γ ∈ Ioo 0 2` (the convention of `unitMesoModelOfCoupling`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.MoTInput

open MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- Instantiate the [18] cell-model interface from a mating-of-trees coupling, for `γ ∈ (0, 2)`. -/
def cellModelOfCoupling (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    GMSLemma27.CellModel γ where
  Ω := Ω
  measurableSpace := inferInstance
  P := P
  isProbabilityMeasure := D.isProbabilityMeasure
  field := fun ω => coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω))
  area := fun ω => CellScaling.lqgArea γ (coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω)))
  curve := fun ω => η ω
  ae_continuous_curve := Filter.Eventually.of_forall (fun ω => (η ω).continuous)
  ae_curve_zero := by
    filter_upwards [D.areaParam, D.spaceFilling] with ω harea hspace
    rcases harea with ⟨⟨φ, hφ0, hηeq⟩, _⟩
    rcases hspace with ⟨_, _, hηL0, _⟩
    rw [hηeq, hφ0, hηL0]
  ae_area_curve := by
    filter_upwards [D.areaParam, MesoModel.FrozenIdentities.ae_exists_isVagueLimitC_cone D hγ] with ω harea hex
    have hex' : ∃ μ : Measure ℂ, CellScaling.IsVagueLimitC (CellScaling.lqgAreaApprox γ
        (coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω)))) μ := hex
    intro a b hab
    rw [CellScaling.lqgArea, dite_eq_left hex']
    exact harea.2 _ hex'.choose_spec a b hab

end MatedCRTHarmonic.MoTInput
