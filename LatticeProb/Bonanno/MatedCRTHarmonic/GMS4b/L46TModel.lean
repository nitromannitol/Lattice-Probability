/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4b.L46TModel at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTInput.CellModel

/-!
# The zero-cone cell model for [18] Proposition 4.5

The frozen coupling carries the zero-quantum-cone field, its actual dyadic
LQG area, and the curve parametrized by that area. This is the model used
for the zero-cone case of the transfer.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMS4b

open MatedCRTHarmonic.MatedCRT

/-- The zero-quantum-cone realization of the frozen coupling. -/
def l46tZeroConeCellModel
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    GMSLemma27.CellModel γ where
  Ω := Ω
  measurableSpace := inferInstance
  P := P
  isProbabilityMeasure := D.isProbabilityMeasure
  field := fun ω => coneField (X₀ ω)
    (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω))
  area := fun ω => CellScaling.lqgArea γ
    (coneField (X₀ ω) (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω)))
  curve := fun ω => η₀ ω
  ae_continuous_curve := Filter.Eventually.of_forall fun ω => (η₀ ω).continuous
  ae_curve_zero := by
    filter_upwards [D.areaParam₀, D.spaceFilling] with ω harea hspace
    rcases harea with ⟨⟨φ, hφ0, hηeq⟩, _⟩
    rcases hspace with ⟨_, _, hηL0, _⟩
    rw [hηeq, hφ0, hηL0]
  ae_area_curve := by
    filter_upwards [D.areaParam₀,
      MesoModel.FrozenIdentities.ae_exists_isVagueLimitC_cone₀ D hγ] with ω harea hex
    have hex' : ∃ μ : Measure ℂ, CellScaling.IsVagueLimitC (CellScaling.lqgAreaApprox γ
        (coneField (X₀ ω) (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω)))) μ := hex
    intro a b hab
    rw [CellScaling.lqgArea, dite_eq_left hex']
    exact harea.2 _ hex'.choose_spec a b hab

end MatedCRTHarmonic.GMS4b
