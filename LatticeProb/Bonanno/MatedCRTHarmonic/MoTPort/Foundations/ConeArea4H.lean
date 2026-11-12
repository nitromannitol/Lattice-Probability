/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTPort.Foundations.ConeArea4H at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea4G
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea2

/-!
# Cone area, part 8: (b1) unconditional; `ConeRefMeas` from (b2), (b3) only

* **`ae_isVagueLimitOn_coneField_punctured`**: for a whole-plane GFF `X`, a cone process `A` and
  `0 < γ < 2`, a.s. the approximations of the cone field `coneField (lateralPartC X) A Q` converge
  vaguely on `ℂ \ {0}` (input (b1) of `ConeArea2.coneRefMeas_of_punctured`). It is
  `ConeArea3.ae_isVagueLimitOn_coneField_punctured_of` fed with (R1)
  `ae_isVagueLimitOn_punctured` (ConeArea4D), (R2) `ae_radial_R2` (ConeArea4F) and (R3)
  `ae_locallyIntegrable_coneProfile` (ConeArea4G).
* **`coneRefMeas_of_fin_tight`**: `ConeRefMeas γ W` for `0 < γ < 2` from the two remaining inputs
  (b2) eventual finiteness on compacts and (b3) tightness at `0` of the cone-field
  approximations (`ConeArea2.coneRefMeas_of_punctured` with (b1) discharged).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace MatedCRTHarmonic.MoTPort
namespace ConeArea4

open QuantumZipper LQGMetric

/-- **(b1)**: a.s. vague limit of the cone-field approximations on `ℂ \ {0}` -/
theorem ae_isVagueLimitOn_coneField_punctured {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → Field} {A : ℝ → Ω → ℝ} {γ α Q : ℝ}
    (hX : IsWholePlaneGFF X P) (hA : IsConeProcess α Q A P) (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, ∃ μ, IsVagueLimitOn (univ \ {0})
      (areaApproxC γ (coneField (lateralPartC (X ω)) (fun t => A t ω) Q)) μ :=
  ConeArea3.ae_isVagueLimitOn_coneField_punctured_of hX hA
    (ae_isVagueLimitOn_punctured hX hγ hγ2) (ae_radial_R2 hX)
    (ae_locallyIntegrable_coneProfile hA)

end ConeArea4
end MatedCRTHarmonic.MoTPort
