/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTPort.Foundations.ConeArea8 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea7
import LatticeProb.Bonanno.LQGMetric.Field.GFFInvariance
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeMeasND

/-!
# Cone area, part 21: the cone LQG measure is a.s. small near the origin

**`ae_exists_ball_lt_one`**: for `0 < γ < 2`, `W > 0` and the reference cone data, a.s. some
ball `B(0,r)` has `qAreaC`-mass `< 1` (the small-ball half of `ConeArea7.ConeMassBounds`).

Proof: a.s. the cone approximations have a vague limit `μ` on `ℂ \ {0}` (ConeArea4H (b1)), are
eventually finite on compacts (ConeArea4I (b2)) and tight at `0` (ConeArea6E `b3'`); then `μ` is
the vague limit on `ℂ` (QZ `AtomlessUncond.isVagueLimitOn_of_local_of_tight` via
`ConeArea2.isVagueLimitOn_univ_of_punctured`), so `qAreaC = μ`, and QZ
`AtomlessUncond.measure_closedBall_le_of_tight` turns the tightness bound `≤ 1/2` into
`μ(B̄(0,δ/2)) ≤ 1/2`. Wiring only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.MoTPort
namespace ConeArea8

open QuantumZipper LQGMetric

/-- a.s. the cone area measure is *the* vague limit of the punctured-plane approximations: the
punctured limit `μ` is the vague limit on `ℂ` and equals `qAreaC` -/
theorem ae_qAreaC_coneField_eq {γ W : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hW : 0 < W)
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X : Ω' → Field} {A : ℝ → Ω' → ℝ} (hX : IsWholePlaneGFF X P')
    (hA : IsConeProcess (coneAlpha γ W) (Qc γ) A P') (hI : IndepFun X (fun ω t => A t ω) P') :
    ∀ᵐ ω ∂P', ∃ μ : Measure ℂ,
      qAreaC γ (coneField (lateralPartC (X ω)) (fun t => A t ω) (Qc γ)) = μ ∧
      IsVagueLimitOn (univ \ {0})
        (areaApproxC γ (coneField (lateralPartC (X ω)) (fun t => A t ω) (Qc γ))) μ ∧
      (∀ K, IsCompact K → ∀ᶠ k in atTop, areaApproxC γ
          (coneField (lateralPartC (X ω)) (fun t => A t ω) (Qc γ)) k K < ⊤) ∧
      ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ᶠ k in atTop, areaApproxC γ
          (coneField (lateralPartC (X ω)) (fun t => A t ω) (Qc γ)) k
            (Metric.ball 0 δ) ≤ ENNReal.ofReal ε := by
  filter_upwards [ConeArea4.ae_isVagueLimitOn_coneField_punctured hX hA hγ hγ2,
    ConeArea4.ae_fin_away_coneField hX hA hγ hγ2, ConeArea6.b3' hγ hγ2 hW Ω' _ P' X A
      inferInstance hX hA hI] with ω ⟨μ, hμ⟩ haway htight
  have hfin := fun K (hK : IsCompact K) => ConeArea4.fin_of_away_of_tight haway htight hK
  exact ⟨μ, ConeArea.qAreaC_eq_of_isVagueLimitOn
    (ConeArea2.isVagueLimitOn_univ_of_punctured hμ hfin htight), hμ, hfin, htight⟩

end ConeArea8
end MatedCRTHarmonic.MoTPort
