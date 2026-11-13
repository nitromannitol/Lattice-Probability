/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.ConeScaling.AreaScaling at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeScaling.FieldLaw
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeScaling.AreaFunctional
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCone.OpenSupport

/-!
# `AreaScalingLaw`: the area of the unit disk at the cone scale

Target: `CellScaling.AreaScalingLaw D` (`CellScaling/Model.lean`): for every `b > 0` and Borel `S`,

  `P(b⁻¹ μ_h(B_{R_b}(0)) ∈ S) = P(μ_h(B_1(0)) ∈ S)`.

Proof:
* `μ_{h_b}(B_1) = b⁻¹ μ_h(R_b B_1) = b⁻¹ μ_h(B_{R_b})` a.s. — the random-dilation coordinate change at
  the cone scale ([SW] Thm 1.1/1.4, `1605.06171v2.`), the named input
  `ConeAreaRandomDilation D` (proved by `LQGCoord.ae_lqgArea_coneRescaleField_holds`;
  discharged in `ConeScaling/AreaScalingHolds.lean`);
* `h_b =d h` (DMS Prop 4.13(i)): `ConeRealization.map_rescaledField_eq`;
* `h ↦ μ_h(B_1)` agrees with the measurable functional `areaOpenFun γ (ball 0 1)` on fields whose
  area approximations converge vaguely; this holds a.s. for `h` and for `h_b` because `μ_{h_b}(B_1) = b⁻¹ μ_h(B_{R_b}) > 0`
   whereas the junk value of `lqgArea` is `0`.
SLE-free; no bundle field is used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.ConeScaling

open LQGMetric MatedCRTHarmonic.CellScaling

/-- **Random-dilation covariance of the cone area at the cone scale** ([SW] Sheffield–Wang Thm 1.1/1.4, arXiv:1605.06171): for every `b > 0`, almost surely
`μ_{h_b}(B_1(0)) = b⁻¹ μ_h(B_{R_b}(0))`, where `h_b = h(R_b ·) + Q log R_b − γ⁻¹ log b`. It is the
instance `A = B_1(0)`, `R = R_b` of `LQGCoord.ae_lqgArea_coneRescaleField_holds` (and of
`CellScaling.LR1SetwiseAreaCovariance`). -/
def ConeAreaRandomDilation {γ : ℝ} {M : MesoModel.MatedCRTUnitMesoModel γ} (D : ConeRealization M) :
    Prop :=
  ∀ b : ℝ, 0 < b → ∀ᵐ ω ∂M.coupled.family.P,
    lqgArea γ (coneRescaleField γ (D.scale b ω) b (D.field ω)) (ball 0 1) =
      ENNReal.ofReal b⁻¹ * D.area ω (ball 0 (D.scale b ω))

lemma measure_setOf_mem_congr {Ω α : Type*} [MeasurableSpace Ω] {P : Measure Ω} {f g : Ω → α}
    (h : f =ᵐ[P] g) (S : Set α) : P {ω | f ω ∈ S} = P {ω | g ω ∈ S} := by
  apply measure_congr
  filter_upwards [h] with ω hω
  rw [hω]

lemma lt_Qc {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : γ < QuantumZipper.Qc γ := by
  have h := lqgQ_sub_pos hγ hγ2
  have hQ : lqgQ γ = QuantumZipper.Qc γ := by dsimp [lqgQ, QuantumZipper.Qc]
  linarith

/-- **`AreaScalingLaw` from the random-dilation covariance** (DMS Prop 4.13(i) + [SW]). -/
theorem areaScalingLaw_of_randomDilation {γ : ℝ} {M : MesoModel.MatedCRTUnitMesoModel γ}
    (D : ConeRealization M) (hcov : ConeAreaRandomDilation D) : AreaScalingLaw D := by
  intro b hb S hS
  have := D.gff.gaussian.isProbabilityMeasure
  obtain ⟨hγ, hγ2⟩ := M.hγ
  obtain ⟨hhm, hbm, hlaw⟩ := ConeRealization.map_rescaledField_eq D b
  have hXA := indepFun_motConeRadial hγ hγ2 D.brownian D.brownian' D.indep.1
  have hα := lt_Qc hγ hγ2
  have hvague := LQGCone.ae_isVagueLimitC_coneField hγ hγ2 hα D.gff D.brownian D.brownian'
    D.indep.2 hXA
  have hpos := LQGCone.ae_lqgArea_coneField_open_pos hγ hγ2 hα D.gff D.brownian D.brownian'
    D.indep.2 hXA
  have hG := measurable_areaOpenFun γ (ball (0 : ℂ) 1)
  have e1 : (fun ω => ENNReal.ofReal b⁻¹ * D.area ω (ball 0 (D.scale b ω))) =ᵐ[M.coupled.family.P]
      fun ω => areaOpenFun γ (ball 0 1) (coneRescaleField γ (D.scale b ω) b (D.field ω)) := by
    filter_upwards [hcov b hb, hpos] with ω hc hp
    have hR : 0 < D.scale b ω := Real.exp_pos _
    have hne : lqgArea γ (coneRescaleField γ (D.scale b ω) b (D.field ω)) (ball 0 1) ≠ 0 := by
      rw [hc]
      refine mul_ne_zero ?_ (hp _ isOpen_ball (nonempty_ball.2 hR)).ne'
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le, inv_pos]
      exact hb
    rw [areaOpenFun_eq_lqgArea isOpen_ball isBounded_ball
      (exists_isVagueLimitC_of_lqgArea_ne_zero hne), hc]
  have e2 : (fun ω => D.area ω (ball 0 1)) =ᵐ[M.coupled.family.P]
      fun ω => areaOpenFun γ (ball 0 1) (D.field ω) := by
    filter_upwards [hvague] with ω hv
    exact (areaOpenFun_eq_lqgArea isOpen_ball isBounded_ball hv).symm
  rw [measure_setOf_mem_congr e1, measure_setOf_mem_congr e2]
  have hGS : MeasurableSet (areaOpenFun γ (ball 0 1) ⁻¹' S) := hG hS
  change M.coupled.family.P
      ((fun ω => coneRescaleField γ (D.scale b ω) b (D.field ω)) ⁻¹'
        (areaOpenFun γ (ball 0 1) ⁻¹' S)) =
    M.coupled.family.P (D.field ⁻¹' (areaOpenFun γ (ball 0 1) ⁻¹' S))
  rw [← Measure.map_apply_of_aemeasurable hbm hGS, hlaw,
    Measure.map_apply_of_aemeasurable hhm hGS]

end MatedCRTHarmonic.ConeScaling
