import LatticeProb.LQG.ConeRadiusCurveIndependence
import LatticeProb.Topology.IndependentRadiusExitBall

/-! # Exit-ball estimates at a cone scale -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Metric MatedCRTHarmonic
open scoped ENNReal NNReal

namespace LatticeProb

/-- A uniform fixed-radius exit estimate transfers to a positive multiple of the
cone scale for any measurable transform of the Lebesgue-time curve. -/
theorem measure_forward_coneScale_exitFailure_le
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (b : ℝ) {a : ℝ} (ha : 0 < a)
    {d : ℕ} (F : C(ℝ, ℂ) → C(ℝ, EuclideanSpace ℝ (Fin d))) (hF : Measurable F)
    {ε : ℝ} (hε : 0 < ε) (p : ℝ≥0∞)
    (hbound : ∀ r : ℝ, 0 < r →
      P {ω | ¬ (openExitTime (fun s (_ : Unit) => (F ∘ ηL) ω (0 + (s : ℝ)))
        (ball 0 r) () ≠ ⊤ ∧ ∃ z, ball z (ε * r) ⊆
        (F ∘ ηL) ω '' Icc 0 (sInf {t : ℝ | 0 ≤ t ∧ (F ∘ ηL) ω t ∉ ball 0 r}))} ≤ p) :
    P {ω | ¬ (openExitTime (fun s (_ : Unit) => (F ∘ ηL) ω (0 + (s : ℝ)))
      (ball 0 (a * CellScaling.coneScale γ γ (fun s => B s ω) (fun s => B' s ω) b)) () ≠ ⊤ ∧
      0 ≤ ε * (a * CellScaling.coneScale γ γ (fun s => B s ω) (fun s => B' s ω) b) / 2 ∧ ∃ z,
      closedBall z (ε * (a * CellScaling.coneScale γ γ (fun s => B s ω) (fun s => B' s ω) b) / 2) ⊆
      (F ∘ ηL) ω '' Icc 0 (sInf {t : ℝ | 0 ≤ t ∧ (F ∘ ηL) ω t ∉
        ball 0 (a * CellScaling.coneScale γ γ (fun s => B s ω) (fun s => B' s ω) b)}))} ≤ p := by
  let : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨R, hRm, hRp, hRi, hReq⟩ := exists_coneScale_indepFun_curve D hγ0 hγ2 b F hF
  have hRi' : IndepFun (fun ω => a * R ω) (F ∘ ηL) P :=
    hRi.comp (measurable_const.mul measurable_id) measurable_id
  have hbound' := measure_forward_variableBallExitFailure_le
    (measurable_const.mul hRm) (hF.comp D.measurable_curves.1) hRi'
    (ae_of_all P (fun ω => mul_pos ha (hRp ω))) hε p hbound
  have heq : {ω | ¬ (openExitTime (fun s (_ : Unit) => (F ∘ ηL) ω (0 + (s : ℝ)))
      (ball 0 (a * R ω)) () ≠ ⊤ ∧ 0 ≤ ε * (a * R ω) / 2 ∧ ∃ z,
      closedBall z (ε * (a * R ω) / 2) ⊆
      (F ∘ ηL) ω '' Icc 0 (sInf {t : ℝ | 0 ≤ t ∧ (F ∘ ηL) ω t ∉ ball 0 (a * R ω)}))}
      =ᵐ[P] {ω | ¬ (openExitTime (fun s (_ : Unit) => (F ∘ ηL) ω (0 + (s : ℝ)))
      (ball 0 (a * CellScaling.coneScale γ γ (fun s => B s ω) (fun s => B' s ω) b)) () ≠ ⊤ ∧
      0 ≤ ε * (a * CellScaling.coneScale γ γ (fun s => B s ω) (fun s => B' s ω) b) / 2 ∧ ∃ z,
      closedBall z (ε * (a * CellScaling.coneScale γ γ (fun s => B s ω) (fun s => B' s ω) b) / 2) ⊆
      (F ∘ ηL) ω '' Icc 0 (sInf {t : ℝ | 0 ≤ t ∧ (F ∘ ηL) ω t ∉
        ball 0 (a * CellScaling.coneScale γ γ (fun s => B s ω) (fun s => B' s ω) b)}))} := by
    filter_upwards [hReq] with ω hω
    simp only [hω]
  rw [← measure_congr heq]
  exact hbound'

end LatticeProb
