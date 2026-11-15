import LatticeProb.LQG.ConeRandomRadiusExit
import LatticeProb.Topology.FirstHitExitRadius
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.JointScalingOMain

/-! # First-hit exit-ball estimates at a cone scale -/

set_option autoImplicit false

open Filter MeasureTheory ProbabilityTheory Set Metric MatedCRTHarmonic
open scoped ENNReal NNReal Topology

namespace LatticeProb

/-- A uniform first-hit estimate transfers to a closed-ball exit estimate at a
positive multiple of the cone scale. -/
theorem measure_forward_coneScale_exitFailure_le_of_firstHit
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (b : ℝ) {a : ℝ} (ha : 0 < a)
    (F : C(ℝ, ℂ) → C(ℝ, EuclideanSpace ℝ (Fin 2))) (hF : Measurable F)
    (hFpoint : ∀ (v : C(ℝ, ℂ)) t, F v t = Complex.orthonormalBasisOneI.repr (v t))
    {ε : ℝ} (hε : 0 < ε) (p : ℝ≥0∞)
    (hbound : ∀ r : ℝ, 0 < r →
      P {ω | ¬ ∃ z, ball z (ε * r) ⊆ (ηL ω) ''
        Icc (GMS4b.hitTime (ηL ω) 0)
          (sInf {t : ℝ | GMS4b.hitTime (ηL ω) 0 ≤ t ∧ ηL ω t ∉ ball 0 r})} ≤ p) :
    P {ω | ¬ (openExitTime (fun s (_ : Unit) => (F ∘ ηL) ω (0 + (s : ℝ)))
      (ball 0 (a * CellScaling.coneScale γ γ (fun s => B s ω) (fun s => B' s ω) b)) () ≠ ⊤ ∧
      0 ≤ ε * (a * CellScaling.coneScale γ γ (fun s => B s ω) (fun s => B' s ω) b) / 2 ∧ ∃ z,
      closedBall z (ε * (a * CellScaling.coneScale γ γ (fun s => B s ω) (fun s => B' s ω) b) / 2) ⊆
      (F ∘ ηL) ω '' Icc 0 (sInf {t : ℝ | 0 ≤ t ∧ (F ∘ ηL) ω t ∉
        ball 0 (a * CellScaling.coneScale γ γ (fun s => B s ω) (fun s => B' s ω) b)}))} ≤ p := by
  have hpath : ∀ᵐ ω ∂P, Continuous (ηL ω) ∧
      Tendsto (ηL ω) (cocompact ℝ) (cocompact ℂ) ∧ (0 : ℂ) ∈ range (ηL ω) ∧
      ∀ t, (F ∘ ηL) ω t = Complex.orthonormalBasisOneI.repr
        (ηL ω (GMS4b.hitTime (ηL ω) 0 + t) - 0) := by
    filter_upwards [D.spaceFilling, CellScaling.JointScalingO.ae_firstHit_zero_of_coupling D]
      with ω hspace hroot
    have hroot' : GMS4b.hitTime (ηL ω) 0 = 0 := hroot
    refine ⟨(ηL ω).continuous, hspace.2.1, Set.mem_range.mpr (hspace.1 0), fun t => ?_⟩
    rw [Function.comp_apply, hFpoint, hroot', zero_add, sub_zero]
  apply measure_forward_coneScale_exitFailure_le D hγ0 hγ2 b ha F hF hε p
  intro r hr
  rw [measure_firstHit_forwardExit_failure_eq P (F ∘ ηL) (fun ω => ⇑(ηL ω))
    0 r (ε * r) hpath]
  exact hbound r hr

end LatticeProb
