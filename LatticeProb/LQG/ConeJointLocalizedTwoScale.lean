import LatticeProb.LQG.ConeCouplingJointLocalizedArea
import LatticeProb.LQG.ConeOuterWindowPolynomial
import LatticeProb.LQG.ConeInnerWindowPowerTail

/-! # Joint exit bounds on two cone scales -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Metric LQGMetric
open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped NNReal ENNReal

namespace LatticeProb.LQG

/-- A localized diameter tail is controlled by the exit failures on selected
scales and by separate inner and outer cone-window estimates. -/
theorem measure_cone_localized_diameter_le_joint_two_scale
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2)
    (μ : Ω → Measure ℂ)
    (hμ : ∀ᵐ ω ∂P, IsVagueLimitC (lqgAreaApprox γ
      (coneField (X ω) (coneRadial γ γ (fun s => B s ω) (fun s => B' s ω)))) (μ ω))
    (F : C(ℝ, ℂ) → C(ℝ, EuclideanSpace ℝ (Fin 2))) (hFm : Measurable F)
    (hF : ∀ (v : C(ℝ, ℂ)) t, F v t = Complex.orthonormalBasisOneI.repr (v t))
    {p q ρ r e s : ℝ} (hp : 0 < p) (hq : 0 < q) (hqρ : q < ρ)
    (hρ1 : ρ < 1) (hr : r ∈ Ioo (0 : ℝ) 1) (M : ℕ)
    (he : e < p ^ 2 / (2 * γ ^ 2) - 2)
    (hs : 0 < s) (hsγ : s < 4 / γ ^ 2 - 1) :
    ∃ Cjoint Cexit Carea : ℝ, ∃ Cinner : ℝ≥0∞, Cinner < ⊤ ∧
      ∀ {δ w b : ℝ}, δ ∈ Ioo (0 : ℝ) 1 → δ ^ (1 - r) ≤ q →
      0 < w → 2 * w ≤ δ ^ (2 + γ ^ 2 / 2 + p) → 0 < b → b < 1 →
      ∀ {u : ℝ}, 0 < u → ∀ {T : ℝ≥0}, 0 < T →
      (T : ℝ) = (γ⁻¹ * Real.log 1 - γ⁻¹ * Real.log b) /
        (CellScaling.lqgQ γ - γ) + u →
      ∀ (N : ℕ), (T : ℝ) + 3 ≤ (N : ℝ) →
      P {ω | ENNReal.ofReal ((2 * Real.exp 1) ^ 2 * (4 / (Real.pi * δ ^ 2))) <
        MatedCRTHarmonic.GMS4b.locDA w (η ω) 0} ≤
      (ENNReal.ofReal (Real.exp (-(((CellScaling.lqgQ γ - γ) * u) ^ 2 / (2 * T)))) +
        (N : ℝ≥0∞) * ENNReal.ofReal (Cjoint * δ ^ M)) +
      (ENNReal.ofReal (Cexit * δ ^ M) + ENNReal.ofReal (Carea * δ ^ e)) +
        Cinner * ENNReal.ofReal ((b⁻¹ * (w / 2)) ^ (-s)) := by
  obtain ⟨Cjoint, hjoint⟩ :=
    measure_cone_localized_diameter_exceeds_le_joint_polynomial D hγ.1 hγ.2 F hFm hF
      hq hqρ hρ1 hr M
  obtain ⟨Cexit, Carea, houter⟩ :=
    measure_cone_scaled_window_escape_le_polynomial_add D hstd hγ hp hq hqρ hρ1 hr M he
  obtain ⟨Cinner, hfinite, hinner⟩ :=
    cone_inner_window_containment_power_tail D hstd hγ μ hμ s hs hsγ
  refine ⟨Cjoint, Cexit, Carea, Cinner, hfinite, ?_⟩
  intro δ w b hδ hδq hw hwidth hb hb1 u hu T hTpos hT N hN
  have hlocal := hjoint hδ hδq b 1 w hb hb1 hu hTpos hT N hN
  have houter' := houter hδ hδq hw.le hwidth (show (0 : ℝ) < 1 by norm_num)
  have hinner' := hinner b w hb hw
  calc
    _ ≤ P {ω |
        let L := CellScaling.coneScale γ γ (fun t => B t ω) (fun t => B' t ω) b
        let R := CellScaling.coneScale γ γ (fun t => B t ω) (fun t => B' t ω) 1
        0 < L ∧ ¬ η ω '' Icc (0 - w / 2) 0 ⊆ ball 0 L ∧
        ¬ η ω '' Icc 0 (0 + w / 2) ⊆ ball 0 L ∧
        η ω '' Icc (0 - w) (0 + w) ⊆ closedBall 0 R ∧
        ENNReal.ofReal ((2 * Real.exp 1) ^ 2 * (4 / (Real.pi * δ ^ 2))) <
          MatedCRTHarmonic.GMS4b.locDA w (η ω) 0} +
      P {ω | ¬ η ω '' Icc (-(1 * w)) (1 * w) ⊆
        ball 0 (CellScaling.coneScale γ γ (fun t => B t ω) (fun t => B' t ω) 1)} +
      P {ω | let L := CellScaling.coneScale γ γ (fun t => B t ω) (fun t => B' t ω) b
        η ω '' Icc (0 - w / 2) 0 ⊆ ball 0 L ∨
          η ω '' Icc 0 (0 + w / 2) ⊆ ball 0 L} := by
      calc
        _ ≤ P ({ω |
            let L := CellScaling.coneScale γ γ (fun t => B t ω) (fun t => B' t ω) b
            let R := CellScaling.coneScale γ γ (fun t => B t ω) (fun t => B' t ω) 1
            0 < L ∧ ¬ η ω '' Icc (0 - w / 2) 0 ⊆ ball 0 L ∧
            ¬ η ω '' Icc 0 (0 + w / 2) ⊆ ball 0 L ∧
            η ω '' Icc (0 - w) (0 + w) ⊆ closedBall 0 R ∧
            ENNReal.ofReal ((2 * Real.exp 1) ^ 2 * (4 / (Real.pi * δ ^ 2))) <
              MatedCRTHarmonic.GMS4b.locDA w (η ω) 0} ∪
          {ω | ¬ η ω '' Icc (-(1 * w)) (1 * w) ⊆
            ball 0 (CellScaling.coneScale γ γ (fun t => B t ω) (fun t => B' t ω) 1)} ∪
          {ω | let L := CellScaling.coneScale γ γ (fun t => B t ω) (fun t => B' t ω) b
            η ω '' Icc (0 - w / 2) 0 ⊆ ball 0 L ∨
              η ω '' Icc 0 (0 + w / 2) ⊆ ball 0 L}) := by
          apply measure_mono
          intro ω hω
          by_cases hout : η ω '' Icc (-(1 * w)) (1 * w) ⊆
              ball 0 (CellScaling.coneScale γ γ (fun t => B t ω) (fun t => B' t ω) 1)
          · by_cases hl : η ω '' Icc (0 - w / 2) 0 ⊆
                ball 0 (CellScaling.coneScale γ γ (fun t => B t ω) (fun t => B' t ω) b)
            · exact Or.inr (Or.inl hl)
            · by_cases hr' : η ω '' Icc 0 (0 + w / 2) ⊆
                  ball 0 (CellScaling.coneScale γ γ (fun t => B t ω) (fun t => B' t ω) b)
              · exact Or.inr (Or.inr hr')
              · apply Or.inl (Or.inl ?_)
                refine ⟨Real.exp_pos _, hl, hr', ?_, hω⟩
                simpa only [one_mul, zero_sub, zero_add] using hout.trans ball_subset_closedBall
          · exact Or.inl (Or.inr hout)
        _ ≤ _ := (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ _ := add_le_add (add_le_add hlocal (by simpa only [one_mul] using houter')) hinner'

end LatticeProb.LQG
