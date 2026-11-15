import LatticeProb.LQG.ConeCouplingJointExitSelection
import LatticeProb.LQG.ConeCouplingScaleTail
import LatticeProb.Topology.LocalizedDiameterAreaBound

/-! # Joint exit-failure bounds for localized diameters -/

set_option autoImplicit false

open MeasureTheory Set Metric MatedCRTHarmonic
open scoped ENNReal NNReal

namespace LatticeProb

/-- A localized diameter bound holds except for the controlled event of a bad
selected scale, on windows satisfying the stated inner and outer bounds. -/
theorem measure_cone_localized_diameter_exceeds_le_joint
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (F : C(ℝ, ℂ) → C(ℝ, EuclideanSpace ℝ (Fin 2))) (hFm : Measurable F)
    (hF : ∀ (v : C(ℝ, ℂ)) t, F v t = Complex.orthonormalBasisOneI.repr (v t))
    (b₁ b₂ δ w : ℝ) (hδ : 0 < δ) (p : ℝ≥0∞) (N : ℕ)
    (hp : ∀ k, P (firstExitBallFailure (F ∘ ηL) δ k) ≤ p) :
    P {ω |
      let L := CellScaling.coneScale γ γ (fun s => B s ω) (fun s => B' s ω) b₁
      let R := CellScaling.coneScale γ γ (fun s => B s ω) (fun s => B' s ω) b₂
      0 < L ∧
      ¬ η ω '' Icc (0 - w / 2) 0 ⊆ ball 0 L ∧
      ¬ η ω '' Icc 0 (0 + w / 2) ⊆ ball 0 L ∧
      η ω '' Icc (0 - w) (0 + w) ⊆ closedBall 0 R ∧
      ENNReal.ofReal ((2 * Real.exp 1) ^ 2 * (4 / (Real.pi * δ ^ 2))) <
        MatedCRTHarmonic.GMS4b.locDA w (η ω) 0} ≤
      P {ω | N < (conePaddedScales γ γ B B' b₁ b₂ ω).card} +
        (N : ℝ≥0∞) * p := by
  calc
    _ ≤ P {ω | ∃ k ∈ conePaddedScales γ γ B B' b₁ b₂ ω,
        F (ηL ω) ∈ firstExitBallFailure id δ k} := by
      apply measure_mono_ae
      filter_upwards [ae_coupling_first_exit_trace_area_of_cone_scales D F hF hδ b₁ b₂] with ω htrace hwindow
      classical
      by_contra hbad
      have hgood : ∀ k ∈ conePaddedScales γ γ B B' b₁ b₂ ω,
          F (ηL ω) ∉ firstExitBallFailure id δ k := by
        intro k hk hfail
        exact hbad ⟨k, hk, hfail⟩
      have hC : 0 < 4 / (Real.pi * δ ^ 2) := by positivity
      have hle := MatedCRTHarmonic.GMS4b.locDA_le_of_first_exit_bounds
        (η ω) (η ω).continuous 0 hwindow.1 hC hwindow.2.1 hwindow.2.2.1
        hwindow.2.2.2.1 (htrace hgood)
      exact (not_lt_of_ge hle) hwindow.2.2.2.2
    _ ≤ _ := measure_exists_mem_conePaddedScales_joint_firstExitBallFailure_le
      D hγ0 hγ2 F hFm b₁ b₂ δ p N hp

/-- Polynomial exit bounds and the cone scale-count tail control localized
    diameter failures on the stated windows. -/
theorem measure_cone_localized_diameter_exceeds_le_joint_polynomial
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (F : C(ℝ, ℂ) → C(ℝ, EuclideanSpace ℝ (Fin 2))) (hFm : Measurable F)
    (hF : ∀ (v : C(ℝ, ℂ)) t, F v t = Complex.orthonormalBasisOneI.repr (v t))
    {q ρ r : ℝ} (hq : 0 < q) (hqρ : q < ρ) (hρ : ρ < 1)
    (hr : r ∈ Ioo (0 : ℝ) 1) (n : ℕ) :
    ∃ C : ℝ, ∀ {δ : ℝ}, δ ∈ Ioo (0 : ℝ) 1 → δ ^ (1 - r) ≤ q →
    ∀ (b₁ b₂ w : ℝ), 0 < b₁ → b₁ < b₂ →
    ∀ {u : ℝ}, 0 < u → ∀ {T : ℝ≥0}, 0 < T →
    (T : ℝ) = (γ⁻¹ * Real.log b₂ - γ⁻¹ * Real.log b₁) /
      (CellScaling.lqgQ γ - γ) + u →
    ∀ (N : ℕ), (T : ℝ) + 3 ≤ (N : ℝ) →
    P {ω |
      let L := CellScaling.coneScale γ γ (fun s => B s ω) (fun s => B' s ω) b₁
      let R := CellScaling.coneScale γ γ (fun s => B s ω) (fun s => B' s ω) b₂
      0 < L ∧
      ¬ η ω '' Icc (0 - w / 2) 0 ⊆ ball 0 L ∧
      ¬ η ω '' Icc 0 (0 + w / 2) ⊆ ball 0 L ∧
      η ω '' Icc (0 - w) (0 + w) ⊆ closedBall 0 R ∧
      ENNReal.ofReal ((2 * Real.exp 1) ^ 2 * (4 / (Real.pi * δ ^ 2))) <
        MatedCRTHarmonic.GMS4b.locDA w (η ω) 0} ≤
      ENNReal.ofReal (Real.exp (-(((CellScaling.lqgQ γ - γ) * u) ^ 2 / (2 * T)))) +
        (N : ℝ≥0∞) * ENNReal.ofReal (C * δ ^ n) := by
  obtain ⟨C, hC⟩ := LQG.measure_areaTime_planar_exit_failure_uniform_le D F hF hq hqρ hρ hr n
  refine ⟨C, ?_⟩
  intro δ hδ hδq b₁ b₂ w hb₁ hb u hu T hTpos hT N hN
  exact (measure_cone_localized_diameter_exceeds_le_joint D hγ0 hγ2 F hFm hF
    b₁ b₂ δ w hδ.1 _ N (hC hδ hδq)).trans
    (add_le_add (measure_cone_coupling_scale_count_gt_le_exp
      D hγ0 hγ2 hb₁ hb hu hTpos hT N hN) le_rfl)

end LatticeProb
