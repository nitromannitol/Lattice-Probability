import LatticeProb.LQG.ConeCouplingLocalizedArea

/-! # Scale counts for a cone coupling -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Metric MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped ENNReal NNReal

namespace LatticeProb

/-- The number of padded logarithmic scales in a cone coupling has a
centered Brownian hitting-time upper tail. -/
theorem measure_cone_coupling_scale_count_gt_le_exp
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {b₁ b₂ u : ℝ} (hb₁ : 0 < b₁) (hb : b₁ < b₂) (hu : 0 < u)
    {T : ℝ≥0} (hTpos : 0 < T)
    (hT : (T : ℝ) = (γ⁻¹ * Real.log b₂ - γ⁻¹ * Real.log b₁) /
      (CellScaling.lqgQ γ - γ) + u)
    (N : ℕ) (hN : (T : ℝ) + 3 ≤ (N : ℝ)) :
    P {ω | N < (conePaddedScales γ γ B B' b₁ b₂ ω).card} ≤
      ENNReal.ofReal (Real.exp (-(((CellScaling.lqgQ γ - γ) * u) ^ 2 / (2 * T)))) := by
  let : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨C, hCm, hCc, hC⟩ := QuantumZipper.WedgeRes.exists_good_version D.bm_B
  obtain ⟨C', hC'm, hC'c, hC'⟩ := QuantumZipper.WedgeRes.exists_good_version D.bm_B'
  have hCB : IsBrownianReal C P :=
    ⟨D.bm_B.toIsPreBrownianReal.congr (fun t => hC.mono fun ω h => (h t).symm),
      ae_of_all _ hCc⟩
  have hC'B : IsBrownianReal C' P :=
    ⟨D.bm_B'.toIsPreBrownianReal.congr (fun t => hC'.mono fun ω h => (h t).symm),
      ae_of_all _ hC'c⟩
  have hind : IndepFun (QuantumZipper.pathOf C) (QuantumZipper.pathOf C') P := by
    apply D.indep_cone.2.congr
    · filter_upwards [hC] with ω hω
      funext t
      exact (hω t).symm
    · filter_upwards [hC'] with ω hω
      funext t
      exact (hω t).symm
  obtain ⟨W, hWm, _, _, hW⟩ :=
    CellScaling.JointScalingO.exists_radialPath_indepFun_curve D hγ0 hγ2
  have hW' : ∀ᵐ ω ∂P, ∀ t, W ω t = CellScaling.coneRadial γ γ
      (fun s => C s ω) (fun s => C' s ω) t := by
    filter_upwards [hW, hC, hC'] with ω hw hc hc' t
    simpa only [hc, hc'] using hw t
  have htail := ConeScaling.measure_cone_scale_count_gt_le_exp
    hγ0 (sub_pos.mp (CellScaling.lqgQ_sub_pos hγ0 hγ2)) hCB hC'B
    (fun t => hCm.of_uncurry_left) hCc hind hWm hW' hb₁ hb hu hTpos hT N hN
  calc
    _ ≤ P {ω | N < (conePaddedScales γ γ C C' b₁ b₂ ω).card} := by
      apply measure_mono_ae
      filter_upwards [hC, hC'] with ω hc hc' hω
      simpa only [conePaddedScales, hc, hc'] using hω
    _ ≤ _ := by simpa only [conePaddedScales] using htail

/-- A localized diameter failure on controlled windows is bounded by the
cone scale-count tail and the two directional exit-failure bounds. -/
theorem measure_cone_localized_diameter_exceeds_le_exp
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (F : C(ℝ, ℂ) → C(ℝ, EuclideanSpace ℝ (Fin 2))) (hFm : Measurable F)
    (hF : ∀ (v : C(ℝ, ℂ)) t, F v t = Complex.orthonormalBasisOneI.repr (v t))
    (b₁ b₂ δ w : ℝ) (hb₁ : 0 < b₁) (hb : b₁ < b₂) (hδ : 0 < δ)
    {u : ℝ} (hu : 0 < u) {T : ℝ≥0} (hTpos : 0 < T)
    (hT : (T : ℝ) = (γ⁻¹ * Real.log b₂ - γ⁻¹ * Real.log b₁) /
      (CellScaling.lqgQ γ - γ) + u)
    (p q : ℝ≥0∞) (N : ℕ) (hN : (T : ℝ) + 3 ≤ (N : ℝ))
    (hp : ∀ k, P (forwardExitBallFailure (F ∘ ηL) δ k) ≤ p)
    (hq : ∀ k, P (backwardExitBallFailure (F ∘ ηL) δ k) ≤ q) :
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
        (N : ℝ≥0∞) * (p + q) := by
  exact (measure_cone_localized_diameter_exceeds_le D hγ0 hγ2 F hFm hF
    b₁ b₂ δ w hδ p q N hp hq).trans
    (add_le_add (measure_cone_coupling_scale_count_gt_le_exp D hγ0 hγ2 hb₁ hb hu hTpos hT N hN) le_rfl)

end LatticeProb
