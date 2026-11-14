/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatAnnulusTranslatedSmallLower at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatAnnulusCenterSmallLower
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatTranslateVersion
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatAnnulusShiftCost
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.RealRandomTail

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_heat_annulus_translated_small_lower_of_perc
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (ξ : Ioi (0 : ℝ))
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ ε, IsHeatSmoothing P h ε (X ε))
    (z : ℂ) (d : ℝ) (hd : 0 < d) (hd2 : d ≤ 1 / 2)
    (η : ℝ) (hη : 0 < η) :
    ∃ T ε₀ : ℝ, 0 < T ∧ 0 < ε₀ ∧
      ∀ ε : Ioo (0 : ℝ) 1, (ε : ℝ) < ε₀ →
        P {ω | ENNReal.ofReal (m ⟨ε, ε.property.1⟩ : ℝ)⁻¹ *
          crossLenIn ξ (X ⟨ε, ε.property.1⟩ ω)
            (closedBall z d) (sphere z (d / 16))
            (sphere z (3 * d / 4)) < ENNReal.ofReal T⁻¹} ≤
          ENNReal.ofReal η := by
  let c₀ : ℂ := Complex.mk (1 / 2) (1 / 2)
  let a : ℂ := z - c₀
  let g : Ω → DistC := fun ω =>
    addConst (affineComp 1 a (h ω)) (-circleAvg (h ω) 1 a)
  have hg : IsNormalizedWholePlaneGFF g P :=
    (dg20_heat_translate_normalized P h hh a 1 one_pos).1
  obtain ⟨Y, hY, hYeq⟩ := dg20_exists_translated_heat_family P h hh X hX a
  let c : Ω → ℝ := fun ω => circleAvg (h ω) 1 a
  have hcm : Measurable c :=
    (measurable_circleAvg_left 1 a).comp hh.1.measurable
  have hη2 : 0 < η / 2 := half_pos hη
  obtain ⟨M, hM, hctail⟩ := dg20_real_random_tail P c hcm (η / 2) hη2
  obtain ⟨N, ε₀, hN, hε₀, hYtail⟩ :=
    dg20_heat_center_annulus_small_lower_of_perc hPerc ξ m hm
      P g hg Y hY d hd hd2 (η / 2) hη2
  let C : ℝ := Real.exp (|(ξ : ℝ)| * M)
  have hC : 0 < C := Real.exp_pos _
  let T : ℝ := 4 * (C + 1) * (N + 1)
  have hT : 0 < T := by dsimp [T]; positivity
  have hTN : 2 * C * N ≤ T := by
    dsimp [T]
    nlinarith [mul_nonneg hC.le hN.le]
  have hInv : C * T⁻¹ ≤ (2 * N)⁻¹ := by
    have h2N : 0 < 2 * N := by positivity
    have hh := (div_le_div_iff₀ hT h2N).2
      (by nlinarith [hTN] : C * (2 * N) ≤ 1 * T)
    simpa only [div_eq_mul_inv, one_div, one_mul] using hh
  have hsmall : (2 * N)⁻¹ < N⁻¹ := by
    have hh := one_div_lt_one_div_of_lt hN (by nlinarith : N < 2 * N)
    simpa only [one_div] using hh
  have hsmallE : ENNReal.ofReal ((2 * N)⁻¹) <
      ENNReal.ofReal N⁻¹ :=
    (ENNReal.ofReal_lt_ofReal_iff (inv_pos.mpr hN)).2 hsmall
  have hCL : ENNReal.ofReal C * ENNReal.ofReal T⁻¹ ≤
      ENNReal.ofReal ((2 * N)⁻¹) := by
    rw [← ENNReal.ofReal_mul hC.le]
    exact ENNReal.ofReal_le_ofReal hInv
  have hsum : ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) =
      ENNReal.ofReal η := by
    rw [← ENNReal.ofReal_add hη2.le hη2.le]
    congr 1
    ring
  have hca : c₀ + a = z := by dsimp [a]; abel
  have hshapeU : ((· + a) '' closedBall c₀ d) = closedBall z d := by
    simpa only [hca] using dg20_image_add_closedBall c₀ a d
  have hshapeA : ((· + a) '' sphere c₀ (d / 16)) = sphere z (d / 16) := by
    simpa only [hca] using dg20_image_add_sphere c₀ a (d / 16)
  have hshapeB : ((· + a) '' sphere c₀ (3 * d / 4)) =
      sphere z (3 * d / 4) := by
    simpa only [hca] using dg20_image_add_sphere c₀ a (3 * d / 4)
  refine ⟨T, ε₀, hT, hε₀, ?_⟩
  intro ε hε
  let e : Ioi (0 : ℝ) := ⟨ε, ε.property.1⟩
  let b : ℝ≥0∞ := ENNReal.ofReal (m e : ℝ)⁻¹
  let A : Ω → ℝ≥0∞ := fun ω => b *
    crossLenIn ξ (X e ω) (closedBall z d) (sphere z (d / 16))
      (sphere z (3 * d / 4))
  let B : Ω → ℝ≥0∞ := fun ω => b *
    crossLenIn ξ (Y e ω) (closedBall c₀ d) (sphere c₀ (d / 16))
      (sphere c₀ (3 * d / 4))
  let E : Ω → Prop := fun ω => ∀ x, Y e ω x = X e ω (x + a) - c ω
  have hnull : P {ω | ¬ E ω} = 0 := ae_iff.mp (hYeq e)
  have hbad : P {ω | ¬ (B ω ≤ ENNReal.ofReal C * A ω)} ≤
      ENNReal.ofReal (η / 2) := by
    have hsub : {ω | ¬ (B ω ≤ ENNReal.ofReal C * A ω)} ⊆
        {ω | M < |c ω|} ∪ {ω | ¬ E ω} := by
      intro ω hω
      by_cases he : E ω
      · by_cases hc : |c ω| ≤ M
        · have hcc : ENNReal.ofReal (Real.exp |(ξ : ℝ) * c ω|) ≤
              ENNReal.ofReal C := by
            apply ENNReal.ofReal_le_ofReal
            change Real.exp |(ξ : ℝ) * c ω| ≤ Real.exp (|(ξ : ℝ)| * M)
            rw [abs_mul]
            exact Real.exp_le_exp.2
              (mul_le_mul_of_nonneg_left hc (abs_nonneg (ξ : ℝ)))
          have hraw := (dg20_translated_crossing_cost_compare ξ
            (X e ω) (Y e ω) (closedBall c₀ d) (sphere c₀ (d / 16))
            (sphere c₀ (3 * d / 4)) a (c ω) he).2
          rw [hshapeU, hshapeA, hshapeB] at hraw
          have hBA : B ω ≤ ENNReal.ofReal C * A ω := by
            calc
              B ω ≤ b * (ENNReal.ofReal (Real.exp |(ξ : ℝ) * c ω|) *
                  crossLenIn ξ (X e ω) (closedBall z d)
                    (sphere z (d / 16)) (sphere z (3 * d / 4))) :=
                mul_le_mul_of_nonneg_left hraw bot_le
              _ ≤ b * (ENNReal.ofReal C *
                  crossLenIn ξ (X e ω) (closedBall z d)
                    (sphere z (d / 16)) (sphere z (3 * d / 4))) := by
                gcongr
              _ = ENNReal.ofReal C * A ω := by
                dsimp only [A, B]
                ac_rfl
          exact False.elim (hω hBA)
        · exact Or.inl (lt_of_not_ge hc)
      · exact Or.inr he
    calc
      _ ≤ P ({ω | M < |c ω|} ∪ {ω | ¬ E ω}) := measure_mono hsub
      _ ≤ P {ω | M < |c ω|} + P {ω | ¬ E ω} := measure_union_le _ _
      _ ≤ ENNReal.ofReal (η / 2) := by
        rw [hnull, add_zero]
        exact hctail
  have hloY : P {ω | B ω ≤ ENNReal.ofReal ((2 * N)⁻¹)} ≤
      ENNReal.ofReal (η / 2) := by
    calc
      _ ≤ P {ω | B ω < ENNReal.ofReal N⁻¹} :=
        measure_mono (by intro ω hω; exact lt_of_le_of_lt hω hsmallE)
      _ ≤ ENNReal.ofReal (η / 2) := by
        simpa only [B, b, e, c₀] using hYtail ε hε
  have hsub : {ω | A ω < ENNReal.ofReal T⁻¹} ⊆
      {ω | ¬ (B ω ≤ ENNReal.ofReal C * A ω)} ∪
        {ω | B ω ≤ ENNReal.ofReal ((2 * N)⁻¹)} := by
    intro ω hw
    by_cases hg : B ω ≤ ENNReal.ofReal C * A ω
    · exact Or.inr (hg.trans ((mul_le_mul_of_nonneg_left hw.le bot_le).trans hCL))
    · exact Or.inl hg
  calc
    _ ≤ P ({ω | ¬ (B ω ≤ ENNReal.ofReal C * A ω)} ∪
        {ω | B ω ≤ ENNReal.ofReal ((2 * N)⁻¹)}) := measure_mono hsub
    _ ≤ P {ω | ¬ (B ω ≤ ENNReal.ofReal C * A ω)} +
        P {ω | B ω ≤ ENNReal.ofReal ((2 * N)⁻¹)} := measure_union_le _ _
    _ ≤ ENNReal.ofReal η := by
      simpa only [A, b, e, hsum] using add_le_add hbad hloY

end SupercriticalLQGUniqueness.B2.DG20Pt
