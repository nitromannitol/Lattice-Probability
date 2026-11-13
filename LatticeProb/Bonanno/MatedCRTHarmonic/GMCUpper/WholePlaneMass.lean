/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMCUpper.WholePlaneMass at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCUpper.MassGrid

/-!
# Upper small-ball mass of normalized whole-plane GMC

The translated α = 0 moment is uniform on a compact disk. A square grid
turns it into the spatial supremum estimate used in [18], Lemma 4.7.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric LQGMetric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMCUpper

theorem aemeasurable_wholePlaneArea_ball
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → DistC}
    (hY : IsNormalizedWPGFF Y P) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (z : ℂ) (R : ℝ) :
    AEMeasurable (fun ω => wholePlaneArea γ Y ω (ball z R)) P := by
  letI : IsProbabilityMeasure P := hY.1.gaussian.isProbabilityMeasure
  have hv := MatedCRTHarmonic.LQGCoord.ae_exists_isVagueLimitC_wp
    hY.1 hγ.1 hγ.2
  have he : (fun ω => MatedCRTHarmonic.ConeScaling.areaOpenFun γ (ball z R) (Y ω))
      =ᵐ[P] fun ω => wholePlaneArea γ Y ω (ball z R) := by
    filter_upwards [hv] with ω hω
    exact MatedCRTHarmonic.ConeScaling.areaOpenFun_eq_lqgArea
      isOpen_ball isBounded_ball hω
  exact ((MatedCRTHarmonic.ConeScaling.measurable_areaOpenFun γ (ball z R)).comp
    hY.1.measurable).aemeasurable.congr he

private theorem wholePlane_grid_bad_bound
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → DistC}
    (hY : IsNormalizedWPGFF Y P) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 2)
    {q p ξ ρ δ : ℝ} (hq : 0 < q) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hρ : ρ < 1) (hR64 : 2 * δ ≤ 1 / 64)
    (hδρ : δ ≤ (1 - ρ) / 4)
    {C : ℝ≥0∞}
    (hI : ∀ (w : ℂ), ‖w‖ ≤ 1 → ∀ R : ℝ, 0 < R → R ≤ 1 / 64 →
      ∫⁻ ω, wholePlaneArea γ Y ω (ball w R) ^ q ∂P ≤
        C * ENNReal.ofReal
          (R ^ (q * (2 + γ ^ 2 / 2) - p * q * γ ^ 2 / 2))) :
    P {ω | ∃ z ∈ ball (0 : ℂ) ρ,
      ENNReal.ofReal (δ ^ ξ) < wholePlaneArea γ Y ω (ball z δ)} ≤
      (ENNReal.ofReal 36 *
        (C * ENNReal.ofReal ((2 : ℝ) ^
          (q * (2 + γ ^ 2 / 2) - p * q * γ ^ 2 / 2)))) *
        ENNReal.ofReal (δ ^
          (q * (2 + γ ^ 2 / 2) - p * q * γ ^ 2 / 2 - ξ * q - 2)) := by
  let e : ℝ := q * (2 + γ ^ 2 / 2) - p * q * γ ^ 2 / 2
  let K : ℝ≥0∞ := C * ENNReal.ofReal ((2 : ℝ) ^ e)
  have hcover : {ω | ∃ z ∈ ball (0 : ℂ) ρ,
      ENNReal.ofReal (δ ^ ξ) < wholePlaneArea γ Y ω (ball z δ)} ⊆
      ⋃ ij : Fin (⌈4 / δ⌉₊ + 1) × Fin (⌈4 / δ⌉₊ + 1),
        {ω | massGridEligible ρ δ (-1) (massGridPt δ ij) ∧
          ENNReal.ofReal (δ ^ ξ) <
            wholePlaneArea γ Y ω (ball (massGridPt δ ij) (2 * δ))} := by
    intro ω ⟨z, hz, hbad⟩
    apply far_bad_subset_grid (μ := wholePlaneArea γ Y) hρ.le hδ
    exact ⟨z, hz, by have := norm_nonneg z; linarith, hbad⟩
  have hpoint : ∀ ij : Fin (⌈4 / δ⌉₊ + 1) × Fin (⌈4 / δ⌉₊ + 1),
      P {ω | massGridEligible ρ δ (-1) (massGridPt δ ij) ∧
        ENNReal.ofReal (δ ^ ξ) <
          wholePlaneArea γ Y ω (ball (massGridPt δ ij) (2 * δ))} ≤
      K * ENNReal.ofReal (δ ^ (e - ξ * q)) := by
    intro ij
    by_cases hgood : massGridEligible ρ δ (-1) (massGridPt δ ij)
    · obtain ⟨z, hz, -, hzw⟩ := hgood
      have hw : ‖massGridPt δ ij‖ ≤ 1 := by
        have hzρ : ‖z‖ < ρ := mem_ball_zero_iff.1 hz
        have hnorm : ‖massGridPt δ ij‖ ≤ ‖z‖ + ‖z - massGridPt δ ij‖ := by
          calc
            ‖massGridPt δ ij‖ = ‖z - (z - massGridPt δ ij)‖ := by congr 1; abel
            _ ≤ ‖z‖ + ‖z - massGridPt δ ij‖ := norm_sub_le _ _
        linarith
      have hmoment : ∫⁻ ω, wholePlaneArea γ Y ω
          (ball (massGridPt δ ij) (2 * δ)) ^ q ∂P ≤
          K * ENNReal.ofReal (δ ^ e) := by
        calc
          _ ≤ C * ENNReal.ofReal ((2 * δ) ^ e) :=
            hI _ hw _ (by positivity) hR64
          _ = K * ENNReal.ofReal (δ ^ e) := by
            rw [Real.mul_rpow (by norm_num) hδ.le,
              ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
            simp only [K, mul_assoc]
      calc
        _ ≤ P {ω | ENNReal.ofReal (δ ^ ξ) <
            wholePlaneArea γ Y ω (ball (massGridPt δ ij) (2 * δ))} :=
          measure_mono (by intro ω hω; exact hω.2)
        _ ≤ K * ENNReal.ofReal (δ ^ (e - ξ * q)) :=
          measure_mass_gt_le_rpow
            (aemeasurable_wholePlaneArea_ball hY hγ _ _) hδ hq hmoment
    · have hempty : {ω | massGridEligible ρ δ (-1) (massGridPt δ ij) ∧
          ENNReal.ofReal (δ ^ ξ) <
            wholePlaneArea γ Y ω (ball (massGridPt δ ij) (2 * δ))} = ∅ := by
        ext ω
        simp [hgood]
      rw [hempty, measure_empty]
      exact zero_le
  calc
    P {ω | ∃ z ∈ ball (0 : ℂ) ρ,
      ENNReal.ofReal (δ ^ ξ) < wholePlaneArea γ Y ω (ball z δ)} ≤
      P (⋃ ij : Fin (⌈4 / δ⌉₊ + 1) × Fin (⌈4 / δ⌉₊ + 1),
        {ω | massGridEligible ρ δ (-1) (massGridPt δ ij) ∧
          ENNReal.ofReal (δ ^ ξ) <
            wholePlaneArea γ Y ω (ball (massGridPt δ ij) (2 * δ))}) := measure_mono hcover
    _ ≤ ∑ ij : Fin (⌈4 / δ⌉₊ + 1) × Fin (⌈4 / δ⌉₊ + 1),
        P {ω | massGridEligible ρ δ (-1) (massGridPt δ ij) ∧
          ENNReal.ofReal (δ ^ ξ) <
            wholePlaneArea γ Y ω (ball (massGridPt δ ij) (2 * δ))} :=
      measure_iUnion_fintype_le _ _
    _ ≤ ∑ _ij : Fin (⌈4 / δ⌉₊ + 1) × Fin (⌈4 / δ⌉₊ + 1),
        K * ENNReal.ofReal (δ ^ (e - ξ * q)) :=
      Finset.sum_le_sum fun ij _ => hpoint ij
    _ = ENNReal.ofReal ((((⌈4 / δ⌉₊ + 1 : ℕ) : ℝ)) ^ 2) *
        (K * ENNReal.ofReal (δ ^ (e - ξ * q))) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
        Fintype.card_fin, nsmul_eq_mul]
      congr 1
      norm_cast
      ring
    _ ≤ ENNReal.ofReal (36 * δ ^ (-2 : ℝ)) *
        (K * ENNReal.ofReal (δ ^ (e - ξ * q))) :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal (grid_card_bound hδ hδ1)) le_rfl
    _ = (ENNReal.ofReal 36 * K) *
        ENNReal.ofReal (δ ^ (e - ξ * q - 2)) := by
      simpa only [K, mul_assoc] using
        (far_rpow_factor (e := e - ξ * q) hδ K)
    _ = _ := by rfl

/-- Small-ball GMC upper mass for the normalized whole-plane GFF. -/
theorem upperMassBoundWholePlaneModel_holds
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → DistC}
    {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hY : IsNormalizedWPGFF Y P) :
    UpperMassBoundWholePlaneModel hγ hY := by
  let g : ℝ := γ ^ 2
  have hg : 0 < g := pow_pos hγ.1 _
  have hg4 : g < 4 := by
    dsimp [g]
    have hγ0 : 0 < γ := hγ.1
    have hγ2 : γ < 2 := hγ.2
    nlinarith [mul_pos (show 0 < 2 - γ by linarith)
      (show 0 < 2 + γ by linarith)]
  obtain ⟨q, p, hq, hqp, hp4, he⟩ := exists_outer_exponents g hg hg4
  let e : ℝ := q * (2 + g / 2) - p * q * g / 2
  let ξ : ℝ := (e - 2) / (2 * q)
  let β : ℝ := (e - 2) / 2
  have hξ : 0 < ξ := div_pos (by dsimp [e]; linarith) (by positivity)
  have hβ : 0 < β := by dsimp [β, e]; linarith
  have hexp : e - ξ * q - 2 = β := by
    dsimp [ξ, β]
    field_simp
    ring
  obtain ⟨C₀, hC₀top, hI₀⟩ :=
    exists_uniform_translated_ball_moment hY hγ.1 hγ.2 hq hqp
      (by simpa only [g] using hp4)
  let K : ℝ≥0∞ := ENNReal.ofReal 36 *
    (C₀ * ENNReal.ofReal ((2 : ℝ) ^ e))
  have hKtop : K < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top hC₀top ENNReal.ofReal_lt_top)
  let k : ℝ := K.toReal
  have hK : ENNReal.ofReal k = K := ENNReal.ofReal_toReal hKtop.ne
  refine ⟨ξ, β, hξ, hβ, ?_⟩
  intro ρ hρ
  let δ₀ : ℝ := min (1 / 128) ((1 - ρ) / 4)
  have hδ₀ : 0 < δ₀ := lt_min (by norm_num) (by linarith [hρ.2])
  have hδ₀1 : δ₀ ≤ 1 := by
    have := min_le_left (1 / 128 : ℝ) ((1 - ρ) / 4)
    linarith
  let C : ℝ := max k (δ₀ ^ (-β))
  refine ⟨C, fun δ hδ => ?_⟩
  by_cases hsmall : δ ≤ δ₀
  · have hR64 : 2 * δ ≤ 1 / 64 := by
      have := le_trans hsmall (min_le_left (1 / 128 : ℝ) ((1 - ρ) / 4))
      linarith
    have hδρ : δ ≤ (1 - ρ) / 4 :=
      le_trans hsmall (min_le_right _ _)
    have hbound := wholePlane_grid_bad_bound (ξ := ξ) hY hγ hq hδ.1 hδ.2.le
      hρ.2 hR64 hδρ hI₀
    have hpow : 0 ≤ δ ^ β := Real.rpow_nonneg hδ.1.le _
    calc
      P {ω | ∃ z ∈ ball (0 : ℂ) ρ,
        ENNReal.ofReal (δ ^ ξ) < wholePlaneArea γ Y ω (ball z δ)} ≤
          K * ENNReal.ofReal (δ ^ β) := by
        simpa only [K, e, g, hexp] using hbound
      _ = ENNReal.ofReal (k * δ ^ β) := by
        rw [← hK, ENNReal.ofReal_mul ENNReal.toReal_nonneg]
      _ ≤ ENNReal.ofReal (C * δ ^ β) :=
        ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right (le_max_left _ _) hpow)
  · letI : IsProbabilityMeasure P := hY.1.gaussian.isProbabilityMeasure
    have hδ₀δ : δ₀ ≤ δ := le_of_not_ge hsmall
    have hδpow : δ₀ ^ β ≤ δ ^ β :=
      Real.rpow_le_rpow hδ₀.le hδ₀δ hβ.le
    have hδ₀pow : 0 ≤ δ₀ ^ (-β) := Real.rpow_nonneg hδ₀.le _
    have hδpow0 : 0 ≤ δ ^ β := Real.rpow_nonneg hδ.1.le _
    have hid : δ₀ ^ (-β) * δ₀ ^ β = 1 := by
      rw [← Real.rpow_add hδ₀]
      simp
    have hCδ : 1 ≤ C * δ ^ β := by
      have h1 := mul_le_mul_of_nonneg_left hδpow hδ₀pow
      have h2 := mul_le_mul_of_nonneg_right
        (le_max_right k (δ₀ ^ (-β))) hδpow0
      nlinarith
    calc
      P {ω | ∃ z ∈ ball (0 : ℂ) ρ,
        ENNReal.ofReal (δ ^ ξ) < wholePlaneArea γ Y ω (ball z δ)} ≤
          P Set.univ := measure_mono (subset_univ _)
      _ = 1 := measure_univ
      _ ≤ ENNReal.ofReal (C * δ ^ β) := by
        simpa using ENNReal.ofReal_le_ofReal hCδ

end MatedCRTHarmonic.GMCUpper
