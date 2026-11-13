/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMCUpper.CircleCover at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCUpper.CircleBox
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L4Max

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric LQGMetric

namespace MatedCRTHarmonic.GMCUpper

private def unitSquare : Set ℂ := SupTail.ferniqueBox ⟨-1, -1⟩ 2

private lemma ball_subset_unitSquare {ρ : ℝ} (hρ : ρ ≤ 1) :
    ball (0 : ℂ) ρ ⊆ unitSquare := by
  intro z hz
  have hnorm : ‖z‖ < 1 := (mem_ball_zero_iff.1 hz).trans_le hρ
  have hre := Complex.abs_re_le_norm z
  have him := Complex.abs_im_le_norm z
  rw [unitSquare, DG.mem_ferniqueBox_iff]
  dsimp
  constructor
  · linarith [neg_abs_le z.re]
  constructor
  · linarith [le_abs_self z.re]
  constructor
  · linarith [neg_abs_le z.im]
  · linarith [le_abs_self z.im]

private lemma norm_le_four_of_unitSquare {z : ℂ} (hz : z ∈ unitSquare) : ‖z‖ ≤ 4 := by
  have h := (DG.mem_ferniqueBox_iff ⟨-1, -1⟩ 2 z).1 hz
  have hre : |z.re| ≤ 1 := abs_le.mpr ⟨by linarith [h.1], by linarith [h.2.1]⟩
  have him : |z.im| ≤ 1 := abs_le.mpr ⟨by linarith [h.2.2.1], by linarith [h.2.2.2]⟩
  exact (Complex.norm_le_abs_re_add_abs_im z).trans (by linarith)

/-- The square-covering Gaussian estimate with the exact leading constant
needed for the coefficient `2` in the final supremum bound. -/
theorem circleAverage_square_tail {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → DistC} {H : ℝ → ℂ → Ω → ℝ}
    (hX : IsNormalizedWPGFF X P)
    (hH : DFGPS.IsCircleAvgVersion X P H)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) {x : ℝ} (hx : 0 ≤ x) :
    P.real {ω | Real.sqrt (2 * (-Real.log r + 2 * Real.log 5 + 1) *
      Real.log ((⌈4 / r⌉₊ : ℕ) ^ 2 : ℕ)) + SupTail.ferniqueCF * Real.sqrt 2 + x ≤
      ⨆ z : unitSquare, H r z ω} ≤
      Real.exp (-x ^ 2 / (2 * (-Real.log r + 2 * Real.log 5 + 1))) := by
  letI : IsProbabilityMeasure P := hX.1.gaussian.isProbabilityMeasure
  have hG := isGFFCircleAverage_of_version hX hH
  let Y : ℂ → Ω → ℝ := fun z ω => H r z ω
  have hYG : IsGaussianProcess Y P :=
    hG.isGaussianProcess.comp_right (fun z => (⟨r, hr⟩, z))
  have hY0 : ∀ z, ∫ ω, Y z ω ∂P = 0 := fun z => hG.integral_eq_zero r hr z
  have hYc : ∀ ω, ContinuousOn (fun z => Y z ω) unitSquare :=
    fun ω => (hG.continuous r hr ω).continuousOn
  have hinc : ∀ z ∈ unitSquare, ∀ w ∈ unitSquare, ‖z - w‖ ≤ r →
      ∫ ω, (Y w ω - Y z ω) ^ 2 ∂P ≤ 2 * ‖z - w‖ / r := by
    intro z _ w _ _
    have h := hH.integral_sq_sub hX.1 hr hr w z
    simp only [sub_self, abs_zero, zero_add, min_self] at h
    calc ∫ ω, (Y w ω - Y z ω) ^ 2 ∂P ≤ 2 * (‖w - z‖ / r) := h
      _ = 2 * ‖z - w‖ / r := by rw [norm_sub_rev]; ring
  have hs2 : 0 < -Real.log r + 2 * Real.log 5 + 1 := by
    have hlog := Real.log_nonpos hr.le hr1
    have hlog5 := Real.log_nonneg (show (1 : ℝ) ≤ 5 by norm_num)
    linarith
  have hvar : ∀ z ∈ unitSquare, Var[Y z; P] ≤ -Real.log r + 2 * Real.log 5 + 1 := by
    intro z hz
    have hm : AEMeasurable (Y z) P := hYG.aemeasurable z
    rw [← covariance_self hm, hG.covariance_eq r hr r hr z z]
    exact (GMCFacts.gffCircleCov_self_le hr hr1 (norm_le_four_of_unitSquare hz)).trans
      (by linarith)
  simpa only [unitSquare, show (2 : ℝ) * 2 = 4 by norm_num, Y] using
    (DGo.dgo_prop33_tail_of_var hYG hY0 (y := ⟨-1, -1⟩) (b := 2) (δ := r)
      (A := 2) (σ2 := -Real.log r + 2 * Real.log 5 + 1)
      (by norm_num) hr (by norm_num) hs2 hYc hinc hvar hx)

/-- The square-covering estimate for the negative circle-average field. -/
theorem circleAverage_square_tail_neg {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → DistC} {H : ℝ → ℂ → Ω → ℝ}
    (hX : IsNormalizedWPGFF X P)
    (hH : DFGPS.IsCircleAvgVersion X P H)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) {x : ℝ} (hx : 0 ≤ x) :
    P.real {ω | Real.sqrt (2 * (-Real.log r + 2 * Real.log 5 + 1) *
      Real.log ((⌈4 / r⌉₊ : ℕ) ^ 2 : ℕ)) + SupTail.ferniqueCF * Real.sqrt 2 + x ≤
      ⨆ z : unitSquare, -H r z ω} ≤
      Real.exp (-x ^ 2 / (2 * (-Real.log r + 2 * Real.log 5 + 1))) := by
  letI : IsProbabilityMeasure P := hX.1.gaussian.isProbabilityMeasure
  have hG := isGFFCircleAverage_of_version hX hH
  let Y : ℂ → Ω → ℝ := fun z ω => -H r z ω
  have hYG : IsGaussianProcess Y P := by
    have h := (hG.isGaussianProcess.comp_right (fun z => (⟨r, hr⟩, z))).smul
      (fun _ => (-1 : ℝ))
    simpa [Y, smul_eq_mul] using h
  have hY0 : ∀ z, ∫ ω, Y z ω ∂P = 0 := by
    intro z
    simp only [Y, integral_neg, hG.integral_eq_zero r hr z, neg_zero]
  have hYc : ∀ ω, ContinuousOn (fun z => Y z ω) unitSquare :=
    fun ω => (hG.continuous r hr ω).neg.continuousOn
  have hinc : ∀ z ∈ unitSquare, ∀ w ∈ unitSquare, ‖z - w‖ ≤ r →
      ∫ ω, (Y w ω - Y z ω) ^ 2 ∂P ≤ 2 * ‖z - w‖ / r := by
    intro z _ w _ _
    have h := hH.integral_sq_sub hX.1 hr hr w z
    simp only [sub_self, abs_zero, zero_add, min_self] at h
    have he : (fun ω => (Y w ω - Y z ω) ^ 2) =
        fun ω => (H r w ω - H r z ω) ^ 2 := by
      funext ω
      dsimp [Y]
      ring
    rw [he]
    calc ∫ ω, (H r w ω - H r z ω) ^ 2 ∂P ≤ 2 * (‖w - z‖ / r) := h
      _ = 2 * ‖z - w‖ / r := by rw [norm_sub_rev]; ring
  have hs2 : 0 < -Real.log r + 2 * Real.log 5 + 1 := by
    have hlog := Real.log_nonpos hr.le hr1
    have hlog5 := Real.log_nonneg (show (1 : ℝ) ≤ 5 by norm_num)
    linarith
  have hvar : ∀ z ∈ unitSquare, Var[Y z; P] ≤ -Real.log r + 2 * Real.log 5 + 1 := by
    intro z hz
    have hm : AEMeasurable (H r z) P :=
      (hG.isGaussianProcess.comp_right (fun z => (⟨r, hr⟩, z))).aemeasurable z
    change Var[-(H r z); P] ≤ _
    rw [variance_neg, ← covariance_self hm, hG.covariance_eq r hr r hr z z]
    exact (GMCFacts.gffCircleCov_self_le hr hr1 (norm_le_four_of_unitSquare hz)).trans
      (by linarith)
  simpa only [unitSquare, show (2 : ℝ) * 2 = 4 by norm_num, Y] using
    (DGo.dgo_prop33_tail_of_var hYG hY0 (y := ⟨-1, -1⟩) (b := 2) (δ := r)
      (A := 2) (σ2 := -Real.log r + 2 * Real.log 5 + 1)
      (by norm_num) hr (by norm_num) hs2 hYc hinc hvar hx)

private lemma square_threshold_le {r δ' : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hδ : 0 < δ')
    (hL : 2 * (2 * Real.log 5 + 1 + Real.log 50 +
      SupTail.ferniqueCF * Real.sqrt 2) / δ' ≤ Real.log r⁻¹) :
    Real.sqrt (2 * (-Real.log r + 2 * Real.log 5 + 1) *
      Real.log ((⌈4 / r⌉₊ : ℕ) ^ 2 : ℕ)) +
      SupTail.ferniqueCF * Real.sqrt 2 + δ' / 2 * Real.log r⁻¹ ≤
      (2 + δ') * Real.log r⁻¹ := by
  set L := Real.log r⁻¹
  set c := 2 * Real.log 5 + 1
  set a := Real.log 50
  have hL0 : 0 ≤ L := Real.log_nonneg ((one_le_inv₀ hr).2 hr1)
  have hc : 0 ≤ c := by
    dsimp [c]
    have := Real.log_nonneg (show (1 : ℝ) ≤ 5 by norm_num)
    linarith
  have ha : 0 ≤ a := Real.log_nonneg (by norm_num)
  have hf : 0 ≤ SupTail.ferniqueCF * Real.sqrt 2 :=
    mul_nonneg SupTail.ferniqueCF_pos.le (Real.sqrt_nonneg _)
  have hlog : Real.log ((⌈4 / r⌉₊ : ℕ) ^ 2 : ℕ) ≤ a + 2 * L := by
    have h := DG.log_two_ceil_sq_le (s := 4) (δ := r) (by norm_num) hr hr1
    have hm : 0 < (⌈4 / r⌉₊ : ℝ) := Nat.cast_pos.2
      (Nat.ceil_pos.2 (div_pos (by norm_num) hr))
    have hmono : Real.log ((⌈4 / r⌉₊ : ℕ) ^ 2 : ℕ) ≤
        Real.log (2 * (⌈4 / r⌉₊ : ℝ) ^ 2) := by
      apply Real.log_le_log (by exact_mod_cast pow_pos hm 2)
      push_cast
      nlinarith [sq_nonneg (⌈4 / r⌉₊ : ℝ)]
    have he : (2 : ℝ) * (4 + 1) ^ 2 = 50 := by norm_num
    rw [he] at h
    have h' : Real.log (2 * (⌈4 / r⌉₊ : ℝ) ^ 2) ≤ a + 2 * L := by
      simpa only [a, L] using h
    exact hmono.trans h'
  have hrw : -Real.log r = L := by simp [L, Real.log_inv]
  have hroot : Real.sqrt (2 * (L + c) * Real.log ((⌈4 / r⌉₊ : ℕ) ^ 2 : ℕ)) ≤
      2 * L + c + a := by
    have harg : 0 ≤ 2 * (L + c) * Real.log ((⌈4 / r⌉₊ : ℕ) ^ 2 : ℕ) := by
      have hm : 1 ≤ (⌈4 / r⌉₊ : ℕ) := Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (Nat.ceil_pos.2 (div_pos (by norm_num) hr)))
      have hlog0 : 0 ≤ Real.log ((⌈4 / r⌉₊ : ℕ) ^ 2 : ℕ) :=
        Real.log_nonneg (by exact_mod_cast pow_le_pow_left₀ (by norm_num : (0 : ℕ) ≤ 1) hm 2)
      positivity
    rw [Real.sqrt_le_left (by positivity)]
    have hmul : 2 * (L + c) * Real.log ((⌈4 / r⌉₊ : ℕ) ^ 2 : ℕ) ≤
        2 * (L + c) * (a + 2 * L) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    nlinarith [sq_nonneg (c - a), mul_nonneg hL0 ha]
  rw [hrw]
  have hconst : c + a + SupTail.ferniqueCF * Real.sqrt 2 ≤ δ' / 2 * L := by
    have hmul := (mul_le_mul_of_nonneg_left hL hδ.le)
    dsimp [c, a] at hmul ⊢
    field_simp at hmul ⊢
    linarith
  dsimp [c] at hroot
  dsimp [c] at hconst
  have he : 2 * (L + (2 * Real.log 5 + 1)) *
      Real.log ((⌈4 / r⌉₊ : ℕ) ^ 2 : ℕ) =
      2 * (L + 2 * Real.log 5 + 1) * Real.log ((⌈4 / r⌉₊ : ℕ) ^ 2 : ℕ) := by ring
  rw [he] at hroot
  linarith

private lemma square_tail_rate {r δ' : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hδ : 0 < δ')
    (hc : 2 * Real.log 5 + 1 ≤ Real.log r⁻¹) :
    Real.exp (-((δ' / 2 * Real.log r⁻¹) ^ 2) /
      (2 * (-Real.log r + 2 * Real.log 5 + 1))) ≤
      r ^ (δ' ^ 2 / 16) := by
  set L := Real.log r⁻¹
  set c := 2 * Real.log 5 + 1
  have hL : 0 ≤ L := Real.log_nonneg ((one_le_inv₀ hr).2 hr1)
  have hc0 : 0 < c := by
    dsimp [c]
    have hlog := Real.log_nonneg (show (1 : ℝ) ≤ 5 by norm_num)
    linarith
  have hcL : c ≤ L := hc
  have hden : 0 < 2 * (L + c) := by positivity
  have hbase : L * (L + c) ≤ 2 * L ^ 2 := by nlinarith [mul_nonneg hL (sub_nonneg.2 hcL)]
  have hmul := mul_le_mul_of_nonneg_left hbase (sq_nonneg δ')
  have hfrac : δ' ^ 2 / 16 * L ≤ (δ' / 2 * L) ^ 2 / (2 * (L + c)) := by
    apply (le_div_iff₀ hden).2
    nlinarith
  have he : -Real.log r = L := by simp [L, Real.log_inv]
  rw [he]
  have hrpow : r ^ (δ' ^ 2 / 16) = Real.exp (-(δ' ^ 2 / 16 * L)) := by
    rw [Real.rpow_def_of_pos hr]
    have hlogr : Real.log r = -L := by
      dsimp [L]
      rw [Real.log_inv]
      ring
    rw [hlogr]
    ring
  rw [hrpow]
  dsimp [c] at hfrac
  have he2 : L + (2 * Real.log 5 + 1) = L + 2 * Real.log 5 + 1 := by ring
  rw [he2] at hfrac
  exact Real.exp_le_exp.2 (by simpa [neg_div] using neg_le_neg hfrac)

private lemma le_square_iSup {f : ℂ → ℝ} (hf : ContinuousOn f unitSquare)
    {z : ℂ} (hz : z ∈ unitSquare) : f z ≤ ⨆ w : unitSquare, f w := by
  have hB : BddAbove (range fun w : unitSquare => f w) := by
    obtain ⟨M, hM⟩ := (SupTail.isCompact_ferniqueBox ⟨-1, -1⟩ 2).bddAbove_image hf
    exact ⟨M, by rintro _ ⟨w, rfl⟩; exact hM ⟨w, w.2, rfl⟩⟩
  exact le_ciSup hB ⟨z, hz⟩

private lemma circleAverage_small_tail {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → DistC} {H : ℝ → ℂ → Ω → ℝ}
    (hX : IsNormalizedWPGFF X P)
    (hH : DFGPS.IsCircleAvgVersion X P H)
    {δ' : ℝ} (hδ : 0 < δ') {ρ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hL₁ : 2 * (2 * Real.log 5 + 1 + Real.log 50 +
      SupTail.ferniqueCF * Real.sqrt 2) / δ' ≤ Real.log r⁻¹)
    (hL₂ : 2 * Real.log 5 + 1 ≤ Real.log r⁻¹) :
    P {ω | ∃ z ∈ ball (0 : ℂ) ρ,
      (2 + δ') * Real.log r⁻¹ < |H r z ω|} ≤
      ENNReal.ofReal (2 * r ^ (δ' ^ 2 / 16)) := by
  letI : IsProbabilityMeasure P := hX.1.gaussian.isProbabilityMeasure
  let T : ℝ := Real.sqrt (2 * (-Real.log r + 2 * Real.log 5 + 1) *
    Real.log ((⌈4 / r⌉₊ : ℕ) ^ 2 : ℕ)) +
      SupTail.ferniqueCF * Real.sqrt 2 + δ' / 2 * Real.log r⁻¹
  let E : Set Ω := {ω | ∃ z ∈ ball (0 : ℂ) ρ,
    (2 + δ') * Real.log r⁻¹ < |H r z ω|}
  let A : Set Ω := {ω | T ≤ ⨆ z : unitSquare, H r z ω}
  let B : Set Ω := {ω | T ≤ ⨆ z : unitSquare, -H r z ω}
  have hT : T ≤ (2 + δ') * Real.log r⁻¹ := square_threshold_le hr hr1 hδ hL₁
  have hG := isGFFCircleAverage_of_version hX hH
  have hsub : E ⊆ A ∪ B := by
    rintro ω ⟨z, hz, hbad⟩
    have hzS := ball_subset_unitSquare hρ.2.le hz
    rcases le_total 0 (H r z ω) with hs | hs
    · rw [abs_of_nonneg hs] at hbad
      left
      exact hT.trans (hbad.le.trans
        (le_square_iSup ((hG.continuous r hr ω).continuousOn) hzS))
    · rw [abs_of_nonpos hs] at hbad
      right
      exact hT.trans (hbad.le.trans
        (le_square_iSup ((hG.continuous r hr ω).neg.continuousOn) hzS))
  have hrate := square_tail_rate hr hr1 hδ hL₂
  have hlog0 : 0 ≤ Real.log r⁻¹ := Real.log_nonneg ((one_le_inv₀ hr).2 hr1)
  have hx : 0 ≤ δ' / 2 * Real.log r⁻¹ :=
    mul_nonneg (div_nonneg hδ.le (by norm_num)) hlog0
  have hA : P.real A ≤ r ^ (δ' ^ 2 / 16) :=
    (circleAverage_square_tail hX hH hr hr1
      (x := δ' / 2 * Real.log r⁻¹) hx).trans hrate
  have hB : P.real B ≤ r ^ (δ' ^ 2 / 16) :=
    (circleAverage_square_tail_neg hX hH hr hr1
      (x := δ' / 2 * Real.log r⁻¹) hx).trans hrate
  calc P E ≤ P (A ∪ B) := measure_mono hsub
    _ ≤ P A + P B := measure_union_le _ _
    _ = ENNReal.ofReal (P.real A) + ENNReal.ofReal (P.real B) := by
      rw [ofReal_measureReal (measure_ne_top _ _), ofReal_measureReal (measure_ne_top _ _)]
    _ ≤ ENNReal.ofReal (r ^ (δ' ^ 2 / 16)) +
        ENNReal.ofReal (r ^ (δ' ^ 2 / 16)) :=
      add_le_add (ENNReal.ofReal_le_ofReal hA) (ENNReal.ofReal_le_ofReal hB)
    _ = ENNReal.ofReal (2 * r ^ (δ' ^ 2 / 16)) := by
      rw [← ENNReal.ofReal_add (Real.rpow_pos_of_pos hr _).le]
      · congr 1
        ring
      · exact (Real.rpow_pos_of_pos hr _).le

/-- [MS16b] Proposition 2.4 with the sharp leading coefficient `2`, for
the whole-plane circle-average process in the actual model. -/
theorem circleAverageSupBoundModel_holds {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → DistC} {H : ℝ → ℂ → Ω → ℝ}
    (hX : IsNormalizedWPGFF X P)
    (hH : DFGPS.IsCircleAvgVersion X P H) :
    CircleAverageSupBoundModel P X H hX hH := by
  letI : IsProbabilityMeasure P := hX.1.gaussian.isProbabilityMeasure
  intro δ' hδ
  let β : ℝ := δ' ^ 2 / 16
  have hβ : 0 < β := by dsimp [β]; positivity
  let K : ℝ := max 1 (max
    (2 * (2 * Real.log 5 + 1 + Real.log 50 +
      SupTail.ferniqueCF * Real.sqrt 2) / δ')
    (2 * Real.log 5 + 1))
  have hK : 0 < K := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)
  let r₀ : ℝ := Real.exp (-K)
  have hr₀ : 0 < r₀ := Real.exp_pos _
  have hr₀1 : r₀ < 1 := by
    dsimp [r₀]
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.2 (by linarith)
  refine ⟨β, hβ, fun ρ hρ => ?_⟩
  let C : ℝ := 2 * Real.exp (β * K)
  have hC2 : 2 ≤ C := by
    dsimp [C]
    have he : 1 ≤ Real.exp (β * K) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.2 (mul_nonneg hβ.le hK.le)
    linarith
  refine ⟨C, fun r hr => ?_⟩
  obtain ⟨hr0, hr1⟩ := hr
  by_cases hrs : r < r₀
  · have hlogK : K < Real.log r⁻¹ := by
      have h := Real.log_lt_log hr0 hrs
      rw [show Real.log r₀ = -K by simp [r₀]] at h
      rw [Real.log_inv]
      linarith
    have hL₁ : 2 * (2 * Real.log 5 + 1 + Real.log 50 +
        SupTail.ferniqueCF * Real.sqrt 2) / δ' ≤ Real.log r⁻¹ :=
      (le_max_left _ _).trans (le_max_right _ _) |>.trans hlogK.le
    have hL₂ : 2 * Real.log 5 + 1 ≤ Real.log r⁻¹ :=
      (le_max_right _ _).trans (le_max_right _ _) |>.trans hlogK.le
    have hs := circleAverage_small_tail hX hH hδ hρ hr0 hr1.le hL₁ hL₂
    exact hs.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hC2 (Real.rpow_pos_of_pos hr0 β).le))
  · have hrr : r₀ ≤ r := le_of_not_gt hrs
    have hlogr : -K ≤ Real.log r := by
      have h := Real.log_le_log hr₀ hrr
      simpa only [r₀, Real.log_exp] using h
    have hpow : Real.exp (-(β * K)) ≤ r ^ β := by
      rw [Real.rpow_def_of_pos hr0]
      exact Real.exp_le_exp.2 (by nlinarith [mul_nonneg hβ.le (sub_nonneg.2 hlogr)])
    have hCpow : 1 ≤ C * r ^ β := by
      have h1 : C * Real.exp (-(β * K)) = 2 := by
        dsimp [C]
        calc 2 * Real.exp (β * K) * Real.exp (-(β * K)) =
            2 * (Real.exp (β * K) * Real.exp (-(β * K))) := by ring
          _ = 2 * Real.exp (β * K + -(β * K)) := by rw [Real.exp_add]
          _ = 2 := by norm_num
      have h2 := mul_le_mul_of_nonneg_left hpow (by dsimp [C]; positivity : 0 ≤ C)
      linarith
    calc P {ω | ∃ z ∈ ball (0 : ℂ) ρ,
          (2 + δ') * Real.log r⁻¹ < |H r z ω|}
        ≤ 1 := by
          have hbound : P {ω | ∃ z ∈ ball (0 : ℂ) ρ,
              (2 + δ') * Real.log r⁻¹ < |H r z ω|} ≤ P Set.univ :=
            measure_mono (Set.subset_univ _)
          simpa only [measure_univ] using hbound
      _ = ENNReal.ofReal 1 := by norm_num
      _ ≤ ENNReal.ofReal (C * r ^ β) := ENNReal.ofReal_le_ofReal hCpow

end MatedCRTHarmonic.GMCUpper
