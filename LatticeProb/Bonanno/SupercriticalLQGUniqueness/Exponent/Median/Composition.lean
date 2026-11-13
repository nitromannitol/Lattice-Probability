/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.Median.Composition at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.Median.Bridge




 

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Exponent.Median

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

 

theorem isMedian_heat_rectLen_of_version
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : IsNormalizedWholePlaneGFF h P)
    (ξ ε : ℝ) (hε : 0 < ε) (X : Ω → C(ℂ, ℝ))
    (hX : ∀ z : ℂ, ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => h ω (positiveHeatTrunc
        ⟨ε ^ 2 / 2, Set.mem_Ioi.mpr (div_pos (pow_pos hε 2) two_pos)⟩ z n))
        atTop (𝓝 (X ω z)))
    (a : ℝ≥0∞)
    (hm : IsMedian P (fun ω => lfppCrossingLength ξ (X ω)) a) :
    IsMedian P (fun ω => rectLen ξ (heatMollify ε (h ω)) (rectAB 1 1)) a := by
  obtain ⟨H, hHeq, hHlim⟩ := exists_heatVersion hh ε hε
  have hmH := (Exponent.HeatVersion.isMedian_heat_version_iff ξ ε hε X H hX hHlim a).mp hm
  have hae : (fun ω => lfppCrossingLength ξ (H ω)) =ᵐ[P]
      (fun ω => rectLen ξ (heatMollify ε (h ω)) (rectAB 1 1)) := by
    filter_upwards [hHeq] with ω hω
    rw [Exponent.HeatVersion.lfppCrossingLength_eq_rectLen]
    congr 1
    funext z
    exact hω z
  exact (Exponent.HeatVersion.isMedian_congr_ae P hae a).mp hmH

 
theorem median_between_of_cdf_margins_on_space
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (H : Ω → ℝ≥0∞) (a lo hi : ℝ≥0∞)
    (hm : IsMedian P H a)
    (hlow : P {ω | H ω < lo} ≤ (3 / 8 : ℝ≥0∞))
    (hhigh : (5 / 8 : ℝ≥0∞) ≤ P {ω | H ω ≤ hi}) :
    lo ≤ a ∧ a ≤ hi := by
  have hhalf : (2⁻¹ : ℝ≥0∞) = ENNReal.ofReal (1 / 2 : ℝ) := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
      ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  have hthree : (3 / 8 : ℝ≥0∞) = ENNReal.ofReal (3 / 8 : ℝ) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  have hfive : (5 / 8 : ℝ≥0∞) = ENNReal.ofReal (5 / 8 : ℝ) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  constructor
  · by_contra h
    have hlt : a < lo := lt_of_not_ge h
    have hsub : {ω | H ω ≤ a} ⊆ {ω | H ω < lo} := by
      intro ω hω
      exact lt_of_le_of_lt hω hlt
    have hbad : (2⁻¹ : ℝ≥0∞) ≤ (3 / 8 : ℝ≥0∞) :=
      hm.2.1.trans ((measure_mono hsub).trans hlow)
    have hstrict : (3 / 8 : ℝ≥0∞) < 2⁻¹ := by
      rw [hthree, hhalf]
      exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)
    exact (not_le.mpr hstrict) hbad
  · by_contra h
    have hlt : hi < a := lt_of_not_ge h
    have hsub : {ω | a ≤ H ω} ⊆ {ω | H ω ≤ hi}ᶜ := by
      intro ω hω
      simpa only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] using hlt.trans_le hω
    have hsum : P {ω | H ω ≤ hi} + P {ω | a ≤ H ω} ≤ 1 := by
      calc
        P {ω | H ω ≤ hi} + P {ω | a ≤ H ω} ≤
            P {ω | H ω ≤ hi} + P {ω | H ω ≤ hi}ᶜ :=
          add_le_add le_rfl (measure_mono hsub)
        _ = 1 := by
          change P (H ⁻¹' Set.Iic hi) + P (H ⁻¹' Set.Iic hi)ᶜ = 1
          rw [measure_add_measure_compl₀
            (hm.1.nullMeasurableSet_preimage measurableSet_Iic), measure_univ]
    have hbad : (5 / 8 : ℝ≥0∞) + 2⁻¹ ≤ 1 :=
      (add_le_add hhigh hm.2.2).trans hsum
    have hstrict : (1 : ℝ≥0∞) < (5 / 8 : ℝ≥0∞) + 2⁻¹ := by
      rw [hfive, hhalf, ← ENNReal.ofReal_add (by norm_num) (by norm_num),
        ← ENNReal.ofReal_one]
      exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)
    exact (not_le.mpr hstrict) hbad

 

theorem cdf_margins_of_two_eighth_errors
    {Ω Ω₀ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₀]
    (P : Measure Ω) (P₀ : Measure Ω₀)
    (H : Ω → ℝ≥0∞) (Z L : Ω₀ → ℝ≥0∞)
    (lo zlo u v zhi hi : ℝ≥0∞)
    (h₁ : P {ω | H ω < lo} ≤ P₀ {ω | Z ω < zlo} + (1 / 8 : ℝ≥0∞))
    (h₂ : P₀ {ω | Z ω < zlo} ≤ P₀ {ω | L ω < u} + (1 / 8 : ℝ≥0∞))
    (h₃ : P₀ {ω | L ω < u} ≤ (1 / 8 : ℝ≥0∞))
    (h₄ : (7 / 8 : ℝ≥0∞) ≤ P₀ {ω | L ω ≤ v})
    (h₅ : P₀ {ω | L ω ≤ v} ≤ P₀ {ω | Z ω ≤ zhi} + (1 / 8 : ℝ≥0∞))
    (h₆ : P₀ {ω | Z ω ≤ zhi} ≤ P {ω | H ω ≤ hi} + (1 / 8 : ℝ≥0∞)) :
    P {ω | H ω < lo} ≤ (3 / 8 : ℝ≥0∞) ∧
      (5 / 8 : ℝ≥0∞) ≤ P {ω | H ω ≤ hi} := by
  constructor
  · calc
      P {ω | H ω < lo} ≤ P₀ {ω | Z ω < zlo} + (1 / 8 : ℝ≥0∞) := h₁
      _ ≤ (P₀ {ω | L ω < u} + (1 / 8 : ℝ≥0∞)) + (1 / 8 : ℝ≥0∞) :=
        add_le_add h₂ le_rfl
      _ ≤ ((1 / 8 : ℝ≥0∞) + (1 / 8 : ℝ≥0∞)) + (1 / 8 : ℝ≥0∞) :=
        add_le_add (add_le_add h₃ le_rfl) le_rfl
      _ = (3 / 8 : ℝ≥0∞) := by simp [div_eq_mul_inv]; ring
  · have h : (7 / 8 : ℝ≥0∞) ≤
        P {ω | H ω ≤ hi} + ((1 / 8 : ℝ≥0∞) + (1 / 8 : ℝ≥0∞)) := by
      calc
        (7 / 8 : ℝ≥0∞) ≤ P₀ {ω | L ω ≤ v} := h₄
        _ ≤ P₀ {ω | Z ω ≤ zhi} + (1 / 8 : ℝ≥0∞) := h₅
        _ ≤ (P {ω | H ω ≤ hi} + (1 / 8 : ℝ≥0∞)) +
            (1 / 8 : ℝ≥0∞) := add_le_add h₆ le_rfl
        _ = P {ω | H ω ≤ hi} +
            ((1 / 8 : ℝ≥0∞) + (1 / 8 : ℝ≥0∞)) := by rw [add_assoc]
    have h' : (7 / 8 : ℝ≥0∞) -
        ((1 / 8 : ℝ≥0∞) + (1 / 8 : ℝ≥0∞)) ≤ P {ω | H ω ≤ hi} :=
      tsub_le_iff_right.mpr h
    have hnum : (7 / 8 : ℝ≥0∞) -
        ((1 / 8 : ℝ≥0∞) + (1 / 8 : ℝ≥0∞)) = (5 / 8 : ℝ≥0∞) := by
      apply ENNReal.sub_eq_of_eq_add' (by finiteness)
      simp [div_eq_mul_inv]
      ring
    exact hnum ▸ h'

 


theorem exists_reference_heat_median_sandwich
    {Ω : Type} {Ω₀ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₀]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (P₀ : Measure Ω₀) {W₀ : WNSpace → Ω₀ → ℝ}
    (hW₀ : IsWhiteNoise P₀ W₀) (ξ : ℝ) :
    ∃ (M x B ε₀ : ℝ), 0 < B ∧ 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      let m := Nat.floor (Real.logb 2 (1 / ε))
      let r₁ : ℝ≥0∞ := ENNReal.ofReal (Real.exp (|ξ| * M))
      let r₂ : ℝ≥0∞ := ENNReal.ofReal (Real.exp (|ξ| * x))
      let g : ℝ≥0∞ := ENNReal.ofReal
        (Real.exp (|ξ| * (B * Real.sqrt (m + 1 : ℝ))))
      let u : ℝ := ellN ξ W₀ P₀ m (ENNReal.ofReal (1 / 8 : ℝ))
      let v : ℝ := ellBarN ξ W₀ P₀ m (ENNReal.ofReal (1 / 8 : ℝ))
      ∀ a : ℝ≥0∞,
        IsMedian P (fun ω => rectLen ξ (heatMollify ε (h ω)) (rectAB 1 1)) a →
        r₁⁻¹ * (r₂⁻¹ * (g⁻¹ * ENNReal.ofReal u)) ≤ a ∧
        a ≤ r₁ * (r₂ * (g * ENNReal.ofReal v)) := by
  letI := hW₀.isProbabilityMeasure
  obtain ⟨M, x, ε₁, hε₁, hcmp⟩ :=
    Exponent.HeatVersion.exists_heat_whiteNoise_cdf_bounds P h hh ξ
  obtain ⟨B, hB, hoct⟩ := octave_crossing_cdf_bounds hW₀ ξ
  refine ⟨M, x, B, min ε₁ 1, hB, lt_min hε₁ (by norm_num), ?_⟩
  intro ε hε hεsmall
  dsimp
  let m : ℕ := Nat.floor (Real.logb 2 (1 / ε))
  let r₁ : ℝ≥0∞ := ENNReal.ofReal (Real.exp (|ξ| * M))
  let r₂ : ℝ≥0∞ := ENNReal.ofReal (Real.exp (|ξ| * x))
  let g : ℝ≥0∞ := ENNReal.ofReal
    (Real.exp (|ξ| * (B * Real.sqrt (m + 1 : ℝ))))
  let u : ℝ := ellN ξ W₀ P₀ m (ENNReal.ofReal (1 / 8 : ℝ))
  let v : ℝ := ellBarN ξ W₀ P₀ m (ENNReal.ofReal (1 / 8 : ℝ))
  let H : Ω → ℝ≥0∞ := fun ω => rectLen ξ (heatMollify ε (h ω)) (rectAB 1 1)
  let Z : Ω₀ → ℝ≥0∞ := fun ω => rectLen ξ
    (fun z => phiVer W₀ P₀ ε 1 z ω) (rectAB 1 1)
  let L : Ω₀ → ℝ≥0∞ := fun ω => rectLen ξ
    (fun z => phiMN W₀ P₀ 0 m z ω) (rectAB 1 1)
  let zlo : ℝ≥0∞ := g⁻¹ * ENNReal.ofReal u
  let lo : ℝ≥0∞ := r₁⁻¹ * (r₂⁻¹ * zlo)
  let zhi : ℝ≥0∞ := g * ENNReal.ofReal v
  let hi : ℝ≥0∞ := r₁ * (r₂ * zhi)
  have hε₁' : ε < ε₁ := hεsmall.trans_le (min_le_left _ _)
  have hε1 : ε < 1 := hεsmall.trans_le (min_le_right _ _)
  have hOct := dyadic_octave_of_floor hε hε1
  have hOct' : ((2 : ℝ) ^ m)⁻¹ / 2 ≤ ε ∧ ε ≤ ((2 : ℝ) ^ m)⁻¹ := hOct
  have hOctCDF := hoct m ε hε hOct'.1 hOct'.2
  obtain ⟨Ω', mΩ', P', W, hP', hW, hCDF⟩ := hcmp ε hε hε₁'
  letI : MeasurableSpace Ω' := mΩ'
  letI : IsProbabilityMeasure P' := hP'
  have hεle : ε ≤ 1 := hε1.le
  have hlaw (a : ℝ≥0∞) :=
    phiVer_crossing_cdf_eq_of_whiteNoise hW hW₀ ξ ε hε hεle a
  have hqeq : ENNReal.ofReal (1 / 8 : ℝ) = (1 / 8 : ℝ≥0∞) := by
    rw [show (1 / 8 : ℝ) = (8 : ℝ)⁻¹ by norm_num,
      ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  have hq0 : 0 < ENNReal.ofReal (1 / 8 : ℝ) :=
    ENNReal.ofReal_pos.mpr (by norm_num)
  have hq1 : ENNReal.ofReal (1 / 8 : ℝ) < 1 := by
    rw [hqeq]
    norm_num
  have hqCDF := dyadic_crossing_quantile_cdf hW₀ ξ m
    (ENNReal.ofReal (1 / 8 : ℝ)) hq0 hq1
  have hqbar : 1 - ENNReal.ofReal (1 / 8 : ℝ) = (7 / 8 : ℝ≥0∞) := by
    rw [hqeq]
    apply ENNReal.sub_eq_of_eq_add' (by finiteness)
    simp [div_eq_mul_inv]
    calc
      (1 : ℝ≥0∞) = (8 : ℝ≥0∞)⁻¹ * 8 :=
        (ENNReal.inv_mul_cancel (by norm_num : (8 : ℝ≥0∞) ≠ 0)
          (by finiteness : (8 : ℝ≥0∞) ≠ ∞)).symm
      _ = 7 * 8⁻¹ + 8⁻¹ := by ring
  have hr₁0 : r₁ ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hr₂0 : r₂ ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hg0 : g ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hr₁t : r₁ ≠ ∞ := ENNReal.ofReal_ne_top
  have hr₂t : r₂ ≠ ∞ := ENNReal.ofReal_ne_top
  have hgt : g ≠ ∞ := ENNReal.ofReal_ne_top
  have hmulLo : r₂ * (r₁ * lo) = zlo := by
    dsimp [lo]
    rw [ENNReal.mul_inv_cancel_left hr₁0 hr₁t,
      ENNReal.mul_inv_cancel_left hr₂0 hr₂t]
  have hmulZlo : g * zlo = ENNReal.ofReal u := by
    dsimp [zlo]
    rw [ENNReal.mul_inv_cancel_left hg0 hgt]
  have hCDFlo : P {ω | H ω < lo} ≤ P₀ {ω | Z ω < zlo} +
      (1 / 8 : ℝ≥0∞) := by
    have h := (hCDF lo).1
    rw [Real.sqrt_sq hε.le, hqeq] at h
    change P {ω | H ω < lo} ≤
      P' {ω | rectLen ξ (fun z => phiVer W P' ε 1 z ω) (rectAB 1 1) <
        r₂ * (r₁ * lo)} + (1 / 8 : ℝ≥0∞) at h
    rw [hmulLo, (hlaw zlo).1] at h
    exact h
  have hCDFlo₂ : P₀ {ω | Z ω < zlo} ≤
      P₀ {ω | L ω < ENNReal.ofReal u} + (1 / 8 : ℝ≥0∞) := by
    have h := (hOctCDF zlo).1
    rw [hqeq] at h
    change P₀ {ω | Z ω < zlo} ≤
      P₀ {ω | L ω < g * zlo} + (1 / 8 : ℝ≥0∞) at h
    rwa [hmulZlo] at h
  have hCDFhi₂ : P₀ {ω | L ω ≤ ENNReal.ofReal v} ≤
      P₀ {ω | Z ω ≤ zhi} + (1 / 8 : ℝ≥0∞) := by
    have h := (hOctCDF (ENNReal.ofReal v)).2
    rw [hqeq] at h
    exact h
  have hCDFhi : P₀ {ω | Z ω ≤ zhi} ≤ P {ω | H ω ≤ hi} +
      (1 / 8 : ℝ≥0∞) := by
    have h := (hCDF zhi).2
    rw [Real.sqrt_sq hε.le, hqeq, (hlaw zhi).2] at h
    exact h
  intro a hm
  have hMargins := cdf_margins_of_two_eighth_errors P P₀ H Z L
    lo zlo (ENNReal.ofReal u) (ENNReal.ofReal v) zhi hi
    hCDFlo hCDFlo₂ (by simpa only [L, u, hqeq] using hqCDF.1)
    (by simpa only [L, v, hqbar] using hqCDF.2) hCDFhi₂ hCDFhi
  have hTrap := median_between_of_cdf_margins_on_space P H a lo hi hm
    hMargins.1 hMargins.2
  exact hTrap

 
theorem log_bound_of_triple_exp_sandwich
    (x y z u v lam : ℝ) (a : ℝ≥0∞)
    (hu : 0 < u) (hv : 0 < v) (hlam : 0 < lam)
    (hlo : (ENNReal.ofReal (Real.exp x))⁻¹ *
      ((ENNReal.ofReal (Real.exp y))⁻¹ *
      ((ENNReal.ofReal (Real.exp z))⁻¹ * ENNReal.ofReal u)) ≤ a)
    (hhi : a ≤ ENNReal.ofReal (Real.exp x) *
      (ENNReal.ofReal (Real.exp y) *
      (ENNReal.ofReal (Real.exp z) * ENNReal.ofReal v)))
    (K : ℝ) (hqu : Real.log lam - K ≤ Real.log u)
    (hqv : Real.log v ≤ Real.log lam + K) :
    0 < a ∧ a < ∞ ∧
      |Real.log a.toReal - Real.log lam| ≤ x + y + z + K := by
  have hlow0 : 0 < (ENNReal.ofReal (Real.exp x))⁻¹ *
      ((ENNReal.ofReal (Real.exp y))⁻¹ *
      ((ENNReal.ofReal (Real.exp z))⁻¹ * ENNReal.ofReal u)) := by
    have hx : 0 < (ENNReal.ofReal (Real.exp x))⁻¹ :=
      ENNReal.inv_pos.mpr (by finiteness)
    have hy : 0 < (ENNReal.ofReal (Real.exp y))⁻¹ :=
      ENNReal.inv_pos.mpr (by finiteness)
    have hz : 0 < (ENNReal.ofReal (Real.exp z))⁻¹ :=
      ENNReal.inv_pos.mpr (by finiteness)
    have hu' : 0 < ENNReal.ofReal u := ENNReal.ofReal_pos.mpr hu
    exact ENNReal.mul_pos hx.ne'
      (ENNReal.mul_pos hy.ne' (ENNReal.mul_pos hz.ne' hu'.ne').ne').ne'
  have ha0 : 0 < a := lt_of_lt_of_le hlow0 hlo
  have hat : a < ∞ := lt_of_le_of_lt hhi (by finiteness)
  have hlor : Real.exp (-(x + y + z)) * u ≤ a.toReal := by
    have h := (ENNReal.toReal_le_toReal (by finiteness) hat.ne).mpr hlo
    simp only [ENNReal.toReal_mul, ENNReal.toReal_inv,
      ENNReal.toReal_ofReal (Real.exp_pos _).le,
      ENNReal.toReal_ofReal hu.le] at h
    convert h using 1 <;> simp [Real.exp_add, Real.exp_neg] <;> ring
  have hhir : a.toReal ≤ Real.exp (x + y + z) * v := by
    have h := (ENNReal.toReal_le_toReal hat.ne (by finiteness)).mpr hhi
    simp only [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.exp_pos _).le,
      ENNReal.toReal_ofReal hv.le] at h
    convert h using 1 <;> simp [Real.exp_add] <;> ring
  have har : 0 < a.toReal := ENNReal.toReal_pos ha0.ne' hat.ne
  exact ⟨ha0, hat,
    Exponent.HeatVersion.log_median_bound_of_sandwich hu hv hlam har hlor hhir hqu hqv⟩


 

theorem exists_reference_heat_median_log_bound
    {Ω : Type} {Ω₀ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₀]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (P₀ : Measure Ω₀) {W₀ : WNSpace → Ω₀ → ℝ}
    (hW₀ : IsWhiteNoise P₀ W₀) (ξ : ℝ) :
    ∃ (C ε₀ : ℝ), 0 < C ∧ 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ a : ℝ≥0∞,
      IsMedian P (fun ω => rectLen ξ (heatMollify ε (h ω)) (rectAB 1 1)) a →
      let m := Nat.floor (Real.logb 2 (1 / ε))
      0 < a ∧ a < ∞ ∧
        |Real.log a.toReal - Real.log (lambdaN ξ W₀ P₀ m)| ≤
          C * Real.sqrt ((m : ℝ) + 1) + C := by
  letI := hW₀.isProbabilityMeasure
  obtain ⟨M, x, B, ε₀, hB, hε₀, hsand⟩ :=
    exists_reference_heat_median_sandwich P h hh P₀ hW₀ ξ
  let K : ℝ := Real.sqrt (2 * ξ ^ 2 * Real.log 2) / (1 / 8 : ℝ)
  let C : ℝ := 1 + |ξ| * (|M| + |x| + B) + K
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hC : 0 < C := by
    dsimp [C]
    have : 0 ≤ |ξ| * (|M| + |x| + B) :=
      mul_nonneg (abs_nonneg _) (by positivity)
    linarith
  refine ⟨C, ε₀, hC, hε₀, ?_⟩
  intro ε hε hεsmall a hm
  dsimp
  let m : ℕ := Nat.floor (Real.logb 2 (1 / ε))
  let u : ℝ := ellN ξ W₀ P₀ m (ENNReal.ofReal (1 / 8 : ℝ))
  let v : ℝ := ellBarN ξ W₀ P₀ m (ENNReal.ofReal (1 / 8 : ℝ))
  let lam : ℝ := lambdaN ξ W₀ P₀ m
  have hq0 : 0 < ENNReal.ofReal (1 / 8 : ℝ) :=
    ENNReal.ofReal_pos.mpr (by norm_num)
  have hqhalf : ENNReal.ofReal (1 / 8 : ℝ) ≤ (2⁻¹ : ℝ≥0∞) := by
    rw [show (1 / 8 : ℝ) = (8 : ℝ)⁻¹ by norm_num,
      ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  have hq1 : ENNReal.ofReal (1 / 8 : ℝ) < 1 :=
    hqhalf.trans_lt inv_two_lt_one'
  have hu : 0 < u := T20B.ellN_pos hW₀ hq0 hq1 m
  have hlam : 0 < lam := lambdaN_pos hW₀ m
  have hv : 0 < v :=
    hlam.trans_le (T20B.lambdaN_le_ellBarN hq0 hqhalf m)
  have hquant := dyadic_quantile_sandwich hW₀ ξ m
  have hqu : Real.log lam - K * Real.sqrt m ≤ Real.log u := by
    have h := Real.log_le_log
      (mul_pos (Real.exp_pos _) hlam) hquant.1
    change Real.log (Real.exp (-K * Real.sqrt m) * lam) ≤ Real.log u at h
    rw [Real.log_mul (Real.exp_pos _).ne' hlam.ne', Real.log_exp] at h
    linarith
  have hqv : Real.log v ≤ Real.log lam + K * Real.sqrt m := by
    have h := Real.log_le_log hv hquant.2
    change Real.log v ≤ Real.log (Real.exp (K * Real.sqrt m) * lam) at h
    rw [Real.log_mul (Real.exp_pos _).ne' hlam.ne', Real.log_exp] at h
    linarith
  have hs := hsand ε hε hεsmall a hm
  have hlog := log_bound_of_triple_exp_sandwich
    (|ξ| * M) (|ξ| * x) (|ξ| * (B * Real.sqrt ((m : ℝ) + 1)))
    u v lam a hu hv hlam hs.1 hs.2 (K * Real.sqrt m) hqu hqv
  obtain ⟨ha0, hat, hbound⟩ := hlog
  refine ⟨ha0, hat, hbound.trans ?_⟩
  have hsqrt : Real.sqrt (m : ℝ) ≤ Real.sqrt ((m : ℝ) + 1) :=
    Real.sqrt_le_sqrt (by norm_num)
  have hsqrt0 : 0 ≤ Real.sqrt ((m : ℝ) + 1) := Real.sqrt_nonneg _
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt ((m : ℝ) + 1) := by
    calc
      (1 : ℝ) = Real.sqrt 1 := by norm_num
      _ ≤ Real.sqrt ((m : ℝ) + 1) :=
        Real.sqrt_le_sqrt (by
          have hmnonneg : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
          linarith)
  have hM : M ≤ |M| := le_abs_self _
  have hx : x ≤ |x| := le_abs_self _
  dsimp [C]
  nlinarith [mul_nonneg (abs_nonneg ξ) (add_nonneg (abs_nonneg M) (abs_nonneg x)),
    mul_nonneg hK (sub_nonneg.mpr hsqrt),
    mul_nonneg (mul_nonneg (abs_nonneg ξ) (by positivity : 0 ≤ |M| + |x| + B))
      (sub_nonneg.mpr hsqrt1),
    mul_nonneg (abs_nonneg ξ) (sub_nonneg.mpr hM),
    mul_nonneg (abs_nonneg ξ) (sub_nonneg.mpr hx)]


 

theorem exists_normalized_heat_version_median_log_bound
    {Ω : Type} {Ω₀ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₀]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (P₀ : Measure Ω₀) {W₀ : WNSpace → Ω₀ → ℝ}
    (hW₀ : IsWhiteNoise P₀ W₀) (ξ : ℝ) :
    ∃ (C ε₀ : ℝ), 0 < C ∧ 0 < ε₀ ∧
      ∀ (X : ℝ → Ω → C(ℂ, ℝ)),
      (∀ ε : ℝ, ∀ hε : 0 < ε, ∀ z : ℂ, ∀ᵐ ω ∂P,
        Tendsto (fun n : ℕ => h ω (positiveHeatTrunc
          ⟨ε ^ 2 / 2, Set.mem_Ioi.mpr (div_pos (pow_pos hε 2) two_pos)⟩ z n))
          atTop (𝓝 (X ε ω z))) →
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ a : ℝ≥0∞,
      IsMedian P (fun ω => lfppCrossingLength ξ (X ε ω)) a →
      let m := Nat.floor (Real.logb 2 (1 / ε))
      0 < a ∧ a < ∞ ∧
        |Real.log a.toReal - Real.log (lambdaN ξ W₀ P₀ m)| ≤
          C * Real.sqrt ((m : ℝ) + 1) + C := by
  obtain ⟨C, ε₀, hC, hε₀, hRef⟩ :=
    exists_reference_heat_median_log_bound P h hh P₀ hW₀ ξ
  refine ⟨C, ε₀, hC, hε₀, ?_⟩
  intro X hX ε hε hεsmall a hm
  exact hRef ε hε hεsmall a
    (isMedian_heat_rectLen_of_version hh ξ ε hε (X ε) (hX ε hε) a hm)


 

end SupercriticalLQGUniqueness.Exponent.Median
