/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4RC2Tail at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA3RTail
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA3RRate

 










set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 
theorem laneA4R_rate_pow {C₀ c₀ ε τ : ℝ} (hC₀ : 0 < C₀) (hc₀ : 0 < c₀) (hε0 : 0 < ε)
    (hε : ε < 1 / 100) (hτ : 0 < τ) :
    ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ K : ℕ, K₀ ≤ K → ∀ v : ℝ, (K : ℝ) ^ (2 / 3 : ℝ) < v →
      (2 : ℝ) ^ ((K : ℝ) ^ ((1 / 2 : ℝ) + 3 * ε)) < Real.exp v ∧
      2 * Real.exp (τ * (v + 1)) * (C₀ * (5 : ℝ) ^ K *
        Real.exp (-(c₀ * v ^ 2 / ((K : ℝ) ^ (3 * ε) * Real.log v)))) ≤
        Real.exp (-(τ * (v + 1)) / 2) := by
  set ρ : ℝ := max 1 τ with hρdef
  have hρ1 : 1 ≤ ρ := le_max_left _ _
  have hρτ : τ ≤ ρ := le_max_right _ _
  have hρ0 : 0 < ρ := by linarith
  set C₁ : ℝ := 2 * Real.exp (3 * τ / 2) * max C₀ 1 with hC₁def
  have hm1 : 1 ≤ max C₀ 1 := le_max_right _ _
  have hC₁ : 0 < C₁ := by positivity
  obtain ⟨K₀, hK₀1, hK₀⟩ := laneA3R_tail_rate hC₁ (div_pos hc₀ hρ0) hε0 hε
  refine ⟨K₀, hK₀1, fun K hK v hv => ?_⟩
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast le_trans hK₀1 hK
  have hx1 : 1 ≤ (K : ℝ) ^ (2 / 3 : ℝ) := Real.one_le_rpow hK1 (by norm_num)
  have hv1 : 1 < v := lt_of_le_of_lt hx1 hv
  have h4v : (K : ℝ) ^ (2 / 3 : ℝ) < 4 * v := by linarith
  obtain ⟨hJ, hrate⟩ := hK₀ K hK (4 * v) h4v
  have e4 : 4 * v / 4 = v := by ring
  rw [e4] at hJ hrate
  refine ⟨hJ, ?_⟩
  set e₃ : ℝ := (K : ℝ) ^ (3 * ε) with he₃
  have he₃0 : 0 < e₃ := Real.rpow_pos_of_pos (by linarith) _
  have hlogv : 0 < Real.log v := Real.log_pos hv1
  set X : ℝ := v ^ 2 / (e₃ * Real.log v) with hX
  have hX0 : 0 ≤ X := by positivity
  set a₁ : ℝ := C₁ * (5 : ℝ) ^ K * Real.exp (-(c₀ / ρ) * v ^ 2 / e₃) with ha₁
  set a₂ : ℝ := C₁ * (5 : ℝ) ^ K * Real.exp (-(c₀ / ρ) * v ^ 2 / (e₃ * Real.log v)) with ha₂
  have ha₁0 : 0 ≤ a₁ := by positivity
  have ha₂0 : 0 < a₂ := by positivity
  
  have h2 : 2 * Real.exp (8 * v) * a₂ ≤ Real.exp (-(4 * v)) := by
    have e8 : 2 * (4 * v) = 8 * v := by ring
    rw [e8] at hrate
    calc 2 * Real.exp (8 * v) * a₂ ≤ 2 * Real.exp (8 * v) * (a₁ + a₂) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_left ha₁0) (by positivity)
      _ ≤ Real.exp (-(4 * v)) := hrate
  have ha₂le : a₂ ≤ Real.exp (-(12 * v)) := by
    have e : Real.exp (-(4 * v)) = Real.exp (8 * v) * Real.exp (-(12 * v)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e] at h2
    have h8 : 0 < Real.exp (8 * v) := Real.exp_pos _
    have : Real.exp (8 * v) * (2 * a₂) ≤ Real.exp (8 * v) * Real.exp (-(12 * v)) := by
      linarith
    have := le_of_mul_le_mul_left this h8
    linarith
  
  have hloga₂ : Real.log a₂ = Real.log C₁ + K * Real.log 5 - c₀ / ρ * X := by
    rw [ha₂, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_mul hC₁.ne'
      (by positivity), Real.log_pow, Real.log_exp, hX]
    ring
  have hlog : Real.log C₁ + K * Real.log 5 - c₀ / ρ * X ≤ -(12 * v) := by
    rw [← hloga₂, ← Real.log_exp (-(12 * v))]
    exact Real.log_le_log ha₂0 ha₂le
  have hlogC₁ : Real.log C₁ = Real.log 2 + 3 * τ / 2 + Real.log (max C₀ 1) := by
    rw [hC₁def, Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num)
      (Real.exp_pos _).ne', Real.log_exp]
  have hlogm : 0 ≤ Real.log (max C₀ 1) := Real.log_nonneg hm1
  have hlogC₀ : Real.log C₀ ≤ Real.log (max C₀ 1) :=
    Real.log_le_log hC₀ (le_max_left _ _)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have hlogC₁0 : 0 ≤ Real.log C₁ := by rw [hlogC₁]; positivity
  have hK0 : (0 : ℝ) ≤ K := by linarith
  have hρmul : ρ * (Real.log C₁ + K * Real.log 5 - c₀ / ρ * X) ≤ ρ * (-(12 * v)) :=
    mul_le_mul_of_nonneg_left hlog hρ0.le
  have hcancel : ρ * (c₀ / ρ * X) = c₀ * X := by
    rw [← mul_assoc, mul_div_cancel₀ c₀ hρ0.ne']
  have hexp : ρ * (Real.log C₁ + K * Real.log 5 - c₀ / ρ * X) =
      ρ * Real.log C₁ + ρ * (K * Real.log 5) - c₀ * X := by
    rw [mul_sub, mul_add, hcancel]
  have i1 : Real.log C₁ ≤ ρ * Real.log C₁ := le_mul_of_one_le_left hlogC₁0 hρ1
  have i2 : K * Real.log 5 ≤ ρ * (K * Real.log 5) :=
    le_mul_of_one_le_left (by positivity) hρ1
  have i3 : 3 * τ / 2 * v ≤ 12 * ρ * v :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  
  have hpos : 0 < 2 * Real.exp (τ * (v + 1)) * (C₀ * (5 : ℝ) ^ K *
      Real.exp (-(c₀ * v ^ 2 / ((K : ℝ) ^ (3 * ε) * Real.log v)))) := by positivity
  rw [← Real.exp_log hpos]
  apply Real.exp_le_exp.mpr
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num)
    (Real.exp_pos _).ne', Real.log_exp, Real.log_mul (by positivity) (Real.exp_pos _).ne',
    Real.log_mul hC₀.ne' (by positivity), Real.log_pow, Real.log_exp]
  have eX : c₀ * v ^ 2 / (e₃ * Real.log v) = c₀ * X := by
    rw [hX, mul_div_assoc]
  rw [eX]
  linarith [hρmul, hexp, i1, i2, i3, hlogC₁, hlogC₀]

 
theorem laneA4R_rpow_lintegral_le_of_tail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z : Ω → ℝ≥0∞} (hZ : AEMeasurable Z P) {τ A x₀ : ℝ}
    (hτ : 0 < τ) (hA : 0 < A) (hx₀ : 0 ≤ x₀)
    (htail : ∀ u, x₀ < u →
      2 * Real.exp (τ * u) * (P {ω | ENNReal.ofReal (A * Real.exp u) ≤ Z ω}).toReal ≤
        Real.exp (-(τ * u) / 2)) :
    ∫⁻ ω, Z ω ^ τ ∂P ≤ ENNReal.ofReal (A ^ τ * (Real.exp (τ * x₀) + 1)) := by
  set Z' := hZ.mk Z with hZ'
  have hZ'm : Measurable Z' := hZ.measurable_mk
  have hZZ' : Z =ᵐ[P] Z' := hZ.ae_eq_mk
  have hτ2 : 0 < τ / 2 := by linarith
  set Y : Ω → ℝ≥0∞ := fun ω => Z' ω ^ (τ / 2) with hY
  have hYm : Measurable Y := hZ'm.pow_const _
  have hA' : 0 < A ^ (τ / 2) := Real.rpow_pos_of_pos hA _
  have hsq := laneA3R_sq_lintegral_le_of_tail (P := P) hYm hA' (by positivity : 0 ≤ τ * x₀ / 2)
    (fun t ht => by
      set u := 2 * t / τ with hu
      have hut : τ * u = 2 * t := by rw [hu]; field_simp
      have hux : x₀ < u := by
        rw [hu, lt_div_iff₀ hτ]; linarith
      have hset : {ω | ENNReal.ofReal (A ^ (τ / 2) * Real.exp t) ≤ Y ω} =ᵐ[P]
          {ω | ENNReal.ofReal (A * Real.exp u) ≤ Z ω} := by
        filter_upwards [hZZ'] with ω hω
        have e : ENNReal.ofReal (A ^ (τ / 2) * Real.exp t) =
            ENNReal.ofReal (A * Real.exp u) ^ (τ / 2) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hτ2.le,
            Real.mul_rpow hA.le (Real.exp_pos _).le, ← Real.exp_mul]
          congr 3
          rw [show u * (τ / 2) = τ * u / 2 by ring, hut]; ring
        change (ENNReal.ofReal (A ^ (τ / 2) * Real.exp t) ≤ Y ω) =
          (ENNReal.ofReal (A * Real.exp u) ≤ Z ω)
        rw [e, hY]
        simp only
        rw [hω, ENNReal.rpow_le_rpow_iff hτ2]
      rw [measure_congr hset]
      have h := htail u hux
      rw [hut] at h
      rwa [show -(2 * t) / 2 = -t by ring] at h)
  calc ∫⁻ ω, Z ω ^ τ ∂P = ∫⁻ ω, Y ω ^ (2 : ℝ) ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [hZZ'] with ω hω
        rw [hY]
        simp only
        rw [hω, ← ENNReal.rpow_mul]
        congr 1; ring
    _ ≤ ENNReal.ofReal ((A ^ (τ / 2)) ^ 2 * (Real.exp (2 * (τ * x₀ / 2)) + 1)) := hsq
    _ = ENNReal.ofReal (A ^ τ * (Real.exp (τ * x₀) + 1)) := by
        congr 1
        rw [← Real.rpow_natCast, ← Real.rpow_mul hA.le]
        congr 2
        · push_cast; ring
        · ring

 
theorem laneA4R_rpow_lintegral_le_of_lt_tail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z : Ω → ℝ≥0∞} (hZ : AEMeasurable Z P) {τ A x₀ : ℝ}
    (hτ : 0 < τ) (hA : 0 < A) (hx₀ : 0 ≤ x₀)
    (htail : ∀ v, x₀ < v →
      2 * Real.exp (τ * (v + 1)) * (P {ω | ENNReal.ofReal (A * Real.exp v) < Z ω}).toReal ≤
        Real.exp (-(τ * (v + 1)) / 2)) :
    ∫⁻ ω, Z ω ^ τ ∂P ≤ ENNReal.ofReal (A ^ τ * (Real.exp (τ * (x₀ + 1)) + 1)) := by
  refine laneA4R_rpow_lintegral_le_of_tail hZ hτ hA (by linarith) fun u hu => ?_
  have hv : x₀ < u - 1 := by linarith
  have hsub : {ω | ENNReal.ofReal (A * Real.exp u) ≤ Z ω} ⊆
      {ω | ENNReal.ofReal (A * Real.exp (u - 1)) < Z ω} := by
    intro ω hω
    refine lt_of_lt_of_le ?_ (show ENNReal.ofReal (A * Real.exp u) ≤ Z ω from hω)
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
    exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr (by linarith)) hA
  have h := htail (u - 1) hv
  rw [sub_add_cancel] at h
  refine le_trans ?_ h
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)

end SupercriticalLQGUniqueness.B2.DG20Conc
