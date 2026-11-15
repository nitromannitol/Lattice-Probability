import LatticeProb.Prob.BrownianWedgeSurvivalSmall

/-! # Subcritical Brownian wedge survival -/

set_option autoImplicit false

open MeasureTheory Set InnerProductSpace
open scoped NNReal ENNReal Topology

namespace LatticeProb

/-- The one-time survival probability in a wedge has every subcritical power bound. -/
theorem brownian_wedge_survival_subcritical {θ p q : ℝ}
    (hθ0 : 0 < θ) (hθπ : θ < Real.pi) (hq : 0 < q) (hqp : q < p)
    (hpθ : p * θ < Real.pi) :
    ∃ K : ℝ, 0 < K ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {x : Euc 2}
        {B : ℝ≥0 → Ω → Euc 2}, IsBrownianSpace 2 x B P →
        ∀ t : ℝ≥0, 0 < (t : ℝ) →
        let J : Euc 2 → ℂ := Complex.orthonormalBasisOneI.repr.symm
        let W : Set (Euc 2) := {y | ((J y).re, (J y).im) ∈
          CorrelatedBM.openSymmetricWedge (Real.sin (θ / 2)) (Real.cos (θ / 2))}
        x ∈ closure W →
        P.real {ω | ∀ s ≤ t, B s ω ∈ W} ≤
          K * (‖x‖ / Real.sqrt (t : ℝ)) ^ q := by
  have hp : 0 < p := lt_trans hq hqp
  let a : ℝ := (p - q) / (2 * p)
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a < 1 := by dsimp [a]; apply (div_lt_one (by positivity)).2; linarith
  have hq1 : q ≤ (1 - a) * p := by
    dsimp [a]
    have hpne : p ≠ 0 := ne_of_gt hp
    field_simp
    linarith
  obtain ⟨n, hn⟩ := exists_nat_ge (q / (2 * a))
  have hq2 : q ≤ 2 * a * n := by
    have h := (div_le_iff₀ (show 0 < 2 * a by positivity)).1 hn
    nlinarith
  obtain ⟨C, c, hC, hc, hsmall⟩ := brownian_wedge_survival_small
  obtain ⟨δ, hδ, hbound⟩ := hsmall n hθ0 hθπ hp hpθ ha ha1 hq1 hq2
  let k : ℝ := (Real.cos (p * (θ / 2)))⁻¹ * (2 : ℝ) ^ p +
    C * ((n.factorial : ℝ) / c ^ n)
  have hcos : 0 < Real.cos (p * (θ / 2)) :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], by nlinarith⟩
  have hk : 0 < k := by dsimp [k]; positivity
  refine ⟨k + (δ ^ q)⁻¹, by positivity, ?_⟩
  intro Ω mΩ P x B hB t ht
  dsimp only
  intro hx
  have := hB.isProbabilityMeasure
  let d : ℝ := ‖x‖ / Real.sqrt (t : ℝ)
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hdp : 0 ≤ d ^ q := Real.rpow_nonneg hd _
  by_cases hd0 : d = 0
  · have hx0 : x = 0 := by
      have hs : 0 < Real.sqrt (t : ℝ) := Real.sqrt_pos.2 ht
      have : ‖x‖ = 0 := by
        have := (div_eq_zero_iff).1 hd0
        rcases this with h | h
        · exact h
        · exact False.elim (hs.ne' h)
      exact norm_eq_zero.mp this
    have hzero : P {ω | ∀ s ≤ t, B s ω ∈ {y : Euc 2 |
        (((Complex.orthonormalBasisOneI.repr.symm y).re),
          ((Complex.orthonormalBasisOneI.repr.symm y).im)) ∈
          CorrelatedBM.openSymmetricWedge (Real.sin (θ / 2)) (Real.cos (θ / 2))}} = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hB.start] with ω hstart hω
      have hw := hω 0 bot_le
      rw [hstart, hx0] at hw
      simp [CorrelatedBM.openSymmetricWedge] at hw
    have hz : P.real {ω | ∀ s ≤ t, B s ω ∈ {y : Euc 2 |
        (((Complex.orthonormalBasisOneI.repr.symm y).re),
          ((Complex.orthonormalBasisOneI.repr.symm y).im)) ∈
          CorrelatedBM.openSymmetricWedge (Real.sin (θ / 2)) (Real.cos (θ / 2))}} = 0 := by
      rw [measureReal_def, hzero, ENNReal.toReal_zero]
    change P.real _ ≤ (k + (δ ^ q)⁻¹) * d ^ q
    rw [hd0, Real.zero_rpow hq.ne', mul_zero]
    exact le_of_eq hz
  · have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
    by_cases hdδ : d < δ
    · have hb := hbound hB t ht hdpos hdδ hx
      change P.real _ ≤ k * d ^ q at hb
      exact le_trans hb (mul_le_mul_of_nonneg_right (by linarith [inv_nonneg.mpr (Real.rpow_nonneg hδ.le q)]) hdp)
    · have hδd : δ ^ q ≤ d ^ q := Real.rpow_le_rpow hδ.le (le_of_not_gt hdδ) hq.le
      have hδp : 0 < δ ^ q := Real.rpow_pos_of_pos hδ _
      have hlarge : 1 ≤ (δ ^ q)⁻¹ * d ^ q := by
        calc
          1 = (δ ^ q)⁻¹ * δ ^ q := (inv_mul_cancel₀ hδp.ne').symm
          _ ≤ (δ ^ q)⁻¹ * d ^ q := mul_le_mul_of_nonneg_left hδd (inv_nonneg.mpr hδp.le)
      calc
        P.real _ ≤ 1 := measureReal_le_one
        _ ≤ (δ ^ q)⁻¹ * d ^ q := hlarge
        _ ≤ (k + (δ ^ q)⁻¹) * d ^ q := by nlinarith [mul_nonneg hk.le hdp]

end LatticeProb
