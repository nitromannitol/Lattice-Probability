/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4RC2Final at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4RC2Cond
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4RIndep
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA3RTransfer
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCCondIndepMoment
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCAroundMeas

 
















set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.WhiteNoise

 
theorem laneA4R_c2_real {K : ℕ} {q ζ ξ Q ζ₁ η l x₀ : ℝ} (hq : 0 < q) (hζ : 0 < ζ)
    (hζ1 : ζ < 1) (hl : 0 < l) (hζη : ζ * (q ^ 2 * ξ ^ 2) ≤ η / 2)
    (hζ₁ : 2 * q * ζ₁ = η / 2) (hx₀ : 0 ≤ x₀)
    (habs : Real.log 2 + q * (2 * ((1 + ζ) / ζ)) * (x₀ + 1) ≤ η * K * Real.log 2) :
    (Real.exp (((K : ℝ) * Real.log 2) * (q * (1 + ζ) * ξ) ^ 2 / 2) ^ (1 / (1 + ζ))) ^ (2 : ℝ) *
      ((((2 : ℝ) ^ (-(1 - ξ * Q + ζ₁) * (K : ℝ)) * l)⁻¹ ^ (q * (2 * ((1 + ζ) / ζ))) *
          (Real.exp (q * (2 * ((1 + ζ) / ζ)) * (x₀ + 1)) + 1)) ^ (2 * ζ / (1 + ζ))) ^
          (1 / 2 : ℝ) *
      ((((2 : ℝ)⁻¹ ^ K * l) ^ (q * (2 * ((1 + ζ) / ζ))) *
          (Real.exp (q * (2 * ((1 + ζ) / ζ)) * (x₀ + 1)) + 1)) ^ (2 * ζ / (1 + ζ))) ^
          (1 / 2 : ℝ) ≤
      ((2 : ℝ) ^ ((q ^ 2 * ξ ^ 2 / 2 - q * ξ * Q + η) * K)) ^ 2 := by
  set τ : ℝ := q * (2 * ((1 + ζ) / ζ)) with hτ
  set γ : ℝ := 2 * ζ / (1 + ζ) with hγ
  set E : ℝ := Real.exp (τ * (x₀ + 1)) with hE
  set c : ℝ := (2 : ℝ) ^ (-(1 - ξ * Q + ζ₁) * (K : ℝ)) * l with hc
  set s : ℝ := (2 : ℝ)⁻¹ ^ K * l with hs
  set g : ℝ := Real.exp (((K : ℝ) * Real.log 2) * (q * (1 + ζ) * ξ) ^ 2 / 2) with hg
  have h1ζ : 0 < 1 + ζ := by linarith
  have hτ0 : 0 < τ := by positivity
  have hγ0 : 0 < γ := by positivity
  have hγ1 : γ ≤ 1 := by rw [hγ, div_le_one h1ζ]; linarith
  have hE1 : 1 ≤ E := Real.one_le_exp (by positivity)
  have hc0 : 0 < c := by positivity
  have hs0 : 0 < s := by positivity
  have hg0 : 0 < g := Real.exp_pos _
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hXR : 0 < c⁻¹ ^ τ * (E + 1) := by positivity
  have hXM : 0 < s ^ τ * (E + 1) := by positivity
  have hLpos : 0 < (g ^ (1 / (1 + ζ))) ^ (2 : ℝ) * ((c⁻¹ ^ τ * (E + 1)) ^ γ) ^ (1 / 2 : ℝ) *
      ((s ^ τ * (E + 1)) ^ γ) ^ (1 / 2 : ℝ) := by positivity
  have hRpos : 0 < ((2 : ℝ) ^ ((q ^ 2 * ξ ^ 2 / 2 - q * ξ * Q + η) * K)) ^ 2 := by positivity
  rw [← Real.log_le_log_iff hLpos hRpos]
  have hlogc : Real.log c = -(1 - ξ * Q + ζ₁) * K * Real.log 2 + Real.log l := by
    rw [hc, Real.log_mul (by positivity) hl.ne', Real.log_rpow (by norm_num)]
  have hlogs : Real.log s = -(K * Real.log 2) + Real.log l := by
    rw [hs, Real.log_mul (by positivity) hl.ne', Real.log_pow, Real.log_inv]; ring
  have hlogE : 0 ≤ Real.log (E + 1) := Real.log_nonneg (by linarith)
  have hlogE2 : Real.log (E + 1) ≤ Real.log 2 + τ * (x₀ + 1) := by
    have : Real.log (E + 1) ≤ Real.log (2 * E) := Real.log_le_log (by linarith) (by linarith)
    rwa [Real.log_mul (by norm_num) (by positivity), hE, Real.log_exp] at this
  have hγE : γ * Real.log (E + 1) ≤ Real.log 2 + τ * (x₀ + 1) :=
    le_trans (mul_le_of_le_one_left hlogE hγ1) hlogE2
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_rpow (by positivity), Real.log_rpow hg0, hg, Real.log_exp,
    Real.log_rpow (by positivity), Real.log_rpow hXR, Real.log_mul (by positivity) (by positivity),
    Real.log_rpow (inv_pos.mpr hc0), Real.log_inv, hlogc,
    Real.log_rpow (by positivity), Real.log_rpow hXM, Real.log_mul (by positivity) (by positivity),
    Real.log_rpow hs0, hlogs, Real.log_pow, Real.log_rpow (by norm_num)]
  have hid1 : (2 : ℝ) * (1 / (1 + ζ) * ((K : ℝ) * Real.log 2 * (q * (1 + ζ) * ξ) ^ 2 / 2)) =
      (1 + ζ) * (q ^ 2 * ξ ^ 2) * (K * Real.log 2) := by
    field_simp
  have hid2 : γ * τ = 4 * q := by
    rw [hγ, hτ]; field_simp; ring
  rw [hid1]
  have hA : ζ * (q ^ 2 * ξ ^ 2) * (K * Real.log 2) ≤ η / 2 * (K * Real.log 2) :=
    mul_le_mul_of_nonneg_right hζη (by positivity)
  have hB : 2 * q * ζ₁ * (K * Real.log 2) = η / 2 * (K * Real.log 2) := by rw [hζ₁]
  calc _ = (1 + ζ) * (q ^ 2 * ξ ^ 2) * (K * Real.log 2) +
        γ * τ / 2 * ((ζ₁ - ξ * Q) * (K * Real.log 2)) + γ * Real.log (E + 1) := by ring
    _ = (1 + ζ) * (q ^ 2 * ξ ^ 2) * (K * Real.log 2) +
        2 * q * ((ζ₁ - ξ * Q) * (K * Real.log 2)) + γ * Real.log (E + 1) := by
        rw [hid2]; ring
    _ ≤ _ := by
        push_cast
        linarith [hA, hB, hγE, habs]

 
theorem laneA4R_c2_absorb {τ η : ℝ} (hτ : 0 < τ) (hη : 0 < η) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K →
      Real.log 2 + τ * ((K : ℝ) ^ (2 / 3 : ℝ) + 1) ≤ η * K * Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set a : ℝ := η * Real.log 2 with ha
  have ha0 : 0 < a := by positivity
  obtain ⟨K₁, hK₁⟩ := laneA3R_eventually_log_le (2 * τ / a) (1 / 3) (by norm_num)
  obtain ⟨K₂, hK₂⟩ := laneA3R_eventually_log_le (2 * (τ + Real.log 2) / a) 1 one_pos
  refine ⟨max 1 (max K₁ K₂), fun K hK => ?_⟩
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast le_trans (le_max_left _ _) hK
  have hK0 : (0 : ℝ) < K := by linarith
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK1
  have h1 := hK₁ K (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hK)
  have h2 := hK₂ K (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hK)
  rw [Real.rpow_one] at h2
  have hm1 : 0 ≤ 2 * τ / a := by positivity
  have hm2 : 0 ≤ 2 * (τ + Real.log 2) / a := by positivity
  have i1 : 2 * τ / a ≤ (K : ℝ) ^ (1 / 3 : ℝ) := le_trans (le_mul_of_one_le_right hm1
    (by linarith)) h1
  have i2 : 2 * (τ + Real.log 2) / a ≤ K := le_trans (le_mul_of_one_le_right hm2
    (by linarith)) h2
  have hsplit : (K : ℝ) ^ (2 / 3 : ℝ) * (K : ℝ) ^ (1 / 3 : ℝ) = K := by
    rw [← Real.rpow_add hK0]; norm_num
  have hp : 0 ≤ (K : ℝ) ^ (2 / 3 : ℝ) := by positivity
  have j1 : τ * (K : ℝ) ^ (2 / 3 : ℝ) ≤ a / 2 * K := by
    have := mul_le_mul_of_nonneg_left i1 hp
    rw [hsplit] at this
    have e : τ * (K : ℝ) ^ (2 / 3 : ℝ) = a / 2 * ((K : ℝ) ^ (2 / 3 : ℝ) * (2 * τ / a)) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have j2 : τ + Real.log 2 ≤ a / 2 * K := by
    have e : τ + Real.log 2 = a / 2 * (2 * (τ + Real.log 2) / a) := by field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left i2 (by positivity)
  have : η * K * Real.log 2 = a * K := by rw [ha]; ring
  rw [this]
  nlinarith [j1, j2]

theorem laneA4R_rpow_half_le_of_le_sq {x : ℝ≥0∞} {c : ℝ} (hc : 0 ≤ c)
    (h : x ≤ ENNReal.ofReal (c ^ 2)) : x ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal c := by
  calc x ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (c ^ 2) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow h (by norm_num)
    _ = ENNReal.ofReal c := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.rpow_natCast,
          ← Real.rpow_mul hc]
        norm_num

 
theorem laneC2StarAt_proved.{u} : LaneC2StarAt.{u} := by
  intro Qψ hε ξ Q _hQ p₀ hp₀ hp₀2 hJ hB3 C q η hC hq hη
  have hξ : (0 : ℝ) < (ξ : ℝ) := ξ.2
  set ξr : ℝ := (ξ : ℝ) with hξr
  
  set ζ : ℝ := min (1 / 2) (η / (2 * (q ^ 2 * ξr ^ 2 + 1))) with hζdef
  have hζ0 : 0 < ζ := lt_min (by norm_num) (by positivity)
  have hζ1 : ζ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hζη : ζ * (q ^ 2 * ξr ^ 2) ≤ η / 2 := by
    have hle : ζ ≤ η / (2 * (q ^ 2 * ξr ^ 2 + 1)) := min_le_right _ _
    have hpos : 0 < 2 * (q ^ 2 * ξr ^ 2 + 1) := by positivity
    calc ζ * (q ^ 2 * ξr ^ 2) ≤ η / (2 * (q ^ 2 * ξr ^ 2 + 1)) * (q ^ 2 * ξr ^ 2) :=
          mul_le_mul_of_nonneg_right hle (by positivity)
      _ ≤ η / 2 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ hpos (by norm_num)]
          nlinarith [sq_nonneg (q * ξr)]
  set ζ₁ : ℝ := η / (4 * q) with hζ₁def
  have hζ₁0 : 0 < ζ₁ := by positivity
  have hζ₁ : 2 * q * ζ₁ = η / 2 := by rw [hζ₁def]; field_simp; ring
  set τ : ℝ := q * (2 * ((1 + ζ) / ζ)) with hτdef
  have hτ0 : 0 < τ := by positivity
  
  obtain ⟨C₀, c₀, KJ, hC₀, hc₀, hJr⟩ := j1FixedPAt_roundCut Qψ ξr p₀ hJ C hC.le
  obtain ⟨KB, cB₀, cB₁, hcB₀, hcB₁, hB3t⟩ := hB3 ζ₁ C hζ₁0 hC
  obtain ⟨KR1, _, hR1⟩ := laneA4R_rate_pow hC₀ hc₀ Qψ.ε₀_pos hε hτ0
  obtain ⟨KR2, _, hR2⟩ := laneA4R_rate_pow hcB₀ hcB₁ Qψ.ε₀_pos hε hτ0
  obtain ⟨KF, hKF⟩ := laneA4R_c2_absorb hτ0 hη
  refine ⟨max (max KJ KB) (max (max KR1 KR2) KF), ?_⟩
  intro Ω _ _ P _ W hW n K hK hKn hΛ
  have hKJ : KJ ≤ K := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hK
  have hKB : KB ≤ K := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hK
  have hKR1 : KR1 ≤ K :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hK
  have hKR2 : KR2 ≤ K :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hK
  have hKF' : KF ≤ K := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hK
  set lam : ℝ := lambdaN ξr W P (n - K) with hlam
  have hlam0 : 0 < lam := lambdaN_pos hW (n - K)
  set x₀ : ℝ := (K : ℝ) ^ (2 / 3 : ℝ) with hx₀
  have hx₀0 : 0 ≤ x₀ := by positivity
  set I := laneSourceIdx Qψ K with hI
  
  have hψ := isPsiVersion_psiMN (Q := Qψ) hW (Nat.zero_le n)
  have hphi := isPhiVersion_phiMN (W := W) (P := P) hW (Nat.zero_le K)
  set L : Ω → ℝ := lenObs ξr (psiMN Qψ W P 0 n) (rectAB 1 1) with hLdef
  have hLm : Measurable L := measurable_lenObs hψ.cont hψ.meas _
  have hL0 : ∀ x, 0 < L x := fun x =>
    lenObs_pos hψ.cont _ (by norm_num [rectAB]) (by norm_num [rectAB])
      (by norm_num [MarkedRect.crossWidth, rectAB]) x
  set Φ : ℤ × ℤ → Ω → ℝ := fun b => phiMN W P 0 K (T20.dyCenter K b) with hΦ
  have hΦm : ∀ b, Measurable (Φ b) := fun b => hphi.meas _
  set R : Ω → ℝ≥0∞ := fun x => ENNReal.ofReal (L x)⁻¹ with hR
  have hRm : Measurable R := ENNReal.measurable_ofReal.comp hLm.inv
  set E : ℤ × ℤ → Ω → ℝ≥0∞ := fun b x => ENNReal.ofReal (Real.exp (ξr * Φ b x)) with hEdef
  have hEm : ∀ b, Measurable (E b) := fun b =>
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul (hΦm b)))
  set D : ℤ × ℤ → Ω → ℝ≥0∞ := fun b x => laneA3Around P W hW Qψ ξr n K b x with hDdef
  set U : ℤ × ℤ → Ω → ℝ≥0∞ := fun b x =>
    ENNReal.ofReal (Real.exp (-ξr * Φ b x)) * D b x with hUdef
  have hUm : ∀ b, AEMeasurable (U b) P := fun b =>
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul (hΦm b)))).aemeasurable.mul
      (laneC_aemeasurable_psi_aroundDist P W hW Qψ ξr n K (laneBCoarseIndex Qψ K) b)
  have hDU : ∀ b ∈ I, ∀ x, D b x ≤ E b x * U b x := by
    intro b _ x
    refine le_of_eq ?_
    rw [hUdef, hEdef]
    simp only
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
      show ξr * Φ b x + -ξr * Φ b x = 0 by ring, Real.exp_zero, ENNReal.ofReal_one, one_mul]
  
  have hFkm : Measurable fun ω (x : ℂ) => psiMN Qψ W P K n x ω :=
    measurable_pi_iff.mpr (isPsiVersion_psiMN (Q := Qψ) hW hKn).meas
  have hXm : Measurable (laneA3RStarMap Qψ W P K n) :=
    hFkm.prodMk (measurable_pi_iff.mpr fun c =>
      measurable_pi_iff.mpr (T20B.blkKn_spec hW Qψ hKn c.1).2.1)
  have hstar : laneFineStar Qψ W P K n ≤ (inferInstance : MeasurableSpace Ω) := by
    rw [laneFineStar_eq_comap]; exact hXm.comap_le
  have hIndAll := laneFineStar_indep_coarse_proved P W hW Qψ K n hKn
  set G : ℝ≥0∞ := ENNReal.ofReal
    (Real.exp (((K : ℝ) * Real.log 2) * (q * (1 + ζ) * ξr) ^ 2 / 2)) with hGdef
  have hG : ∀ b ∈ I, ∀ᵐ ω ∂P,
      ∫⁻ x, E b x ^ (q * (1 + ζ)) ∂(condExpKernel P (laneFineStar Qψ W P K n) ω) ≤ G := by
    intro b _
    have hInd : Indep (MeasurableSpace.comap (phiMN W P 0 K (T20.dyCenter K b))
        (inferInstance : MeasurableSpace ℝ)) (laneFineStar Qψ W P K n) P := by
      refine indep_of_indep_of_le_left hIndAll (le_trans ?_ le_sup_left)
      exact ((measurable_pi_apply (T20.dyCenter K b)).comp
        (comap_measurable (fun ω (x : ℂ) => phiMN W P 0 K x ω))).comap_le
    have h := laneC_conditional_coarse_phi_exp_moment_of_indep P hW hstar K b
      (q * (1 + ζ) * ξr) hInd
    filter_upwards [h] with ω hω
    refine le_trans (le_of_eq ?_) hω
    refine lintegral_congr fun x => ?_
    rw [hEdef]
    simp only
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by positivity), ← Real.exp_mul]
    congr 2
    ring
  
  have hcond := laneA4R_cond_max_sq_le P hstar I hRm hEm hUm hDU hq hζ0 hζ1 hG
  
  set aR : ℝ := ((2 : ℝ) ^ (-(1 - ξr * Q + ζ₁) * (K : ℝ)) * lam)⁻¹ ^ τ *
    (Real.exp (τ * (x₀ + 1)) + 1) with haR
  set aM : ℝ := ((2 : ℝ)⁻¹ ^ K * lam) ^ τ * (Real.exp (τ * (x₀ + 1)) + 1) with haM
  have hmomR : ∫⁻ x, R x ^ τ ∂P ≤ ENNReal.ofReal aR := by
    refine laneA4R_recip_moment hLm hL0 hτ0 (by positivity) hx₀0
      (rate := fun v => cB₀ * (5 : ℝ) ^ K *
        Real.exp (-(cB₁ * v ^ 2 / ((K : ℝ) ^ (3 * Qψ.ε₀) * Real.log v)))) ?_ ?_
    · intro v hv
      have hT := (hR2 K hKR2 v hv).1
      have h := (hB3t P W hW n K hKB hKn hΛ (Real.exp v) hT).1
      rw [Real.log_exp] at h
      refine le_trans (measure_mono ?_) h
      intro ω hω
      have hω' : L ω < (Real.exp v)⁻¹ *
          ((2 : ℝ) ^ (-(1 - ξr * Q + ζ₁) * (K : ℝ)) * lam) := hω
      show L ω < (Real.exp v)⁻¹ * (2 : ℝ) ^ (-(1 - ξr * Q + ζ₁) * (K : ℝ)) * lam
      rwa [mul_assoc]
    · intro v hv
      exact (hR2 K hKR2 v hv).2
  have hmomM : ∫⁻ x, (I.sup fun b => U b x) ^ τ ∂P ≤ ENNReal.ofReal aM := by
    refine laneA4R_sup_moment I hUm hτ0 (by positivity) hx₀0
      (rate := fun v => C₀ * (5 : ℝ) ^ K *
        Real.exp (-(c₀ * v ^ 2 / ((K : ℝ) ^ (3 * Qψ.ε₀) * Real.log v)))) ?_ ?_
    · intro v hv
      have hT := (hR1 K hKR1 v hv).1
      have h := (hJr P W hW K n hKJ hKn hΛ (Real.exp v) hT).2
      rw [Real.log_exp, neg_mul, neg_div] at h
      exact le_trans (measure_mono fun ω hω => hω) h
    · intro v hv
      exact (hR1 K hKR1 v hv).2
  
  have habs := hKF K hKF'
  have hreal := laneA4R_c2_real (K := K) (ξ := ξr) (Q := Q) hq hζ0 hζ1 hlam0 hζη hζ₁ hx₀0
    (by simpa [hτdef] using habs)
  have hfinal : ∫⁻ ω, ((laneSourceIdx Qψ K).sup (fun b =>
      laneCNormalizedAroundProductStar P W hW Qψ ξr q n K b ω)) ^ (2 : ℝ) ∂P ≤
      ENNReal.ofReal (((2 : ℝ) ^ ((q ^ 2 * ξr ^ 2 / 2 - q * ξr * Q + η) * K)) ^ 2) := by
    refine le_trans hcond ?_
    have hτr : q * (2 * ((1 + ζ) / ζ)) = τ := rfl
    rw [hτr]
    calc (G ^ (1 / (1 + ζ))) ^ (2 : ℝ) *
          ((∫⁻ x, R x ^ τ ∂P) ^ (2 * ζ / (1 + ζ))) ^ (1 / 2 : ℝ) *
          ((∫⁻ x, (I.sup fun b => U b x) ^ τ ∂P) ^ (2 * ζ / (1 + ζ))) ^ (1 / 2 : ℝ)
        ≤ (G ^ (1 / (1 + ζ))) ^ (2 : ℝ) *
          ((ENNReal.ofReal aR) ^ (2 * ζ / (1 + ζ))) ^ (1 / 2 : ℝ) *
          ((ENNReal.ofReal aM) ^ (2 * ζ / (1 + ζ))) ^ (1 / 2 : ℝ) := by
          gcongr
      _ = ENNReal.ofReal
          ((Real.exp (((K : ℝ) * Real.log 2) * (q * (1 + ζ) * ξr) ^ 2 / 2) ^ (1 / (1 + ζ))) ^
            (2 : ℝ) * (aR ^ (2 * ζ / (1 + ζ))) ^ (1 / 2 : ℝ) *
            (aM ^ (2 * ζ / (1 + ζ))) ^ (1 / 2 : ℝ)) := by
          have h1ζ : 0 < 1 + ζ := by linarith
          have haR0 : 0 ≤ aR := by positivity
          have haM0 : 0 ≤ aM := by positivity
          rw [hGdef, ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by positivity),
            ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
            ENNReal.ofReal_rpow_of_nonneg haR0 (by positivity),
            ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
            ENNReal.ofReal_rpow_of_nonneg haM0 (by positivity),
            ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ _ := ENNReal.ofReal_le_ofReal hreal
  exact laneA4R_rpow_half_le_of_le_sq (by positivity) hfinal

end SupercriticalLQGUniqueness.B2.DG20Conc
