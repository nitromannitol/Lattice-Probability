/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J3PercEstimate at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J3RectTails
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J3UpperScaled

 









set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

 
theorem j3_up_rate {cu y L : ℝ} (hcu : 0 ≤ cu) (hL : 0 < L) (hy : 2 * L + 2 ≤ y) :
    Real.exp (-cu * (y - L) ^ 2 / Real.log (y - L)) ≤
      Real.exp (-(cu / 4) * y ^ 2 / Real.log y) := by
  refine Real.exp_le_exp.mpr ?_
  have hs2 : 2 < y - L := by linarith
  have hsy : y - L ≤ y := by linarith
  have hshalf : y / 2 ≤ y - L := by linarith
  have hls : 0 < Real.log (y - L) := Real.log_pos (by linarith)
  have hly : Real.log (y - L) ≤ Real.log y := Real.log_le_log (by linarith) hsy
  have hsq : (y / 2) ^ 2 ≤ (y - L) ^ 2 := pow_le_pow_left₀ (by linarith) hshalf 2
  have hnum : cu / 4 * y ^ 2 ≤ cu * (y - L) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hsq hcu
    have e : cu * (y / 2) ^ 2 = cu / 4 * y ^ 2 := by ring
    linarith
  have h1 : cu / 4 * y ^ 2 / Real.log y ≤ cu * (y - L) ^ 2 / Real.log (y - L) :=
    div_le_div₀ (by positivity) hnum hls hly
  have e1 : -cu * (y - L) ^ 2 / Real.log (y - L) = -(cu * (y - L) ^ 2 / Real.log (y - L)) := by
    ring
  have e2 : -(cu / 4) * y ^ 2 / Real.log y = -(cu / 4 * y ^ 2 / Real.log y) := by ring
  linarith

 
theorem j3_percEstimate_of_quantileRatioAllP (hJ2 : J2Defs.QuantileRatioAllP) :
    Iface.DG20PercEstimate' := by
  classical
  intro ξ U K₁ K₂ hK₁ hK₂ hc₁ hc₂ hnt₁ hnt₂ hs₁ hs₂ hdisj hUc
  have hξ : (0 : ℝ) < ξ := ξ.2
  obtain ⟨Kl, F, hlow⟩ := j3_lower_geometry hK₁ hK₂ hnt₁.nonempty hdisj
  obtain ⟨cl, Cl, hcl, hCl, hRl⟩ := j3_mrectLen_tails hJ2 ξ Kl one_pos (by norm_num : (0 : ℝ) < 3)
  obtain ⟨Ku, S, hup⟩ := j3_upper_geometry U.isOpen hUc hc₁ hc₂ hnt₁ hnt₂ hs₁ hs₂
  obtain ⟨cu, Cu, hcu, hCu, hRu⟩ := j3_mrectLen_tails hJ2 ξ Ku (by norm_num : (0 : ℝ) < 3) one_pos
  set Nu : ℝ := (2 * S.card + 1) * 8 with hNu
  have hNu1 : 8 ≤ Nu := by
    have : (1 : ℝ) ≤ 2 * S.card + 1 := by have := Nat.cast_nonneg (α := ℝ) S.card; linarith
    nlinarith
  have hNu0 : 0 < Nu := by linarith
  set L : ℝ := Real.log Nu with hL
  have hL0 : 0 < L := Real.log_pos (by linarith)
  have hll3 : 0 < Real.log (Real.log 3) :=
    Real.log_pos (by rw [Real.lt_log_iff_exp_lt (by norm_num)]; have := Real.exp_one_lt_d9; linarith)
  set Bu : ℝ := Real.exp (cu / 4 * (2 * L + 2) ^ 2 / Real.log (Real.log 3)) with hBu
  have hBu0 : 0 < Bu := by rw [hBu]; exact Real.exp_pos _
  have hA1 : 0 ≤ (F.card : ℝ) * Cl := mul_nonneg (Nat.cast_nonneg _) hCl.le
  have hA2 : 0 < Real.exp (4 * cl) := Real.exp_pos _
  have hA3 : 0 ≤ 4 * (S.card : ℝ) * Cu :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hCu.le
  set c₁ : ℝ := min cl (cu / 4) with hc₁def
  have hc₁ : 0 < c₁ := lt_min hcl (by linarith)
  set c₀ : ℝ := F.card * Cl + Real.exp (4 * cl) + 4 * S.card * Cu + Bu with hc₀def
  have hc₀ : 0 < c₀ := by rw [hc₀def]; linarith
  refine ⟨c₀, c₁, hc₀, hc₁, ?_⟩
  intro Ω _ P _ W hW n T hT
  have hφ := isPhiVersion_phiMN hW (Nat.zero_le n)
  have hlam : 0 < lambdaN (ξ : ℝ) W P n := lambdaN_pos hW n
  have hTpos : 0 < T := by linarith
  set y : ℝ := Real.log T with hy
  have hylog3 : Real.log 3 < y := Real.log_lt_log (by norm_num) hT
  have hy1 : 1 < y := by
    have : 1 < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]; have := Real.exp_one_lt_d9; linarith
    linarith
  have hly : 0 < Real.log y := Real.log_pos hy1
  have hlly : Real.log (Real.log 3) ≤ Real.log y :=
    Real.log_le_log (Real.log_pos (by norm_num)) hylog3.le
  have hTy : T = Real.exp y := (Real.exp_log hTpos).symm
  constructor
  · 
    by_cases hy2 : y ≤ 2
    · refine (prob_le_one).trans ?_
      rw [← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      have hy4 : y ^ 2 ≤ 4 := by nlinarith
      have h1 : 1 ≤ Real.exp (4 * cl) * Real.exp (-c₁ * y ^ 2) := by
        rw [← Real.exp_add, ← Real.exp_zero]
        refine Real.exp_le_exp.mpr ?_
        have : c₁ * y ^ 2 ≤ cl * 4 := mul_le_mul (min_le_left _ _) hy4 (sq_nonneg _) hcl.le
        linarith
      have h2 : Real.exp (4 * cl) ≤ c₀ := by
        rw [hc₀def]; linarith
      calc (1 : ℝ) ≤ Real.exp (4 * cl) * Real.exp (-c₁ * y ^ 2) := h1
        _ ≤ c₀ * Real.exp (-c₁ * y ^ 2) := mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    · push_neg at hy2
      have hsub : {ω | crossLenIn (ξ : ℝ) (fun z => phiMN W P 0 n z ω) U K₁ K₂ <
          ENNReal.ofReal (T⁻¹ * lambdaN (ξ : ℝ) W P n)} ⊆
          ⋃ j ∈ F, {ω | T20B.mrectLen (ξ : ℝ) (fun x => phiMN W P 0 n x ω) Kl j.1 j.2 1 3 ≤
            Real.exp (-y) * lambdaN (ξ : ℝ) W P n} := by
        intro ω hω
        obtain ⟨j, hj, hlt⟩ := hlow (ξ : ℝ) (fun z => phiMN W P 0 n z ω) U _ hω
        refine mem_biUnion hj ?_
        simp only [mem_setOf_eq]
        rw [Real.exp_neg, hy, Real.exp_log hTpos]
        exact hlt.le
      refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
      have hterm : ∀ j ∈ F, P {ω | T20B.mrectLen (ξ : ℝ) (fun x => phiMN W P 0 n x ω) Kl j.1 j.2
          1 3 ≤ Real.exp (-y) * lambdaN (ξ : ℝ) W P n} ≤
          ENNReal.ofReal (Cl * Real.exp (-cl * y ^ 2)) := fun j _ =>
        (hRl P W hW n j.1 j.2 y hy2).2
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      have he : Real.exp (-cl * y ^ 2) ≤ Real.exp (-c₁ * y ^ 2) :=
        Real.exp_le_exp.mpr (by nlinarith [min_le_left cl (cu / 4), sq_nonneg y])
      have h2 : (F.card : ℝ) * Cl ≤ c₀ := by
        rw [hc₀def]; linarith
      calc (F.card : ℝ) * (Cl * Real.exp (-cl * y ^ 2))
          = (F.card * Cl) * Real.exp (-cl * y ^ 2) := by ring
        _ ≤ c₀ * Real.exp (-c₁ * y ^ 2) :=
            mul_le_mul h2 he (Real.exp_pos _).le hc₀.le
  · 
    have hyl : 0 < Real.log y := hly
    by_cases hyS : y ≤ 2 * L + 2
    · refine (prob_le_one).trans ?_
      rw [← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      have hq : y ^ 2 / Real.log y ≤ (2 * L + 2) ^ 2 / Real.log (Real.log 3) :=
        div_le_div₀ (by positivity) (pow_le_pow_left₀ (by linarith) hyS 2) hll3 hlly
      have h1 : 1 ≤ Bu * Real.exp (-c₁ * y ^ 2 / Real.log y) := by
        rw [hBu, ← Real.exp_add, ← Real.exp_zero]
        refine Real.exp_le_exp.mpr ?_
        have hc : c₁ ≤ cu / 4 := min_le_right _ _
        have h3 : c₁ * (y ^ 2 / Real.log y) ≤ cu / 4 * ((2 * L + 2) ^ 2 / Real.log (Real.log 3)) :=
          mul_le_mul hc hq (by positivity) (by positivity)
        have e1 : -c₁ * y ^ 2 / Real.log y = -(c₁ * (y ^ 2 / Real.log y)) := by ring
        have e2 : cu / 4 * (2 * L + 2) ^ 2 / Real.log (Real.log 3) =
            cu / 4 * ((2 * L + 2) ^ 2 / Real.log (Real.log 3)) := by ring
        linarith
      have h2 : Bu ≤ c₀ := by
        rw [hc₀def]; linarith
      calc (1 : ℝ) ≤ Bu * Real.exp (-c₁ * y ^ 2 / Real.log y) := h1
        _ ≤ c₀ * Real.exp (-c₁ * y ^ 2 / Real.log y) :=
            mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    · push_neg at hyS
      set t : ℝ := T * lambdaN (ξ : ℝ) W P n / Nu with ht
      have ht0 : 0 < t := div_pos (mul_pos hTpos hlam) hNu0
      set s : ℝ := y - L with hs
      have hs2 : 2 < s := by linarith
      have hest : Real.exp s * lambdaN (ξ : ℝ) W P n = t := by
        rw [hs, Real.exp_sub, hy, Real.exp_log hTpos, hL, Real.exp_log hNu0, ht]; ring
      have hsub : {ω | ENNReal.ofReal (T * lambdaN (ξ : ℝ) W P n) <
          crossLenIn (ξ : ℝ) (fun z => phiMN W P 0 n z ω) U K₁ K₂} ⊆
          ⋃ b ∈ S, ⋃ i ∈ (Finset.univ : Finset (Fin 4)),
            {ω | Real.exp s * lambdaN (ξ : ℝ) W P n ≤
              T20B.mrectLen (ξ : ℝ) (fun x => phiMN W P 0 n x ω) Ku (S6U.siteJ Ku b i).1
                (S6U.siteJ Ku b i).2 3 1} := by
        intro ω hω
        by_contra hnot
        simp only [mem_iUnion, mem_setOf_eq, not_exists, not_le, Finset.mem_univ,
          exists_true_left] at hnot
        have hall : ∀ b ∈ S, ∀ i : Fin 4, T20B.mrectLen (ξ : ℝ) (fun x => phiMN W P 0 n x ω) Ku
            (S6U.siteJ Ku b i).1 (S6U.siteJ Ku b i).2 3 1 ≤ t := by
          intro b hb i
          rw [← hest]; exact (hnot b hb i).le
        have hle := hup (ξ : ℝ) (fun z => phiMN W P 0 n z ω) (hφ.cont ω) t ht0 hall
        have e : (2 * (S.card : ℝ) + 1) * 8 * t = T * lambdaN (ξ : ℝ) W P n := by
          rw [ht, ← hNu]; field_simp
        rw [e] at hle
        exact absurd hω (not_lt.mpr hle)
      refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
      have hterm : ∀ b ∈ S, P (⋃ i ∈ (Finset.univ : Finset (Fin 4)),
          {ω | Real.exp s * lambdaN (ξ : ℝ) W P n ≤
            T20B.mrectLen (ξ : ℝ) (fun x => phiMN W P 0 n x ω) Ku (S6U.siteJ Ku b i).1
              (S6U.siteJ Ku b i).2 3 1}) ≤
          4 * ENNReal.ofReal (Cu * Real.exp (-cu * s ^ 2 / Real.log s)) := by
        intro b _
        refine (measure_biUnion_finset_le _ _).trans ?_
        refine (Finset.sum_le_sum fun i _ => (hRu P W hW n _ _ s hs2).1).trans ?_
        simp
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul, show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num,
        ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hrate := j3_up_rate (cu := cu) hcu.le hL0 hyS.le
      have he : Real.exp (-(cu / 4) * y ^ 2 / Real.log y) ≤ Real.exp (-c₁ * y ^ 2 / Real.log y) := by
        refine Real.exp_le_exp.mpr ?_
        have hc : c₁ ≤ cu / 4 := min_le_right _ _
        have h3 : c₁ * y ^ 2 / Real.log y ≤ cu / 4 * y ^ 2 / Real.log y :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc (sq_nonneg y)) hly.le
        have e1 : -c₁ * y ^ 2 / Real.log y = -(c₁ * y ^ 2 / Real.log y) := by ring
        have e2 : -(cu / 4) * y ^ 2 / Real.log y = -(cu / 4 * y ^ 2 / Real.log y) := by ring
        linarith
      have h2 : 4 * S.card * Cu ≤ c₀ := by
        rw [hc₀def]; linarith
      calc (S.card : ℝ) * (4 * (Cu * Real.exp (-cu * s ^ 2 / Real.log s)))
          = (4 * S.card * Cu) * Real.exp (-cu * s ^ 2 / Real.log s) := by ring
        _ ≤ c₀ * Real.exp (-c₁ * y ^ 2 / Real.log y) :=
            mul_le_mul h2 (hrate.trans he) (Real.exp_pos _).le hc₀.le

end SupercriticalLQGUniqueness.B2.DG20Conc
