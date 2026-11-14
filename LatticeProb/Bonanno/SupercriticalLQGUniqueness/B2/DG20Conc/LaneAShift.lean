/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneAShift at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneAAssembly

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Real MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 

theorem laneA_shifted_log_rate {G T : ℝ} (hG : 1 ≤ G)
    (hT : max (3 * G) (G^2) < T) :
    (Real.log T)^2 / (4 * Real.log (Real.log T)) ≤
      (Real.log (T / G))^2 / Real.log (Real.log (T / G)) := by
  have hG0 : 0 < G := by linarith
  have hTG : 3 < T / G := by
    apply (lt_div_iff₀ hG0).2
    exact (le_max_left _ _).trans_lt hT
  have hT0 : 0 < T := by
    have h3G : 3 * G < T := (le_max_left _ _).trans_lt hT
    nlinarith
  have hT2 : G^2 ≤ T := (le_max_right _ _).trans hT.le
  have hdiv : T / G ≤ T := div_le_self hT0.le hG
  have hT3 : 3 < T := lt_of_lt_of_le hTG hdiv
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  have hlogS : 0 < Real.log (T / G) := Real.log_pos (by linarith)
  have hllT : 0 < Real.log (Real.log T) := Real.log_pos (by
    have hlog3 : 1 < Real.log 3 := by
      have h := Real.log_three_gt_d9
      linarith
    exact hlog3.trans (Real.log_lt_log (by norm_num) hT3))
  have hllS : 0 < Real.log (Real.log (T / G)) := by
    apply Real.log_pos
    have hlog3 : 1 < Real.log 3 := by
      have h := Real.log_three_gt_d9
      linarith
    exact hlog3.trans (Real.log_lt_log (by norm_num) hTG)
  have htwog : 2 * Real.log G ≤ Real.log T := by
    have h := Real.log_le_log (by positivity : 0 < G^2) hT2
    rw [Real.log_pow] at h
    simpa only [Nat.cast_ofNat] using h
  have hhalf : Real.log T / 2 ≤ Real.log (T / G) := by
    rw [Real.log_div hT0.ne' hG0.ne']
    linarith
  have hsq : (Real.log T / 2)^2 ≤ (Real.log (T / G))^2 := by
    nlinarith [sq_nonneg (Real.log (T / G) - Real.log T / 2)]
  have hlogle : Real.log (T / G) ≤ Real.log T :=
    Real.log_le_log (div_pos hT0 hG0) hdiv
  have hllle : Real.log (Real.log (T / G)) ≤ Real.log (Real.log T) :=
    Real.log_le_log hlogS hlogle
  calc
    (Real.log T)^2 / (4 * Real.log (Real.log T)) =
        (Real.log T / 2)^2 / Real.log (Real.log T) := by ring
    _ ≤ (Real.log (T / G))^2 / Real.log (Real.log T) :=
      div_le_div_of_nonneg_right hsq hllT.le
    _ ≤ (Real.log (T / G))^2 / Real.log (Real.log (T / G)) :=
      div_le_div_of_nonneg_left (sq_nonneg _) hllS hllle

 

theorem laneA_bounded_log_rate {T B : ℝ} (hT : 3 < T) (hB : T ≤ B) :
    (Real.log T)^2 / Real.log (Real.log T) ≤
      (Real.log B)^2 / Real.log (Real.log 3) := by
  have hlog3 : 1 < Real.log 3 := by
    have h := Real.log_three_gt_d9
    linarith
  have hlogT : 1 < Real.log T :=
    hlog3.trans (Real.log_lt_log (by norm_num) hT)
  have hll3 : 0 < Real.log (Real.log 3) := Real.log_pos hlog3
  have hllT : 0 < Real.log (Real.log T) := Real.log_pos hlogT
  have hlogB : Real.log T ≤ Real.log B := Real.log_le_log (by linarith) hB
  have hsq : (Real.log T)^2 ≤ (Real.log B)^2 := by
    have hlogT0 : 0 ≤ Real.log T := by linarith
    nlinarith
  have hllle : Real.log (Real.log 3) ≤ Real.log (Real.log T) :=
    Real.log_le_log (by linarith)
      (Real.log_le_log (by norm_num) hT.le)
  exact (div_le_div_of_nonneg_right hsq hllT.le).trans
    (div_le_div_of_nonneg_left (sq_nonneg _) hll3 hllle)

 

theorem laneA_rescale_upper_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A : Ω → ℝ≥0∞)
    (L R G C c : ℝ) (hR : 1 ≤ R) (hG : 1 ≤ G) (hC : 0 < C) (hc : 0 < c)
    (hraw : ∀ s : ℝ, 3 < s →
      P {ω | ENNReal.ofReal ((G * R) * (s * L)) < A ω} ≤
        ENNReal.ofReal (G * R) * ENNReal.ofReal
          (C * Real.exp (-c * (Real.log s)^2 / Real.log (Real.log s))))
    (T : ℝ) (hT : 3 < T) :
    let B := max (3 * G) (G^2)
    let M := (Real.log B)^2 / Real.log (Real.log 3)
    let C' := G * C + Real.exp ((c / 4) * M)
    P {ω | ENNReal.ofReal ((T * R) * L) < A ω} ≤
      ENNReal.ofReal (C' * R * Real.exp
        (-(c / 4) * (Real.log T)^2 / Real.log (Real.log T))) := by
  dsimp
  let B : ℝ := max (3 * G) (G^2)
  let M : ℝ := (Real.log B)^2 / Real.log (Real.log 3)
  let C' : ℝ := G * C + Real.exp ((c / 4) * M)
  have hG0 : 0 < G := by linarith
  have hR0 : 0 < R := by linarith
  have hC' : 0 < C' := by dsimp [C']; positivity
  by_cases hbig : B < T
  · have hS : 3 < T / G := by
      apply (lt_div_iff₀ hG0).2
      exact (le_max_left _ _).trans_lt hbig
    have hT0 : 0 < T := by linarith
    have hth : (G * R) * ((T / G) * L) = (T * R) * L := by
      field_simp
    have h := hraw (T / G) hS
    rw [hth] at h
    have hrate := laneA_shifted_log_rate hG hbig
    have he : Real.exp (-c * (Real.log (T / G))^2 /
        Real.log (Real.log (T / G))) ≤
        Real.exp (-(c / 4) * (Real.log T)^2 /
          Real.log (Real.log T)) := by
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_left hrate hc.le
      calc
        -c * (Real.log (T / G))^2 / Real.log (Real.log (T / G)) =
            -(c * ((Real.log (T / G))^2 / Real.log (Real.log (T / G)))) := by ring
        _ ≤ -(c * ((Real.log T)^2 / (4 * Real.log (Real.log T)))) :=
          neg_le_neg hmul
        _ = -(c / 4) * (Real.log T)^2 / Real.log (Real.log T) := by ring
    have hcoef : G * C * Real.exp (-c * (Real.log (T / G))^2 /
        Real.log (Real.log (T / G))) ≤
        C' * Real.exp (-(c / 4) * (Real.log T)^2 /
          Real.log (Real.log T)) := by
      have hGC : 0 ≤ G * C := by positivity
      have hCplus : G * C ≤ C' := by dsimp [C']; linarith [Real.exp_pos ((c / 4) * M)]
      exact (mul_le_mul_of_nonneg_left he hGC).trans
        (mul_le_mul_of_nonneg_right hCplus (Real.exp_pos _).le)
    have hreal : (G * R) *
        (C * Real.exp (-c * (Real.log (T / G))^2 /
          Real.log (Real.log (T / G)))) ≤
        C' * R * Real.exp (-(c / 4) * (Real.log T)^2 /
          Real.log (Real.log T)) := by
      have hm := mul_le_mul_of_nonneg_right hcoef hR0.le
      nlinarith [hm]
    calc
      P {ω | ENNReal.ofReal ((T * R) * L) < A ω} ≤
        ENNReal.ofReal (G * R) * ENNReal.ofReal
          (C * Real.exp (-c * (Real.log (T / G))^2 /
            Real.log (Real.log (T / G)))) := h
      _ = ENNReal.ofReal ((G * R) *
          (C * Real.exp (-c * (Real.log (T / G))^2 /
            Real.log (Real.log (T / G))))) := by
          exact (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal (C' * R * Real.exp
          (-(c / 4) * (Real.log T)^2 / Real.log (Real.log T))) :=
          ENNReal.ofReal_le_ofReal hreal
  · have hTle : T ≤ B := le_of_not_gt hbig
    have hq : (Real.log T)^2 / Real.log (Real.log T) ≤ M :=
      laneA_bounded_log_rate hT hTle
    have hprod : 0 ≤ (c / 4) * (M -
        (Real.log T)^2 / Real.log (Real.log T)) := by
      exact mul_nonneg (by positivity) (sub_nonneg.mpr hq)
    have hexp : 1 ≤ Real.exp ((c / 4) * M) *
        Real.exp (-(c / 4) * (Real.log T)^2 /
          Real.log (Real.log T)) := by
      rw [← Real.exp_add, ← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      convert hprod using 1; ring
    have hreal : 1 ≤ C' * R * Real.exp
        (-(c / 4) * (Real.log T)^2 / Real.log (Real.log T)) := by
      have hRmul : 1 ≤ R * (Real.exp ((c / 4) * M) *
          Real.exp (-(c / 4) * (Real.log T)^2 /
            Real.log (Real.log T))) := by
        calc
          (1 : ℝ) ≤ Real.exp ((c / 4) * M) *
            Real.exp (-(c / 4) * (Real.log T)^2 /
              Real.log (Real.log T)) := hexp
          _ = 1 * (Real.exp ((c / 4) * M) *
            Real.exp (-(c / 4) * (Real.log T)^2 /
              Real.log (Real.log T))) := by ring
          _ ≤ R * (Real.exp ((c / 4) * M) *
            Real.exp (-(c / 4) * (Real.log T)^2 /
              Real.log (Real.log T))) :=
            mul_le_mul_of_nonneg_right hR (by positivity)
      have hCplus : Real.exp ((c / 4) * M) ≤ C' := by
        dsimp [C']
        nlinarith [mul_pos hG0 hC]
      have hm := mul_le_mul_of_nonneg_right hCplus
        (mul_nonneg hR0.le (Real.exp_pos
          (-(c / 4) * (Real.log T)^2 / Real.log (Real.log T))).le)
      nlinarith [hm]
    calc
      P {ω | ENNReal.ofReal ((T * R) * L) < A ω} ≤ 1 := prob_le_one
      _ = ENNReal.ofReal (1 : ℝ) := by norm_num
      _ ≤ ENNReal.ofReal (C' * R * Real.exp
          (-(c / 4) * (Real.log T)^2 / Real.log (Real.log T))) :=
          ENNReal.ofReal_le_ofReal hreal

end SupercriticalLQGUniqueness.B2.DG20Conc
