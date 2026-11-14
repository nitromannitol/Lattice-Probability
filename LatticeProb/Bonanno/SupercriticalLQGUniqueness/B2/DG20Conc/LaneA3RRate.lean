/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA3RRate at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds

 








set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Real

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 
theorem laneA3R_eventually_log_le (M a : ℝ) (ha : 0 < a) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → M * (Real.log K + 1) ≤ (K : ℝ) ^ a := by
  have hM : 0 < |M| + 1 := by positivity
  have h1 : ∀ᶠ x : ℝ in atTop, Real.log x ≤ (1 / (2 * (|M| + 1))) * x ^ a := by
    have := (isLittleO_log_rpow_atTop ha).bound (by positivity : (0 : ℝ) < 1 / (2 * (|M| + 1)))
    filter_upwards [this, eventually_ge_atTop 1] with x hx hx1
    have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hp : 0 ≤ x ^ a := Real.rpow_nonneg (by linarith) _
    rwa [Real.norm_of_nonneg hl, Real.norm_of_nonneg hp] at hx
  have h2 : ∀ᶠ x : ℝ in atTop, 2 * (|M| + 1) ≤ x ^ a :=
    (tendsto_rpow_atTop ha).eventually_ge_atTop _
  have h3 := (h1.and (h2.and (eventually_ge_atTop (1 : ℝ))))
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp (tendsto_natCast_atTop_atTop.eventually h3)
  refine ⟨K₀, fun K hK => ?_⟩
  obtain ⟨hl, hp, hK1⟩ := hK₀ K hK
  have hlog : 0 ≤ Real.log K := Real.log_nonneg hK1
  have hb : (|M| + 1) * Real.log K ≤ (K : ℝ) ^ a / 2 := by
    have := mul_le_mul_of_nonneg_left hl hM.le
    rw [show (|M| + 1) * (1 / (2 * (|M| + 1)) * (K : ℝ) ^ a) = (K : ℝ) ^ a / 2 by
      field_simp] at this
    exact this
  calc M * (Real.log K + 1) ≤ (|M| + 1) * (Real.log K + 1) :=
        mul_le_mul_of_nonneg_right (by linarith [le_abs_self M]) (by linarith)
    _ = (|M| + 1) * Real.log K + (|M| + 1) := by ring
    _ ≤ (K : ℝ) ^ a / 2 + (K : ℝ) ^ a / 2 := by linarith
    _ = (K : ℝ) ^ a := by ring

theorem laneA3R_one_lt_log_three : 1 < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

theorem laneA3R_log_five_lt_two : Real.log 5 < 2 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h := Real.exp_one_gt_d9
  have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  nlinarith

 
theorem laneA3R_tail_rate {C₀ c₀ ε : ℝ} (hC₀ : 0 < C₀) (hc₀ : 0 < c₀) (hε0 : 0 < ε)
    (hε : ε < 1 / 100) :
    ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ K : ℕ, K₀ ≤ K → ∀ t : ℝ, (K : ℝ) ^ (2 / 3 : ℝ) < t →
      (2 : ℝ) ^ ((K : ℝ) ^ ((1 / 2 : ℝ) + 3 * ε)) < Real.exp (t / 4) ∧
      2 * Real.exp (2 * t) *
        (C₀ * (5 : ℝ) ^ K * Real.exp (-c₀ * (t / 4) ^ 2 / (K : ℝ) ^ (3 * ε)) +
          C₀ * (5 : ℝ) ^ K * Real.exp (-c₀ * (t / 4) ^ 2 /
            ((K : ℝ) ^ (3 * ε) * Real.log (t / 4)))) ≤ Real.exp (-t) := by
  obtain ⟨K₁, hK₁⟩ := laneA3R_eventually_log_le 12 (2 / 3) (by norm_num)
  obtain ⟨K₂, hK₂⟩ := laneA3R_eventually_log_le (4 * Real.log 2) (1 / 6 - 3 * ε) (by linarith)
  obtain ⟨K₃, hK₃⟩ := laneA3R_eventually_log_le (192 / c₀) (2 / 3 - 3 * ε) (by linarith)
  obtain ⟨K₄, hK₄⟩ := laneA3R_eventually_log_le (64 * (|Real.log (4 * C₀)| + 2) / c₀)
    (1 / 3 - 3 * ε) (by linarith)
  refine ⟨max 1 (max (max K₁ K₂) (max K₃ K₄)), le_max_left _ _, ?_⟩
  intro K hK t ht
  have hKa : K₁ ≤ K ∧ K₂ ≤ K ∧ K₃ ≤ K ∧ K₄ ≤ K := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
  have hK0 : (0 : ℝ) < K := by linarith
  set L := Real.log K with hL
  have hL0 : 0 ≤ L := Real.log_nonneg hK1
  set x₀ := (K : ℝ) ^ (2 / 3 : ℝ) with hx₀
  have hx₀pos : 0 < x₀ := Real.rpow_pos_of_pos hK0 _
  have hx₀12 : 12 ≤ x₀ := by
    have := hK₁ K hKa.1; nlinarith
  have ht0 : 0 < t := by linarith
  have hs3 : 3 < t / 4 := by linarith
  have hlogs : 1 < Real.log (t / 4) :=
    laneA3R_one_lt_log_three.trans (Real.log_lt_log (by norm_num) hs3)
  constructor
  · 
    have hsplit : x₀ = (K : ℝ) ^ (1 / 6 - 3 * ε) * (K : ℝ) ^ ((1 / 2 : ℝ) + 3 * ε) := by
      rw [hx₀, ← Real.rpow_add hK0]; congr 1; ring
    have h2 := hK₂ K hKa.2.1
    have hle : 4 * Real.log 2 ≤ (K : ℝ) ^ (1 / 6 - 3 * ε) := by
      have : 4 * Real.log 2 ≤ 4 * Real.log 2 * (L + 1) :=
        le_mul_of_one_le_right (by positivity) (by linarith)
      linarith
    have hp : 0 < (K : ℝ) ^ ((1 / 2 : ℝ) + 3 * ε) := Real.rpow_pos_of_pos hK0 _
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply Real.exp_lt_exp.mpr
    have : 4 * Real.log 2 * (K : ℝ) ^ ((1 / 2 : ℝ) + 3 * ε) ≤ x₀ := by
      rw [hsplit]; exact mul_le_mul_of_nonneg_right hle hp.le
    nlinarith
  · 
    set e₃ := (K : ℝ) ^ (3 * ε) with he₃
    have he₃pos : 0 < e₃ := Real.rpow_pos_of_pos hK0 _
    set c := c₀ / (16 * e₃) with hc
    have hcpos : 0 < c := by positivity
    
    have hcx : 12 * (L + 1) ≤ c * x₀ := by
      have h3 := hK₃ K hKa.2.2.1
      have e : c * x₀ = c₀ / 16 * (K : ℝ) ^ (2 / 3 - 3 * ε) := by
        rw [hc, he₃, hx₀, Real.rpow_sub hK0]; field_simp
      rw [e]
      have : 192 / c₀ * (L + 1) * (c₀ / 16) = 12 * (L + 1) := by field_simp; ring
      nlinarith
    set D := |Real.log (4 * C₀)| + 2 * K with hD
    have hD0 : 0 ≤ D := by positivity
    have hcxx : D * (L + 1) ≤ c / 4 * x₀ ^ 2 := by
      have h4 := hK₄ K hKa.2.2.2
      have e : c / 4 * x₀ ^ 2 = c₀ / 64 * K * (K : ℝ) ^ (1 / 3 - 3 * ε) := by
        rw [hc, he₃, hx₀, Real.rpow_sub hK0, ← Real.rpow_natCast,
          ← Real.rpow_mul hK0.le]
        have : (2 / 3 : ℝ) * ((2 : ℕ) : ℝ) = 1 + 1 / 3 := by norm_num
        rw [this, Real.rpow_add hK0, Real.rpow_one]
        field_simp
        norm_num
      rw [e]
      have hDle : D ≤ (|Real.log (4 * C₀)| + 2) * K := by
        rw [hD]; nlinarith [abs_nonneg (Real.log (4 * C₀))]
      have hk : (|Real.log (4 * C₀)| + 2) * (L + 1) ≤ c₀ / 64 * (K : ℝ) ^ (1 / 3 - 3 * ε) := by
        have : 64 * (|Real.log (4 * C₀)| + 2) / c₀ * (L + 1) * (c₀ / 64) =
            (|Real.log (4 * C₀)| + 2) * (L + 1) := by field_simp
        nlinarith
      calc D * (L + 1) ≤ (|Real.log (4 * C₀)| + 2) * K * (L + 1) :=
            mul_le_mul_of_nonneg_right hDle (by linarith)
        _ = K * ((|Real.log (4 * C₀)| + 2) * (L + 1)) := by ring
        _ ≤ K * (c₀ / 64 * (K : ℝ) ^ (1 / 3 - 3 * ε)) := mul_le_mul_of_nonneg_left hk hK0.le
        _ = c₀ / 64 * K * (K : ℝ) ^ (1 / 3 - 3 * ε) := by ring
    
    have hlogt : Real.log (t / 4) ≤ 2 / 3 * L + t / x₀ := by
      have h1 : Real.log (t / 4) ≤ Real.log t := Real.log_le_log (by linarith) (by linarith)
      have h2 : Real.log (t / x₀) ≤ t / x₀ - 1 := Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_div ht0.ne' hx₀pos.ne', hx₀, Real.log_rpow hK0] at h2
      rw [← hL] at h2
      linarith
    
    have hkey : (Real.log (4 * C₀) + K * Real.log 5 + 3 * t) * Real.log (t / 4) ≤ c * t ^ 2 := by
      have hA : Real.log (4 * C₀) + K * Real.log 5 + 3 * t ≤ D + 3 * t := by
        have := le_abs_self (Real.log (4 * C₀))
        have : (K : ℝ) * Real.log 5 ≤ 2 * K := by
          nlinarith [laneA3R_log_five_lt_two]
        rw [hD]; linarith
      have hlpos : 0 < Real.log (t / 4) := by linarith
      have htx : x₀ ≤ t := ht.le
      have hdiv : t / x₀ * x₀ = t := div_mul_cancel₀ t hx₀pos.ne'
      calc (Real.log (4 * C₀) + K * Real.log 5 + 3 * t) * Real.log (t / 4)
          ≤ (D + 3 * t) * Real.log (t / 4) :=
            mul_le_mul_of_nonneg_right hA hlpos.le
        _ ≤ (D + 3 * t) * (2 / 3 * L + t / x₀) :=
            mul_le_mul_of_nonneg_left hlogt (by linarith)
        _ = D * (2 / 3 * L) + D * (t / x₀) + 2 * t * L + 3 * t * (t / x₀) := by ring
        _ ≤ c / 4 * t ^ 2 + c / 4 * t ^ 2 + c / 4 * t ^ 2 + c / 4 * t ^ 2 := by
            have hxt2 : x₀ ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hx₀pos.le htx 2
            have hc4 : 0 ≤ c / 4 := by positivity
            have hD' : D ≤ c / 4 * x₀ ^ 2 :=
              le_trans (le_mul_of_one_le_right hD0 (by linarith)) hcxx
            have hxdiv : x₀ * (t / x₀) = t := mul_div_cancel₀ t hx₀pos.ne'
            have i1 : D * (2 / 3 * L) ≤ c / 4 * t ^ 2 :=
              calc D * (2 / 3 * L) ≤ D * (L + 1) := mul_le_mul_of_nonneg_left (by linarith) hD0
                _ ≤ c / 4 * x₀ ^ 2 := hcxx
                _ ≤ c / 4 * t ^ 2 := mul_le_mul_of_nonneg_left hxt2 hc4
            have i2 : D * (t / x₀) ≤ c / 4 * t ^ 2 :=
              calc D * (t / x₀) ≤ c / 4 * x₀ ^ 2 * (t / x₀) :=
                    mul_le_mul_of_nonneg_right hD' (by positivity)
                _ = c / 4 * x₀ * (x₀ * (t / x₀)) := by ring
                _ = c / 4 * x₀ * t := by rw [hxdiv]
                _ ≤ c / 4 * t * t :=
                    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htx hc4) ht0.le
                _ = c / 4 * t ^ 2 := by ring
            have i3 : 2 * t * L ≤ c / 4 * t ^ 2 := by
              have h8 : 8 * L ≤ c * t :=
                calc 8 * L ≤ 12 * (L + 1) := by linarith
                  _ ≤ c * x₀ := hcx
                  _ ≤ c * t := mul_le_mul_of_nonneg_left htx hcpos.le
              calc 2 * t * L = t / 4 * (8 * L) := by ring
                _ ≤ t / 4 * (c * t) := mul_le_mul_of_nonneg_left h8 (by positivity)
                _ = c / 4 * t ^ 2 := by ring
            have i4 : 3 * t * (t / x₀) ≤ c / 4 * t ^ 2 := by
              have h12 : 12 ≤ c * x₀ := le_trans (by linarith) hcx
              have h3 : 3 / x₀ ≤ c / 4 := by
                rw [div_le_iff₀ hx₀pos]; linarith
              calc 3 * t * (t / x₀) = 3 / x₀ * t ^ 2 := by ring
                _ ≤ c / 4 * t ^ 2 := mul_le_mul_of_nonneg_right h3 (sq_nonneg t)
            linarith
        _ = c * t ^ 2 := by ring
    
    have hlpos : 0 < Real.log (t / 4) := by linarith
    have hl0 : Real.log (t / 4) ≠ 0 := hlpos.ne'
    have he0 : e₃ ≠ 0 := he₃pos.ne'
    have hexp1 : Real.exp (-c₀ * (t / 4) ^ 2 / e₃) ≤
        Real.exp (-c₀ * (t / 4) ^ 2 / (e₃ * Real.log (t / 4))) := by
      have hq : 0 ≤ c₀ * (t / 4) ^ 2 / e₃ := by positivity
      have h1 : c₀ * (t / 4) ^ 2 / e₃ / Real.log (t / 4) ≤ c₀ * (t / 4) ^ 2 / e₃ :=
        div_le_self hq hlogs.le
      have e1 : -c₀ * (t / 4) ^ 2 / (e₃ * Real.log (t / 4)) =
          -(c₀ * (t / 4) ^ 2 / e₃ / Real.log (t / 4)) := by
        rw [div_div]; ring
      have e2 : -c₀ * (t / 4) ^ 2 / e₃ = -(c₀ * (t / 4) ^ 2 / e₃) := by ring
      rw [e1, e2]
      exact Real.exp_le_exp.mpr (by linarith)
    have hrate : -c₀ * (t / 4) ^ 2 / (e₃ * Real.log (t / 4)) =
        -(c * t ^ 2 / Real.log (t / 4)) := by
      rw [hc]
      field_simp
      ring
    have h5 : (5 : ℝ) ^ K = Real.exp (K * Real.log 5) := by
      rw [← Real.log_pow, Real.exp_log (by positivity)]
    calc 2 * Real.exp (2 * t) *
          (C₀ * (5 : ℝ) ^ K * Real.exp (-c₀ * (t / 4) ^ 2 / e₃) +
            C₀ * (5 : ℝ) ^ K * Real.exp (-c₀ * (t / 4) ^ 2 / (e₃ * Real.log (t / 4))))
        ≤ 2 * Real.exp (2 * t) * (2 * (C₀ * (5 : ℝ) ^ K *
            Real.exp (-c₀ * (t / 4) ^ 2 / (e₃ * Real.log (t / 4))))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have : C₀ * (5 : ℝ) ^ K * Real.exp (-c₀ * (t / 4) ^ 2 / e₃) ≤
              C₀ * (5 : ℝ) ^ K * Real.exp (-c₀ * (t / 4) ^ 2 / (e₃ * Real.log (t / 4))) :=
            mul_le_mul_of_nonneg_left hexp1 (by positivity)
          linarith
      _ = Real.exp (Real.log (4 * C₀) + K * Real.log 5 + 2 * t +
            -(c * t ^ 2 / Real.log (t / 4))) := by
          rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log (by positivity), ← h5,
            ← hrate]
          ring
      _ ≤ Real.exp (-t) := by
          apply Real.exp_le_exp.mpr
          have : (Real.log (4 * C₀) + K * Real.log 5 + 3 * t) ≤ c * t ^ 2 / Real.log (t / 4) := by
            rw [le_div_iff₀ hlpos]; exact hkey
          linarith

end SupercriticalLQGUniqueness.B2.DG20Conc
