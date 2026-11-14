/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.B4ExponentRelation at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J2Defs
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBX0Window
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBSqrtAbsorb
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneALaw
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P26Final

 
















set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

 

theorem b4_lambdaN_eq {Ω Ω₂ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₂]
    {P : Measure Ω} {P₂ : Measure Ω₂} {W : WNSpace → Ω → ℝ} {V : WNSpace → Ω₂ → ℝ}
    (hW : IsWhiteNoise P W) (hV : IsWhiteNoise P₂ V) (ξ : ℝ) (m : ℕ) :
    lambdaN ξ W P m = lambdaN ξ V P₂ m := by
  unfold lambdaN lenN lenMN
  rw [laneA_law_lenObs_eq hW hV ξ m (rectAB 1 1)]

 

theorem b4_eq5_76_of_tight {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {ξ : ℝ} (hξ : 0 < ξ)
    (hΛ : ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ →
      ∃ B : ℝ, ∀ n, LambdaN ξ W P n (ENNReal.ofReal p) ≤ B) :
    S6Eq5_76 ξ W P :=
  s6Eq5_76_of_halves hW (s6_eq5_76_low hW hξ hΛ (s6_eq5_75 hW hξ))
    (s6_eq5_76_up hW hξ hΛ (s6_eq6_98_of_Lambda hW hξ hΛ)
      (s6Step1Circ_of_glue hW hξ (s6_step1_glue ξ)))

 
theorem b4_arith_mul {ln lm lk c C' A C76 sk gL gU t D : ℝ} (hlm : 0 < lm) (hlk : 0 < lk)
    (hc : 0 < c) (hA : 0 < A) (ht : 0 < t) (hgL : 0 ≤ gL) (hgU : 0 ≤ gU) (hsk : 0 ≤ sk)
    (hL : Real.exp (-(C76 * sk)) * lm * lk ≤ ln) (hU : ln ≤ Real.exp (C76 * sk) * lm * lk)
    (hXL : c * gL ≤ lk) (hXU : lk ≤ C' * gU) (habs : Real.exp (|C76| * sk) ≤ A * t)
    (hDA : A / c ≤ D) (hDB : A * C' ≤ D) (hD : 0 < D) :
    D⁻¹ * (gL * t⁻¹) * lm ≤ ln ∧ ln ≤ D * (gU * t) * lm := by
  have hE : 0 < Real.exp (|C76| * sk) := Real.exp_pos _
  have hAt : 0 < A * t := mul_pos hA ht
  refine ⟨?_, ?_⟩
  · have h1 : (A * t)⁻¹ ≤ Real.exp (-(C76 * sk)) := by
      have h2 : (A * t)⁻¹ ≤ (Real.exp (|C76| * sk))⁻¹ := inv_anti₀ hE habs
      have h3 : (Real.exp (|C76| * sk))⁻¹ ≤ Real.exp (-(C76 * sk)) := by
        rw [← Real.exp_neg]
        exact Real.exp_le_exp.mpr (by
          have := mul_le_mul_of_nonneg_right (le_abs_self C76) hsk; linarith)
      exact h2.trans h3
    have hDinv : D⁻¹ ≤ c / A := by
      rw [show c / A = (A / c)⁻¹ by rw [inv_div]]
      exact inv_anti₀ (by positivity) hDA
    calc D⁻¹ * (gL * t⁻¹) * lm ≤ c / A * (gL * t⁻¹) * lm := by gcongr
      _ = (A * t)⁻¹ * lm * (c * gL) := by field_simp
      _ ≤ Real.exp (-(C76 * sk)) * lm * lk := by gcongr
      _ ≤ ln := hL
  · have h1 : Real.exp (C76 * sk) ≤ A * t :=
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_abs_self C76) hsk)).trans habs
    calc ln ≤ Real.exp (C76 * sk) * lm * lk := hU
      _ ≤ (A * t) * lm * (C' * gU) := by gcongr
      _ = (A * C') * (gU * t) * lm := by ring
      _ ≤ D * (gU * t) * lm := by gcongr

 
theorem b4_arith_base {ln l0 c C' gL gU t D : ℝ} (hc : 0 < c) (ht1 : 1 ≤ t)
    (hgL : 0 ≤ gL) (hgU : 0 ≤ gU) (hXL : c * gL ≤ ln) (hXU : ln ≤ C' * gU)
    (h0L : c ≤ l0) (h0U : l0 ≤ C') (hDC : C' / c ≤ D) (hD : 0 < D) :
    D⁻¹ * (gL * t⁻¹) * l0 ≤ ln ∧ ln ≤ D * (gU * t) * l0 := by
  have hC' : 0 < C' := lt_of_lt_of_le hc (h0L.trans h0U)
  have ht : 0 < t := lt_of_lt_of_le one_pos ht1
  have hti : t⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht1
  have hl0 : 0 ≤ l0 := hc.le.trans h0L
  refine ⟨?_, ?_⟩
  · have hDinv : D⁻¹ ≤ c / C' := by
      rw [show c / C' = (C' / c)⁻¹ by rw [inv_div]]
      exact inv_anti₀ (by positivity) hDC
    have hgt : gL * t⁻¹ ≤ gL := mul_le_of_le_one_right hgL hti
    have hgt0 : 0 ≤ gL * t⁻¹ := mul_nonneg hgL (inv_nonneg.mpr ht.le)
    have h1 : D⁻¹ * (gL * t⁻¹) ≤ c / C' * gL :=
      mul_le_mul hDinv hgt hgt0 (div_nonneg hc.le hC'.le)
    have h2 : D⁻¹ * (gL * t⁻¹) * l0 ≤ c / C' * gL * C' :=
      mul_le_mul h1 h0U hl0 (mul_nonneg (div_nonneg hc.le hC'.le) hgL)
    have h3 : c / C' * gL * C' = c * gL := by field_simp
    linarith
  · have h1 : C' * gU = C' / c * c * gU := by field_simp
    have h2 : C' / c * c ≤ D * l0 :=
      mul_le_mul hDC h0L hc.le hD.le
    have h3 : gU ≤ gU * t := le_mul_of_one_le_right hgU ht1
    have h4 : C' / c * c * gU ≤ D * l0 * (gU * t) :=
      mul_le_mul h2 h3 hgU (mul_nonneg hD.le hl0)
    have h5 : D * l0 * (gU * t) = D * (gU * t) * l0 := by ring
    linarith

 
theorem b4_exponentRelation_of_quantileRatioAllP (hJ2 : J2Defs.QuantileRatioAllP) :
    Iface.DG20ExponentRelation := by
  intro ξ Q hQ ζ hζ
  have hξ : (0 : ℝ) < ξ := ξ.2
  obtain ⟨W₀, hW₀⟩ := exists_isWhiteNoise
  let P₀ := LQGDimension.ExistAsm.stdP
  have hΛ : ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ →
      ∃ B : ℝ, ∀ n, LambdaN (ξ : ℝ) W₀ P₀ n (ENNReal.ofReal p) ≤ B := by
    refine ⟨1 / 4, by norm_num, fun p hp hp4 => ?_⟩
    obtain ⟨B, hB⟩ := hJ2 ξ p hp (by linarith)
    exact ⟨B, hB P₀ W₀ hW₀⟩
  obtain ⟨C76, h76⟩ := b4_eq5_76_of_tight hW₀ hξ hΛ
  obtain ⟨c, C', hc, hC', hwin⟩ := laneB_whiteNoise_median_window ξ Q hQ (ζ / 2) (by linarith)
  obtain ⟨A, hA, habs⟩ := laneB_exp_sqrt_le_dyadic_power |C76| (ζ / 2) (by linarith)
  refine ⟨1 + A / c + A * C' + C' / c, by positivity, ?_⟩
  intro Ω _ P _ W hW n k hkn
  have hD0 : 0 < 1 + A / c + A * C' + C' / c := by positivity
  have hlam : ∀ m : ℕ, lambdaN (ξ : ℝ) W P m = lambdaN (ξ : ℝ) W₀ P₀ m :=
    fun m => b4_lambdaN_eq hW hW₀ (ξ : ℝ) m
  have hpos : ∀ m : ℕ, 0 < lambdaN (ξ : ℝ) W P m := fun m => lambdaN_pos hW m
  have hsplitL : (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ζ) * (k : ℝ)) =
      (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ζ / 2) * (k : ℝ)) * ((2 : ℝ) ^ (ζ / 2 * (k : ℝ)))⁻¹ := by
    rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_add (by norm_num)]
    congr 1; ring
  have hsplitU : (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ζ) * (k : ℝ)) =
      (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ζ / 2) * (k : ℝ)) * (2 : ℝ) ^ (ζ / 2 * (k : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1; ring
  have h2ge : 1 ≤ (2 : ℝ) ^ (ζ / 2 * (k : ℝ)) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have hgL : 0 ≤ (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ζ / 2) * (k : ℝ)) := by positivity
  have hgU : 0 ≤ (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ζ / 2) * (k : ℝ)) := by positivity
  rw [hsplitL, hsplitU]
  obtain hk0 | hk1 := Nat.eq_zero_or_pos k
  · 
    subst hk0
    have hln := hpos n
    simp only [Nat.cast_zero, mul_zero, Real.rpow_zero, mul_one, Nat.sub_zero, inv_one]
    have hD1 : 1 ≤ 1 + A / c + A * C' + C' / c := by
      have : 0 ≤ A / c + A * C' + C' / c := by positivity
      linarith
    have hDi : (1 + A / c + A * C' + C' / c)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hD1
    constructor <;> nlinarith
  · obtain hnk0 | hnk1 := Nat.eq_zero_or_pos (n - k)
    · 
      have hnk : n = k := by omega
      subst hnk
      rw [hnk0]
      obtain ⟨hlo0, hhi0⟩ := hwin P W hW 0
      obtain ⟨hlon, hhin⟩ := hwin P W hW n
      simp only [Nat.cast_zero, mul_zero, Real.rpow_zero, mul_one] at hlo0 hhi0
      exact b4_arith_base hc h2ge hgL hgU hlon hhin hlo0 hhi0
        (by have : 0 ≤ 1 + A / c + A * C' := by positivity
            linarith) hD0
    · 
      obtain ⟨m, rfl⟩ : ∃ m, n = m + k := ⟨n - k, by omega⟩
      have hm : 1 ≤ m := by simp only [Nat.add_sub_cancel] at hnk1; omega
      simp only [Nat.add_sub_cancel]
      obtain ⟨hL, hU⟩ := h76 m k hm hk1
      rw [← hlam m, ← hlam k, ← hlam (m + k)] at hL hU
      obtain ⟨hlok, hhik⟩ := hwin P W hW k
      exact b4_arith_mul (hpos m) (hpos k) hc hA (by positivity) hgL hgU
        (Real.sqrt_nonneg _) hL hU hlok hhik (habs k)
        (by have : 0 ≤ A * C' + C' / c := by positivity
            linarith)
        (by have : 0 ≤ A / c + C' / c := by positivity
            linarith) hD0

end SupercriticalLQGUniqueness.B2.DG20Conc
