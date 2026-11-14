/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneB3Arith at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

 







set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

private theorem pos_of_mul_pos_or_nonneg {a b : ℝ} (ha : 0 < a) (h : 0 ≤ a * b) : 0 ≤ b := by
  by_contra hb
  push_neg at hb
  have : a * b < 0 := mul_neg_of_pos_of_neg ha hb
  linarith

 

theorem laneB3_sqrt_absorb (C ζ : ℝ) (hC : 0 ≤ C) (hζ : 0 < ζ) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K →
      Real.exp (C * Real.sqrt (K : ℝ)) ≤ (2 : ℝ) ^ ((ζ / 2) * (K : ℝ)) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set a : ℝ := 2 * C / (ζ * Real.log 2) with ha
  have ha0 : 0 ≤ a := by positivity
  obtain ⟨K₀, hK₀⟩ := exists_nat_ge (a ^ 2)
  refine ⟨K₀, fun K hK => ?_⟩
  have hKr : a ^ 2 ≤ (K : ℝ) := hK₀.trans (by exact_mod_cast hK)
  have hsq : a ≤ Real.sqrt (K : ℝ) := by
    rw [show a = Real.sqrt (a ^ 2) by rw [Real.sqrt_sq ha0]]
    exact Real.sqrt_le_sqrt hKr
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hs0 : 0 ≤ Real.sqrt (K : ℝ) := Real.sqrt_nonneg _
  have hss : Real.sqrt (K : ℝ) * Real.sqrt (K : ℝ) = K := Real.mul_self_sqrt hK0
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply Real.exp_le_exp.mpr
  
  have hCa : C = a * (ζ * Real.log 2) / 2 := by
    rw [ha]; field_simp
  have h1 : C * Real.sqrt K ≤ (ζ * Real.log 2) / 2 * (Real.sqrt K * Real.sqrt K) := by
    rw [hCa]
    have hpos : 0 ≤ ζ * Real.log 2 / 2 := by positivity
    calc a * (ζ * Real.log 2) / 2 * Real.sqrt K
        = (ζ * Real.log 2 / 2) * (a * Real.sqrt K) := by ring
      _ ≤ (ζ * Real.log 2 / 2) * (Real.sqrt K * Real.sqrt K) := by
          apply mul_le_mul_of_nonneg_left _ hpos
          exact mul_le_mul_of_nonneg_right hsq hs0
  rw [hss] at h1
  calc C * Real.sqrt K ≤ (ζ * Real.log 2) / 2 * K := h1
    _ = Real.log 2 * (ζ / 2 * K) := by ring

 
theorem laneB3_lower_arith {C₁ O y m Lk Ln ell lam g B : ℝ} (K : ℕ)
    (hC₁ : 0 < C₁) (hO : O < y / (4 * C₁))
    (hm : Real.exp (-(y / 4)) * ell * (2 : ℝ)⁻¹ ^ K ≤ m)
    (hLk : Real.exp (-(y / 4)) * (B * g) ≤ Lk)
    (hpath : Real.exp (-(C₁ * O)) * ((2 : ℝ) ^ K * m) * Lk ≤ C₁ * Ln)
    (hlam : lam ≤ B * ell) (hB : 0 < B) (hg : 0 ≤ g) (hell : 0 ≤ ell)
    (hlam0 : 0 ≤ lam) (hC₁y : C₁ ≤ Real.exp (y / 4)) :
    Real.exp (-y) * g * lam ≤ Ln := by
  have hq : (2 : ℝ) ^ K * (2 : ℝ)⁻¹ ^ K = 1 := by rw [← mul_pow]; norm_num
  have he : Real.exp (-(y / 4)) ≤ Real.exp (-(C₁ * O)) := by
    apply Real.exp_le_exp.mpr
    have : C₁ * O < y / 4 := by
      have := mul_lt_mul_of_pos_left hO hC₁
      calc C₁ * O < C₁ * (y / (4 * C₁)) := this
        _ = y / 4 := by field_simp
    linarith
  have hE0 : 0 < Real.exp (-(y / 4)) := Real.exp_pos _
  have hm0 : 0 ≤ Real.exp (-(y / 4)) * ell * (2 : ℝ)⁻¹ ^ K := by positivity
  have hLk0 : 0 ≤ Real.exp (-(y / 4)) * (B * g) := by positivity
  have hstep : Real.exp (-(y / 4)) * ((2 : ℝ) ^ K *
      (Real.exp (-(y / 4)) * ell * (2 : ℝ)⁻¹ ^ K)) *
      (Real.exp (-(y / 4)) * (B * g)) ≤ C₁ * Ln := by
    refine le_trans ?_ hpath
    have hmnn : 0 ≤ m := hm0.trans hm
    have h2K : (0 : ℝ) ≤ 2 ^ K := by positivity
    apply mul_le_mul _ hLk hLk0 (by positivity)
    exact mul_le_mul he (mul_le_mul_of_nonneg_left hm h2K) (by positivity) (Real.exp_pos _).le
  have hid : Real.exp (-(y / 4)) * ((2 : ℝ) ^ K *
      (Real.exp (-(y / 4)) * ell * (2 : ℝ)⁻¹ ^ K)) *
      (Real.exp (-(y / 4)) * (B * g)) =
      (Real.exp (-(y / 4)) * Real.exp (-(y / 4)) * Real.exp (-(y / 4))) *
        ((B * ell) * g) * ((2 : ℝ) ^ K * (2 : ℝ)⁻¹ ^ K) := by ring
  rw [hid, hq, mul_one] at hstep
  have he3 : Real.exp (-(y / 4)) * Real.exp (-(y / 4)) * Real.exp (-(y / 4)) =
      Real.exp (-(3 * y / 4)) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  rw [he3] at hstep
  have hlg : lam * g ≤ (B * ell) * g := mul_le_mul_of_nonneg_right hlam hg
  have h2 : Real.exp (-(3 * y / 4)) * (lam * g) ≤ C₁ * Ln :=
    le_trans (mul_le_mul_of_nonneg_left hlg (Real.exp_pos _).le) hstep
  have hsplit : Real.exp (-y) = Real.exp (-(y / 4)) * Real.exp (-(3 * y / 4)) := by
    rw [← Real.exp_add]; ring_nf
  have hinv : Real.exp (-(y / 4)) * C₁ ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hC₁y hE0.le
    rwa [← Real.exp_add, neg_add_cancel, Real.exp_zero] at this
  have hLn0 : 0 ≤ Ln := by
    have h0 : 0 ≤ Real.exp (-(3 * y / 4)) * (lam * g) := by positivity
    have h1 : 0 ≤ C₁ * Ln := h0.trans h2
    exact (pos_of_mul_pos_or_nonneg hC₁ h1)
  calc Real.exp (-y) * g * lam
      = Real.exp (-(y / 4)) * (Real.exp (-(3 * y / 4)) * (lam * g)) := by
        rw [hsplit]; ring
    _ ≤ Real.exp (-(y / 4)) * (C₁ * Ln) := mul_le_mul_of_nonneg_left h2 hE0.le
    _ = (Real.exp (-(y / 4)) * C₁) * Ln := by ring
    _ ≤ Ln := mul_le_of_le_one_left hLn0 hinv

 
theorem laneB3_upper_arith {C₁ O y SV Lk Ln M LamEll lam g g' B : ℝ} (K : ℕ)
    (hC₁ : 0 < C₁) (hO : O < y / (4 * C₁))
    (hpath : Ln ≤ SV * (C₁ * M))
    (hSV : SV ≤ C₁ * (2 : ℝ) ^ K * Real.exp (C₁ * O) * Lk)
    (hM0 : 0 ≤ M) (hM : M ≤ Real.exp (y / 4) * LamEll * (2 : ℝ)⁻¹ ^ K)
    (hLk0 : 0 ≤ Lk) (hLk : Lk ≤ Real.exp (y / 4) * g')
    (hLamEll : LamEll ≤ B * lam) (hBg : B * g' ≤ g) (hg' : 0 ≤ g') (hlam : 0 ≤ lam)
    (hC₁y : C₁ ^ 2 ≤ Real.exp (y / 4)) :
    Ln ≤ Real.exp y * g * lam := by
  have hq : (2 : ℝ) ^ K * (2 : ℝ)⁻¹ ^ K = 1 := by rw [← mul_pow]; norm_num
  have he : Real.exp (C₁ * O) ≤ Real.exp (y / 4) := by
    apply Real.exp_le_exp.mpr
    have := mul_lt_mul_of_pos_left hO hC₁
    have h' : C₁ * (y / (4 * C₁)) = y / 4 := by field_simp
    linarith
  have hE0 : 0 < Real.exp (y / 4) := Real.exp_pos _
  have hCM : 0 ≤ C₁ * M := mul_nonneg hC₁.le hM0
  have hLE0 : 0 ≤ LamEll := by
    have : 0 ≤ Real.exp (y / 4) * LamEll * (2 : ℝ)⁻¹ ^ K := hM0.trans hM
    have hpos : 0 < Real.exp (y / 4) * (2 : ℝ)⁻¹ ^ K := by positivity
    nlinarith
  calc Ln ≤ SV * (C₁ * M) := hpath
    _ ≤ (C₁ * (2 : ℝ) ^ K * Real.exp (C₁ * O) * Lk) * (C₁ * M) :=
        mul_le_mul_of_nonneg_right hSV hCM
    _ ≤ (C₁ * (2 : ℝ) ^ K * Real.exp (y / 4) * (Real.exp (y / 4) * g')) *
          (C₁ * (Real.exp (y / 4) * LamEll * (2 : ℝ)⁻¹ ^ K)) := by
        gcongr
    _ = C₁ ^ 2 * (Real.exp (y / 4) * Real.exp (y / 4) * Real.exp (y / 4)) *
          (g' * LamEll) * ((2 : ℝ) ^ K * (2 : ℝ)⁻¹ ^ K) := by ring
    _ ≤ Real.exp (y / 4) * (Real.exp (y / 4) * Real.exp (y / 4) * Real.exp (y / 4)) *
          (g' * (B * lam)) * 1 := by
        rw [hq]
        gcongr
    _ = Real.exp y * ((B * g') * lam) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; ring_nf
    _ ≤ Real.exp y * (g * lam) := by gcongr
    _ = Real.exp y * g * lam := by ring

end SupercriticalLQGUniqueness.B2.DG20Conc
