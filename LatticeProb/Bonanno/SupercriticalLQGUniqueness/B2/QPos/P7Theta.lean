/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P7Theta at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P7Kernel
import LatticeProb.Bonanno.LQGMetric.Field.HeatKernelSquareTheta

 













set_option autoImplicit false
noncomputable section

open Real Finset
open LQGMetric LQGMetric.HeatSq

namespace SupercriticalLQGUniqueness.B2.QPos.P7

 
abbrev idk (s u v : ℝ) : ℝ := intervalDirKernel (-1) 2 s u v

 
def theta (N : ℕ) (s : ℝ) (j : ℤ) : ℝ :=
  ∑' m : ℤ, Real.exp (-(π ^ 2 / 8) * s * ((j : ℝ) + 4 * N * m) ^ 2)

lemma summable_exp_cos {α : ℝ} (hα : 0 < α) (f : ℤ → ℝ) (hf : ∀ k, |f k| ≤ 2) :
    Summable (fun k : ℤ => Real.exp (-α * k ^ 2) * f k) := by
  refine Summable.of_norm_bounded ((summable_exp_neg_mul_int_sq' hα).mul_left 2) fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have := hf k
  have h0 := (Real.exp_pos (-α * k ^ 2)).le
  calc Real.exp (-α * k ^ 2) * |f k| ≤ Real.exp (-α * k ^ 2) * 2 :=
        mul_le_mul_of_nonneg_left this h0
    _ = 2 * Real.exp (-α * k ^ 2) := by ring

 
lemma idk_eq_cos {s : ℝ} (hs : 0 < s) (u v : ℝ) :
    idk s u v = (1 / 4) * ∑' k : ℤ, Real.exp (-(π ^ 2 / 8) * s * k ^ 2) *
      (Real.cos (π * k * (u - v) / 2) - Real.cos (π * k * (u + v + 2) / 2)) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  unfold idk intervalDirKernel
  rw [Summable.tsum_sub (summable_gauss1_shift hs h2 (u - v))
    (summable_gauss1_shift hs h2 (u + v - 2 * (-1))), tsum_gauss1_shift_eq_cos hs h2,
    tsum_gauss1_shift_eq_cos hs h2]
  have hc : π ^ 2 / (2 * 2 ^ 2) = π ^ 2 / 8 := by norm_num
  have hα : 0 < π ^ 2 / 8 * s := by positivity
  have hS1 : Summable (fun k : ℤ => Real.exp (-(π ^ 2 / 8) * s * k ^ 2) *
      Real.cos (π * k * (u - v) / 2)) :=
    (summable_exp_cos hα (fun k : ℤ => Real.cos (π * k * (u - v) / 2))
      (fun k => (Real.abs_cos_le_one _).trans (by norm_num))).congr fun k => by ring_nf
  have hS2 : Summable (fun k : ℤ => Real.exp (-(π ^ 2 / 8) * s * k ^ 2) *
      Real.cos (π * k * (u + v - 2 * (-1)) / 2)) :=
    (summable_exp_cos hα (fun k : ℤ => Real.cos (π * k * (u + v - 2 * (-1)) / 2))
      (fun k => (Real.abs_cos_le_one _).trans (by norm_num))).congr fun k => by ring_nf
  rw [hc, show ((2 : ℝ) * 2)⁻¹ = 1 / 4 by norm_num, ← mul_sub, ← Summable.tsum_sub hS1 hS2]
  congr 1
  refine tsum_congr fun k => ?_
  rw [show u + v - 2 * (-1) = u + v + 2 by ring]
  ring

 
theorem idk_lattice (N : ℕ) (hN : 0 < N) {s : ℝ} (hs : 0 < s) (c a : ℤ) :
    idk s (c / N) (a / N) =
      (1 / 2) * ∑' k : ℤ, Real.exp (-(π ^ 2 / 8) * s * k ^ 2) * (dsin N k c * dsin N k a) := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [idk_eq_cos hs]
  have e : ∀ k : ℤ, Real.cos (π * k * ((c : ℝ) / N - a / N) / 2) -
      Real.cos (π * k * ((c : ℝ) / N + a / N + 2) / 2) = 2 * (dsin N k c * dsin N k a) := by
    intro k
    unfold dsin
    have hA : π * k * ((c : ℝ) / N - a / N) / 2 =
        k * π * (c + N) / (2 * N) - k * π * (a + N) / (2 * N) := by field_simp; ring
    have hB : π * k * ((c : ℝ) / N + a / N + 2) / 2 =
        k * π * (c + N) / (2 * N) + k * π * (a + N) / (2 * N) := by field_simp; ring
    rw [hA, hB, Real.cos_sub, Real.cos_add]; ring
  simp_rw [e]
  rw [show (1 / 4 : ℝ) * ∑' k : ℤ, Real.exp (-(π ^ 2 / 8) * s * k ^ 2) *
      (2 * (dsin N k c * dsin N k a)) =
      (1 / 4) * ∑' k : ℤ, 2 * (Real.exp (-(π ^ 2 / 8) * s * k ^ 2) *
        (dsin N k c * dsin N k a)) by
    congr 1; exact tsum_congr fun k => by ring]
  rw [tsum_mul_left]; ring

 
lemma tsum_ite_dvd (q : ℤ) (hq : q ≠ 0) (j : ℤ) (g : ℤ → ℝ) :
    ∑' k : ℤ, (if q ∣ k - j then g k else 0) = ∑' m : ℤ, g (j + q * m) := by
  have hinj : Function.Injective (fun m : ℤ => j + q * m) := by
    intro m m' h
    simp only [add_right_inj] at h
    exact mul_left_cancel₀ hq h
  rw [← hinj.tsum_eq (f := fun k => if q ∣ k - j then g k else 0)]
  · refine tsum_congr fun m => ?_
    simp
  · intro k hk
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hk
    obtain ⟨⟨m, hm⟩, _⟩ := hk
    exact ⟨m, by simp only; linarith⟩

lemma theta_neg (N : ℕ) (s : ℝ) (j : ℤ) : theta N s (-j) = theta N s j := by
  unfold theta
  rw [← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun m => ?_
  simp only [Equiv.neg_apply, Int.cast_neg]
  congr 2; ring

lemma summable_theta_terms (N : ℕ) {s : ℝ} (hs : 0 < s) (hN : 0 < N) (j : ℤ) :
    Summable (fun m : ℤ => Real.exp (-(π ^ 2 / 8) * s * ((j : ℝ) + 4 * N * m) ^ 2)) := by
  have hq : (4 * N : ℤ) ≠ 0 := by positivity
  have hinj : Function.Injective (fun m : ℤ => j + 4 * N * m) := by
    intro m m' h
    simp only [add_right_inj] at h
    exact mul_left_cancel₀ hq h
  have hα : 0 < π ^ 2 / 8 * s := by positivity
  have := (summable_exp_neg_mul_int_sq' hα).comp_injective hinj
  refine this.congr fun m => ?_
  simp only [Function.comp, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
  congr 1; ring

 
theorem sum_idk_mul_dsin (N : ℕ) (hN : 0 < N) {s : ℝ} (hs : 0 < s) (a j : ℤ) :
    ∑ c ∈ sites1 N, idk s (c / N) (a / N) * dsin N j c = N * theta N s j * dsin N j a := by
  have hα : 0 < π ^ 2 / 8 * s := by positivity
  set f : ℤ → ℝ := fun k => Real.exp (-(π ^ 2 / 8) * s * k ^ 2) with hf
  have hsum : ∀ c : ℤ, Summable (fun k : ℤ => f k * (dsin N k c * dsin N k a)) := by
    intro c
    have hb : ∀ k : ℤ, |dsin N k c * dsin N k a| ≤ 2 := by
      intro k
      have h1 := abs_dsin_le N k c
      have h2 := abs_dsin_le N k a
      rw [abs_mul]; nlinarith [abs_nonneg (dsin N k c), abs_nonneg (dsin N k a)]
    refine (summable_exp_cos hα (fun k => dsin N k c * dsin N k a) hb).congr fun k => ?_
    simp only [hf]; ring_nf
  simp_rw [idk_lattice N hN hs]
  have step1 : ∑ c ∈ sites1 N, (1 / 2) * (∑' k : ℤ, f k * (dsin N k c * dsin N k a)) *
      dsin N j c = (1 / 2) * ∑' k : ℤ, f k * dsin N k a *
        ∑ c ∈ sites1 N, dsin N k c * dsin N j c := by
    have e1 : ∀ c ∈ sites1 N, (1 / 2) * (∑' k : ℤ, f k * (dsin N k c * dsin N k a)) *
        dsin N j c = (1 / 2) * ∑' k : ℤ, f k * dsin N k a * (dsin N k c * dsin N j c) := by
      intro c _
      rw [mul_assoc, ← tsum_mul_right]
      congr 1
      exact tsum_congr fun k => by ring
    rw [sum_congr rfl e1, ← mul_sum, ← Summable.tsum_finsetSum (fun c _ =>
      ((hsum c).mul_right (dsin N j c)).congr fun k => by ring)]
    congr 1
    refine tsum_congr fun k => ?_
    rw [mul_sum]
  rw [step1]
  simp_rw [dsin_orth N hN]
  have e : ∀ k : ℤ, f k * dsin N k a * (N * ((if (4 * N : ℤ) ∣ k - j then (1 : ℝ) else 0) -
      (if (4 * N : ℤ) ∣ k + j then (1 : ℝ) else 0))) =
      N * ((if (4 * N : ℤ) ∣ k - j then f k * dsin N k a else 0) -
        (if (4 * N : ℤ) ∣ k - (-j) then f k * dsin N k a else 0)) := by
    intro k
    rw [show k - -j = k + j by ring]
    split_ifs <;> ring
  simp_rw [e]
  have hq : (4 * N : ℤ) ≠ 0 := by positivity
  have hS1 : Summable (fun k : ℤ => if (4 * N : ℤ) ∣ k - j then f k * dsin N k a else 0) := by
    refine Summable.of_norm_bounded (summable_exp_neg_mul_int_sq' hα) fun k => ?_
    split_ifs
    · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have := abs_dsin_le N k a
      calc f k * |dsin N k a| ≤ f k * 1 :=
            mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
        _ = Real.exp (-(π ^ 2 / 8 * s) * k ^ 2) := by simp only [hf]; ring_nf
    · rw [norm_zero]; exact (Real.exp_pos _).le
  have hS2 : Summable (fun k : ℤ => if (4 * N : ℤ) ∣ k - (-j) then f k * dsin N k a else 0) := by
    refine Summable.of_norm_bounded (summable_exp_neg_mul_int_sq' hα) fun k => ?_
    split_ifs
    · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have := abs_dsin_le N k a
      calc f k * |dsin N k a| ≤ f k * 1 :=
            mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
        _ = Real.exp (-(π ^ 2 / 8 * s) * k ^ 2) := by simp only [hf]; ring_nf
    · rw [norm_zero]; exact (Real.exp_pos _).le
  rw [tsum_mul_left, hS1.tsum_sub hS2, tsum_ite_dvd _ hq, tsum_ite_dvd _ hq]
  have h1 : ∑' m : ℤ, f (j + 4 * N * m) * dsin N (j + 4 * N * m) a = theta N s j * dsin N j a := by
    rw [theta, ← tsum_mul_right]
    refine tsum_congr fun m => ?_
    rw [dsin_add_period N hN]
    simp only [hf]; push_cast; ring_nf
  have h2 : ∑' m : ℤ, f (-j + 4 * N * m) * dsin N (-j + 4 * N * m) a =
      -(theta N s j * dsin N j a) := by
    rw [← theta_neg, theta, ← tsum_mul_right, ← tsum_neg]
    refine tsum_congr fun m => ?_
    rw [dsin_add_period N hN, dsin_neg_freq]
    simp only [hf]; push_cast; ring_nf
  rw [h1, h2]; ring

 

def thetaConst : ℝ := ∑' m : ℤ, Real.exp (-(π ^ 2 / 8) * m ^ 2)

lemma thetaConst_nonneg : 0 ≤ thetaConst := tsum_nonneg fun _ => (Real.exp_pos _).le

theorem theta_sub_bounds (N : ℕ) (hN : 0 < N) {s : ℝ} (hs : 0 < s) (hsN : 1 / 2 ≤ s * N ^ 2)
    {j : ℤ} (hj : j ∈ modes N) :
    0 ≤ theta N s j - Real.exp (-(π ^ 2 / 8) * s * j ^ 2) ∧
      theta N s j - Real.exp (-(π ^ 2 / 8) * s * j ^ 2) ≤
        thetaConst * Real.exp (-(π ^ 2 / 4) * s * N ^ 2) := by
  have hS := summable_theta_terms N hs hN j
  set f : ℤ → ℝ := fun m => Real.exp (-(π ^ 2 / 8) * s * ((j : ℝ) + 4 * N * m) ^ 2) with hf
  have hsplit : theta N s j = f 0 + ∑' m : ℤ, (if m = 0 then 0 else f m) := by
    unfold theta; exact hS.tsum_eq_add_tsum_ite 0
  have hf0 : f 0 = Real.exp (-(π ^ 2 / 8) * s * j ^ 2) := by
    show Real.exp (-(π ^ 2 / 8) * s * ((j : ℝ) + 4 * N * ((0 : ℤ) : ℝ)) ^ 2) = _
    simp
  rw [hsplit, hf0, add_sub_cancel_left]
  have hnn : ∀ m : ℤ, 0 ≤ (if m = 0 then 0 else f m) := fun m => by
    split_ifs; exact le_rfl; exact (Real.exp_pos _).le
  refine ⟨tsum_nonneg hnn, ?_⟩
  simp only [modes, mem_Icc] at hj
  have hπ := Real.pi_pos
  have hbound : ∀ m : ℤ, (if m = 0 then 0 else f m) ≤
      Real.exp (-(π ^ 2 / 4) * s * N ^ 2) * Real.exp (-(π ^ 2 / 8) * m ^ 2) := by
    intro m
    split_ifs with hm
    · positivity
    · rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hm
      have hjr1 : (1 : ℝ) ≤ j := by exact_mod_cast hj.1
      have hjr2 : (j : ℝ) ≤ 2 * N - 1 := by exact_mod_cast hj.2
      have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
      
      have habs : 2 * N * |(m : ℝ)| ≤ |(j : ℝ) + 4 * N * m| := by
        have h1 : |(4 : ℝ) * N * m| = 4 * N * |(m : ℝ)| := by
          rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 * N)]
        have h2 := abs_sub_abs_le_abs_sub ((4 : ℝ) * N * m) (-(j : ℝ))
        rw [abs_neg, abs_of_pos (by linarith : (0 : ℝ) < j), h1] at h2
        rw [show (4 : ℝ) * N * m - -j = j + 4 * N * m by ring] at h2
        nlinarith
      have hsq : (2 * N * |(m : ℝ)|) ^ 2 ≤ ((j : ℝ) + 4 * N * m) ^ 2 := by
        rw [← sq_abs ((j : ℝ) + 4 * N * m)]
        exact pow_le_pow_left₀ (by positivity) habs 2
      have hm2 : (m : ℝ) ^ 2 = |(m : ℝ)| ^ 2 := (sq_abs _).symm
      have hkey : (4 : ℝ) * N ^ 2 * m ^ 2 ≤ ((j : ℝ) + 4 * N * m) ^ 2 := by
        rw [hm2]; nlinarith
      
      have hm2' : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by rw [hm2]; nlinarith
      have hA : (π ^ 2 / 8) * s * (4 * N ^ 2 * m ^ 2) ≥
          (π ^ 2 / 4) * s * N ^ 2 + (π ^ 2 / 8) * m ^ 2 := by
        have : s * N ^ 2 * m ^ 2 ≥ s * N ^ 2 / 2 + m ^ 2 / 4 := by nlinarith
        nlinarith [sq_nonneg π]
      have hB : (π ^ 2 / 8) * s * (4 * N ^ 2 * m ^ 2) ≤
          (π ^ 2 / 8) * s * ((j : ℝ) + 4 * N * m) ^ 2 :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
      nlinarith
  have hsum2 : Summable (fun m : ℤ =>
      Real.exp (-(π ^ 2 / 4) * s * N ^ 2) * Real.exp (-(π ^ 2 / 8) * m ^ 2)) :=
    (summable_exp_neg_mul_int_sq' (by positivity)).mul_left _
  calc ∑' m : ℤ, (if m = 0 then 0 else f m)
      ≤ ∑' m : ℤ, Real.exp (-(π ^ 2 / 4) * s * N ^ 2) * Real.exp (-(π ^ 2 / 8) * m ^ 2) :=
        Summable.tsum_le_tsum hbound (Summable.of_nonneg_of_le hnn hbound hsum2) hsum2
    _ = thetaConst * Real.exp (-(π ^ 2 / 4) * s * N ^ 2) := by
        rw [tsum_mul_left, thetaConst]; ring

end SupercriticalLQGUniqueness.B2.QPos.P7
