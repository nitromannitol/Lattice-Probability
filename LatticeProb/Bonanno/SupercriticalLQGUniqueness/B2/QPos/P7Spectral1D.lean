/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P7Spectral1D at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P7Field
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P7Theta

 









set_option autoImplicit false
noncomputable section

open Real Finset
open LQGMetric LQGMetric.HeatSq

namespace SupercriticalLQGUniqueness.B2.QPos.P7

 
theorem dst_parseval (N : ℕ) (hN : 0 < N) (α : ℤ → ℝ) :
    ∑ c ∈ sites1 N, α c ^ 2 =
      (N : ℝ)⁻¹ * ∑ j ∈ modes N, (∑ c ∈ sites1 N, α c * dsin N j c) ^ 2 := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have h : ∑ j ∈ modes N, (∑ c ∈ sites1 N, α c * dsin N j c) ^ 2 =
      ∑ c ∈ sites1 N, ∑ c' ∈ sites1 N, α c * α c' *
        ∑ j ∈ modes N, dsin N j c * dsin N j c' := by
    simp_rw [sq, sum_mul_sum, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun c _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun c' _ => sum_congr rfl fun j _ => by ring
  rw [h]
  have h2 : ∀ c ∈ sites1 N, ∑ c' ∈ sites1 N, α c * α c' *
      ∑ j ∈ modes N, dsin N j c * dsin N j c' = N * α c ^ 2 := by
    intro c hc
    rw [sum_congr rfl fun c' hc' => by rw [dsin_complete N hN hc hc']]
    simp only [mul_ite, mul_zero, sum_ite_eq, hc, if_true]
    ring
  rw [sum_congr rfl h2, ← mul_sum, ← mul_assoc, inv_mul_cancel₀ hN', one_mul]

 
theorem sum_mul_qker_mul_dsin (N : ℕ) (hN : 0 < N) (s : ℝ) (a : ℤ) {j : ℤ} (hj : j ∈ modes N) :
    ∑ c ∈ sites1 N, ((N : ℝ) * qker N s a c) * dsin N j c =
      N * Real.exp (-s * mu N j) * dsin N j a := by
  simp_rw [mul_qker_eq N hN, sum_mul]
  rw [sum_comm]
  have h : ∀ k ∈ modes N, ∑ c ∈ sites1 N,
      Real.exp (-s * mu N k) * dsin N k a * dsin N k c * dsin N j c =
      Real.exp (-s * mu N k) * dsin N k a * (if k = j then (N : ℝ) else 0) := by
    intro k hk
    rw [← dsin_orth_modes N hN hk hj, mul_sum]
    refine sum_congr rfl fun c _ => by ring
  rw [sum_congr rfl h]
  simp only [mul_ite, mul_zero, sum_ite_eq', hj, if_true]
  ring

 
theorem sum_walk_sub_idk_sq (N : ℕ) (hN : 0 < N) {s : ℝ} (hs : 0 < s) (a : ℤ) :
    (∑ c ∈ sites1 N, ((N : ℝ) * qker N s a c - idk s (c / N) (a / N)) ^ 2) / N =
      ∑ j ∈ modes N, (Real.exp (-s * mu N j) - theta N s j) ^ 2 * dsin N j a ^ 2 := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [dst_parseval N hN]
  have hcoef : ∀ j ∈ modes N, ∑ c ∈ sites1 N,
      ((N : ℝ) * qker N s a c - idk s (c / N) (a / N)) * dsin N j c =
      N * ((Real.exp (-s * mu N j) - theta N s j) * dsin N j a) := by
    intro j hj
    simp_rw [sub_mul]
    rw [sum_sub_distrib, sum_mul_qker_mul_dsin N hN s a hj, sum_idk_mul_dsin N hN hs a j]
    ring
  rw [sum_congr rfl fun j hj => by rw [hcoef j hj]]
  rw [mul_sum, sum_div]
  refine sum_congr rfl fun j _ => ?_
  field_simp

 

lemma mu_le_quad (N : ℕ) (hN : 0 < N) (j : ℤ) : mu N j ≤ π ^ 2 * j ^ 2 / 8 := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have h := Real.one_sub_sq_div_two_le_cos (x := (j : ℝ) * π / (2 * N))
  unfold mu
  have e : π ^ 2 * (j : ℝ) ^ 2 / 8 = (N : ℝ) ^ 2 * (((j : ℝ) * π / (2 * N)) ^ 2 / 2) := by
    field_simp; ring
  rw [e]
  exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)

lemma quad_sub_mu_le (N : ℕ) (hN : 0 < N) (j : ℤ) (hx : |(j : ℝ) * π / (2 * N)| ≤ 1) :
    π ^ 2 * j ^ 2 / 8 - mu N j ≤ (5 * π ^ 4 / 1536) * j ^ 4 / N ^ 2 := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have h := Real.cos_bound hx
  have h' := (abs_le.mp h).2
  unfold mu
  have e1 : π ^ 2 * (j : ℝ) ^ 2 / 8 = (N : ℝ) ^ 2 * (((j : ℝ) * π / (2 * N)) ^ 2 / 2) := by
    field_simp; ring
  have e2 : (5 * π ^ 4 / 1536) * (j : ℝ) ^ 4 / N ^ 2 =
      (N : ℝ) ^ 2 * (|(j : ℝ) * π / (2 * N)| ^ 4 * (5 / 96)) := by
    rw [show |(j : ℝ) * π / (2 * N)| ^ 4 = ((j : ℝ) * π / (2 * N)) ^ 4 by
      rw [← abs_pow, abs_of_nonneg (by positivity)]]
    field_simp; ring
  rw [e1, e2, ← mul_sub]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  linarith

 
lemma pow_four_le_exp {y : ℝ} (hy : 0 ≤ y) : y ^ 4 ≤ 24 * Real.exp y := by
  have := Real.pow_div_factorial_le_exp y hy 4
  norm_num [Nat.factorial] at this
  linarith

 
lemma pow_eight_mul_exp_le {s : ℝ} (hs : 0 < s) (j : ℝ) :
    j ^ 8 * Real.exp (-s * j ^ 2) ≤ 384 * (s ^ 4)⁻¹ * Real.exp (-(s / 2) * j ^ 2) := by
  have h := pow_four_le_exp (show 0 ≤ s / 2 * j ^ 2 by positivity)
  have e : Real.exp (-s * j ^ 2) = Real.exp (-(s / 2) * j ^ 2) * Real.exp (-(s / 2 * j ^ 2)) := by
    rw [← Real.exp_add]; ring_nf
  rw [e]
  have hE : Real.exp (s / 2 * j ^ 2) * Real.exp (-(s / 2 * j ^ 2)) = 1 := by
    rw [← Real.exp_add]; simp
  have hs4 : 0 < s ^ 4 := by positivity
  have h2 : j ^ 8 * Real.exp (-(s / 2 * j ^ 2)) ≤ 384 * (s ^ 4)⁻¹ := by
    rw [le_mul_inv_iff₀ hs4]
    have : (s / 2 * j ^ 2) ^ 4 = s ^ 4 * j ^ 8 / 16 := by ring
    rw [this] at h
    have hE' := Real.exp_pos (-(s / 2 * j ^ 2))
    nlinarith
  have hpos := Real.exp_pos (-(s / 2) * j ^ 2)
  nlinarith

 
lemma exp_neg_le_two_div_sq {y : ℝ} (hy : 0 < y) : Real.exp (-y) ≤ 2 / y ^ 2 := by
  have h := Real.pow_div_factorial_le_exp y hy.le 2
  norm_num [Nat.factorial] at h
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos y) (by positivity)]
  rw [div_le_iff₀ (by positivity)] at *
  field_simp
  linarith

 
lemma exp_mu_sub_sq_le (N : ℕ) (hN : 0 < N) {s : ℝ} (hs : 0 < s) {j : ℤ} (hj : j ∈ modes N) :
    (Real.exp (-s * mu N j) - Real.exp (-(π ^ 2 / 8) * s * j ^ 2)) ^ 2 ≤
      ((5 * π ^ 4 / 1536) ^ 2 * s ^ 2 * (j : ℝ) ^ 8 * Real.exp (-s * j ^ 2)) / N ^ 4 +
        Real.exp (-(2 / π ^ 2) * s * N ^ 2) * Real.exp (-(s / 2) * j ^ 2) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hπ := Real.pi_pos
  have hmu1 := mu_le_quad N hN j
  have hmu2 := mu_ge N hj
  set e := Real.exp (-s * mu N j)
  set f := Real.exp (-(π ^ 2 / 8) * s * j ^ 2)
  have hfe : f ≤ e := Real.exp_le_exp.mpr (by nlinarith)
  have he : e ≤ Real.exp (-(s / 2) * j ^ 2) := Real.exp_le_exp.mpr (by nlinarith)
  have hf0 : 0 ≤ f := (Real.exp_pos _).le
  have hT1 : 0 ≤ ((5 * π ^ 4 / 1536) ^ 2 * s ^ 2 * (j : ℝ) ^ 8 * Real.exp (-s * j ^ 2)) / N ^ 4 :=
    by positivity
  have hT2 : 0 ≤ Real.exp (-(2 / π ^ 2) * s * N ^ 2) * Real.exp (-(s / 2) * j ^ 2) := by
    positivity
  by_cases hx : |(j : ℝ) * π / (2 * N)| ≤ 1
  · 
    have hΔ := quad_sub_mu_le N hN j hx
    set Δ := π ^ 2 * (j : ℝ) ^ 2 / 8 - mu N j
    have hΔ0 : 0 ≤ Δ := by simp only [Δ]; linarith
    have hfe' : f = e * Real.exp (-s * Δ) := by
      simp only [f, e, Δ]; rw [← Real.exp_add]; ring_nf
    have h1 : e - f ≤ e * (s * Δ) := by
      rw [hfe']
      have := Real.add_one_le_exp (-s * Δ)
      have he0 : 0 ≤ e := (Real.exp_pos _).le
      nlinarith
    have h2 : e * (s * Δ) ≤ Real.exp (-(s / 2) * j ^ 2) *
        (s * ((5 * π ^ 4 / 1536) * j ^ 4 / N ^ 2)) := by
      apply mul_le_mul he (mul_le_mul_of_nonneg_left hΔ hs.le) (by positivity)
        (Real.exp_pos _).le
    have h3 : (e - f) ^ 2 ≤ (Real.exp (-(s / 2) * j ^ 2) *
        (s * ((5 * π ^ 4 / 1536) * j ^ 4 / N ^ 2))) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (h1.trans h2) 2
    have h4 : (Real.exp (-(s / 2) * j ^ 2) * (s * ((5 * π ^ 4 / 1536) * j ^ 4 / N ^ 2))) ^ 2 =
        ((5 * π ^ 4 / 1536) ^ 2 * s ^ 2 * (j : ℝ) ^ 8 * Real.exp (-s * j ^ 2)) / N ^ 4 := by
      rw [mul_pow, ← Real.exp_nat_mul]
      field_simp
      ring_nf
    linarith
  · 
    push_neg at hx
    have hj1 : (1 : ℝ) ≤ j := by simp only [modes, mem_Icc] at hj; exact_mod_cast hj.1
    have hx' : 1 < (j : ℝ) * π / (2 * N) := by
      rwa [abs_of_nonneg (by positivity)] at hx
    have hj2 : 4 * (N : ℝ) ^ 2 / π ^ 2 ≤ (j : ℝ) ^ 2 := by
      rw [lt_div_iff₀ (by positivity)] at hx'
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have h1 : (e - f) ^ 2 ≤ e ^ 2 := by
      have : 0 ≤ e - f := by linarith
      nlinarith
    have h2 : e ^ 2 ≤ Real.exp (-(s / 2) * j ^ 2) * Real.exp (-(s / 2) * j ^ 2) := by
      rw [sq]; exact mul_le_mul he he (Real.exp_pos _).le (Real.exp_pos _).le
    have h3 : Real.exp (-(s / 2) * j ^ 2) ≤ Real.exp (-(2 / π ^ 2) * s * N ^ 2) := by
      refine Real.exp_le_exp.mpr ?_
      have : (2 / π ^ 2) * s * N ^ 2 = (s / 2) * (4 * N ^ 2 / π ^ 2) := by field_simp; ring
      rw [neg_mul, neg_mul, neg_mul, this, neg_le_neg_iff]
      exact mul_le_mul_of_nonneg_left hj2 (by positivity)
    have h4 : Real.exp (-(s / 2) * j ^ 2) * Real.exp (-(s / 2) * j ^ 2) ≤
        Real.exp (-(2 / π ^ 2) * s * N ^ 2) * Real.exp (-(s / 2) * j ^ 2) :=
      mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
    linarith

 
def cS1 : ℝ := (384 * (5 * π ^ 4 / 1536) ^ 2 + π ^ 4 / 2) * (Real.sqrt (2 * π) / 2)

lemma cS1_nonneg : 0 ≤ cS1 := by unfold cS1; positivity

lemma card_modes (N : ℕ) (hN : 0 < N) : ((modes N).card : ℝ) = 2 * N - 1 := by
  simp only [modes, Int.card_Icc]
  rw [show (2 * (N : ℤ) - 1 + 1 - 1) = ((2 * N - 1 : ℕ) : ℤ) by omega]
  simp only [Int.toNat_natCast]
  rw [Nat.cast_sub (by omega)]; push_cast; ring

 
lemma sum_modes_exp_half_le (N : ℕ) {s : ℝ} (hs : 0 < s) :
    ∑ j ∈ modes N, Real.exp (-(s / 2) * (j : ℝ) ^ 2) ≤ Real.sqrt (2 * π) / 2 * (Real.sqrt s)⁻¹ := by
  have h := sum_modes_exp_le N (show 0 < s / 2 by positivity)
  have e : Real.sqrt (π / (s / 2)) / 2 = Real.sqrt (2 * π) / 2 * (Real.sqrt s)⁻¹ := by
    rw [show π / (s / 2) = (2 * π) / s by field_simp, Real.sqrt_div' _ hs.le]
    field_simp
  rw [e] at h
  refine le_trans (le_of_eq ?_) h
  exact sum_congr rfl fun j _ => by ring_nf

 

theorem sum_exp_mu_sub_sq_le (N : ℕ) (hN : 0 < N) {s : ℝ} (hs : 0 < s) :
    ∑ j ∈ modes N, (Real.exp (-s * mu N j) - Real.exp (-(π ^ 2 / 8) * s * j ^ 2)) ^ 2 ≤
      cS1 * (Real.sqrt s)⁻¹ * ((N : ℝ) ^ 4 * s ^ 2)⁻¹ := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hπ := Real.pi_pos
  set c₁ := (5 * π ^ 4 / 1536) ^ 2
  
  have hK : ∀ j ∈ modes N,
      (Real.exp (-s * mu N j) - Real.exp (-(π ^ 2 / 8) * s * j ^ 2)) ^ 2 ≤
        (384 * c₁ * ((N : ℝ) ^ 4 * s ^ 2)⁻¹ + Real.exp (-(2 / π ^ 2) * s * N ^ 2)) *
          Real.exp (-(s / 2) * (j : ℝ) ^ 2) := by
    intro j hj
    refine (exp_mu_sub_sq_le N hN hs hj).trans ?_
    have h8 := pow_eight_mul_exp_le hs (j : ℝ)
    have : (c₁ * s ^ 2 * (j : ℝ) ^ 8 * Real.exp (-s * j ^ 2)) / N ^ 4 ≤
        384 * c₁ * ((N : ℝ) ^ 4 * s ^ 2)⁻¹ * Real.exp (-(s / 2) * (j : ℝ) ^ 2) := by
      have hc : 0 ≤ c₁ * s ^ 2 / N ^ 4 := by positivity
      calc (c₁ * s ^ 2 * (j : ℝ) ^ 8 * Real.exp (-s * j ^ 2)) / N ^ 4
          = (c₁ * s ^ 2 / N ^ 4) * ((j : ℝ) ^ 8 * Real.exp (-s * j ^ 2)) := by ring
        _ ≤ (c₁ * s ^ 2 / N ^ 4) * (384 * (s ^ 4)⁻¹ * Real.exp (-(s / 2) * (j : ℝ) ^ 2)) :=
            mul_le_mul_of_nonneg_left h8 hc
        _ = 384 * c₁ * ((N : ℝ) ^ 4 * s ^ 2)⁻¹ * Real.exp (-(s / 2) * (j : ℝ) ^ 2) := by
            field_simp
    nlinarith
  refine (sum_le_sum hK).trans ?_
  rw [← mul_sum]
  have hsum := sum_modes_exp_half_le N hs
  have hexp : Real.exp (-(2 / π ^ 2) * s * N ^ 2) ≤ π ^ 4 / 2 * ((N : ℝ) ^ 4 * s ^ 2)⁻¹ := by
    have h := exp_neg_le_two_div_sq (show 0 < 2 / π ^ 2 * s * N ^ 2 by positivity)
    rw [show -(2 / π ^ 2) * s * N ^ 2 = -(2 / π ^ 2 * s * N ^ 2) by ring]
    refine h.trans (le_of_eq ?_)
    field_simp
  have hfac : 0 ≤ 384 * c₁ * ((N : ℝ) ^ 4 * s ^ 2)⁻¹ +
      Real.exp (-(2 / π ^ 2) * s * N ^ 2) := by positivity
  calc (384 * c₁ * ((N : ℝ) ^ 4 * s ^ 2)⁻¹ + Real.exp (-(2 / π ^ 2) * s * N ^ 2)) *
        ∑ j ∈ modes N, Real.exp (-(s / 2) * (j : ℝ) ^ 2)
      ≤ (384 * c₁ * ((N : ℝ) ^ 4 * s ^ 2)⁻¹ + π ^ 4 / 2 * ((N : ℝ) ^ 4 * s ^ 2)⁻¹) *
          (Real.sqrt (2 * π) / 2 * (Real.sqrt s)⁻¹) := by
        apply mul_le_mul (by linarith) hsum (sum_nonneg fun _ _ => (Real.exp_pos _).le)
        positivity
    _ = cS1 * (Real.sqrt s)⁻¹ * ((N : ℝ) ^ 4 * s ^ 2)⁻¹ := by
        unfold cS1; ring

 
def cS2 : ℝ := thetaConst ^ 2 * (48 / π ^ 6 + 8 / π ^ 4)

lemma cS2_nonneg : 0 ≤ cS2 := by unfold cS2; positivity

 

theorem sum_exp_sub_theta_sq_le (N : ℕ) (hN : 0 < N) {s : ℝ} (hs : 0 < s)
    (hsN : 1 / 2 ≤ s * N ^ 2) :
    ∑ j ∈ modes N, (Real.exp (-(π ^ 2 / 8) * s * j ^ 2) - theta N s j) ^ 2 ≤
      cS2 * (Real.sqrt s)⁻¹ * ((N : ℝ) ^ 4 * s ^ 2)⁻¹ := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hπ := Real.pi_pos
  have hT := thetaConst_nonneg
  set u := s * (N : ℝ) ^ 2 with hu
  have hu0 : 0 < u := by positivity
  have hmode : ∀ j ∈ modes N, (Real.exp (-(π ^ 2 / 8) * s * j ^ 2) - theta N s j) ^ 2 ≤
      thetaConst ^ 2 * Real.exp (-(π ^ 2 / 2) * u) := by
    intro j hj
    obtain ⟨h0, h1⟩ := theta_sub_bounds N hN hs hsN hj
    have : (Real.exp (-(π ^ 2 / 8) * s * j ^ 2) - theta N s j) ^ 2 =
        (theta N s j - Real.exp (-(π ^ 2 / 8) * s * j ^ 2)) ^ 2 := by ring
    rw [this]
    calc (theta N s j - Real.exp (-(π ^ 2 / 8) * s * j ^ 2)) ^ 2
        ≤ (thetaConst * Real.exp (-(π ^ 2 / 4) * s * N ^ 2)) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = thetaConst ^ 2 * Real.exp (-(π ^ 2 / 2) * u) := by
          rw [mul_pow, ← Real.exp_nat_mul, hu]; congr 2; push_cast; ring
  refine (sum_le_sum hmode).trans ?_
  rw [sum_const, nsmul_eq_mul, card_modes N hN]
  
  have hss : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hsq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
  have hamgm : 2 * N * Real.sqrt s ≤ u + 1 := by
    have := sq_nonneg ((N : ℝ) * Real.sqrt s - 1)
    nlinarith
  have hE3 : u ^ 3 * Real.exp (-(π ^ 2 / 2) * u) ≤ 48 / π ^ 6 := by
    have h := Real.pow_div_factorial_le_exp _ (show 0 ≤ π ^ 2 / 2 * u by positivity) 3
    norm_num [Nat.factorial] at h
    have hE := Real.exp_pos (π ^ 2 / 2 * u)
    have hEE : Real.exp (π ^ 2 / 2 * u) * Real.exp (-(π ^ 2 / 2) * u) = 1 := by
      rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
    rw [le_div_iff₀ (by positivity)]
    have : (π ^ 2 / 2 * u) ^ 3 = π ^ 6 * u ^ 3 / 8 := by ring
    rw [this] at h
    nlinarith [Real.exp_pos (-(π ^ 2 / 2) * u)]
  have hE2 : u ^ 2 * Real.exp (-(π ^ 2 / 2) * u) ≤ 8 / π ^ 4 := by
    have h := Real.pow_div_factorial_le_exp _ (show 0 ≤ π ^ 2 / 2 * u by positivity) 2
    norm_num [Nat.factorial] at h
    have hEE : Real.exp (π ^ 2 / 2 * u) * Real.exp (-(π ^ 2 / 2) * u) = 1 := by
      rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
    rw [le_div_iff₀ (by positivity)]
    have : (π ^ 2 / 2 * u) ^ 2 = π ^ 4 * u ^ 2 / 4 := by ring
    rw [this] at h
    nlinarith [Real.exp_pos (-(π ^ 2 / 2) * u)]
  have hN4 : (N : ℝ) ^ 4 * s ^ 2 = u ^ 2 := by rw [hu]; ring
  rw [hN4]
  have hgoal : (2 * (N : ℝ) - 1) * (thetaConst ^ 2 * Real.exp (-(π ^ 2 / 2) * u)) *
      (Real.sqrt s * u ^ 2) ≤ cS2 := by
    have h1 : (2 * (N : ℝ) - 1) * Real.sqrt s ≤ u + 1 := by nlinarith
    calc (2 * (N : ℝ) - 1) * (thetaConst ^ 2 * Real.exp (-(π ^ 2 / 2) * u)) *
          (Real.sqrt s * u ^ 2)
        = thetaConst ^ 2 * (((2 * (N : ℝ) - 1) * Real.sqrt s) *
            (u ^ 2 * Real.exp (-(π ^ 2 / 2) * u))) := by ring
      _ ≤ thetaConst ^ 2 * ((u + 1) * (u ^ 2 * Real.exp (-(π ^ 2 / 2) * u))) := by
          gcongr
      _ = thetaConst ^ 2 * (u ^ 3 * Real.exp (-(π ^ 2 / 2) * u) +
            u ^ 2 * Real.exp (-(π ^ 2 / 2) * u)) := by ring
      _ ≤ thetaConst ^ 2 * (48 / π ^ 6 + 8 / π ^ 4) := by gcongr
      _ = cS2 := rfl
  rw [show cS2 * (Real.sqrt s)⁻¹ * (u ^ 2)⁻¹ = cS2 / (Real.sqrt s * u ^ 2) by
    field_simp]
  rw [le_div_iff₀ (by positivity)]
  exact hgoal

 
theorem sum_walk_sub_idk_sq_le (N : ℕ) (hN : 0 < N) {s : ℝ} (hs : 0 < s)
    (hsN : 1 / 2 ≤ s * N ^ 2) (a : ℤ) :
    (∑ c ∈ sites1 N, ((N : ℝ) * qker N s a c - idk s (c / N) (a / N)) ^ 2) / N ≤
      2 * (cS1 + cS2) * (Real.sqrt s)⁻¹ * ((N : ℝ) ^ 4 * s ^ 2)⁻¹ := by
  rw [sum_walk_sub_idk_sq N hN hs a]
  have h1 : ∀ j ∈ modes N, (Real.exp (-s * mu N j) - theta N s j) ^ 2 * dsin N j a ^ 2 ≤
      2 * (Real.exp (-s * mu N j) - Real.exp (-(π ^ 2 / 8) * s * j ^ 2)) ^ 2 +
        2 * (Real.exp (-(π ^ 2 / 8) * s * j ^ 2) - theta N s j) ^ 2 := by
    intro j _
    have hd : dsin N j a ^ 2 ≤ 1 := by
      have := abs_dsin_le N j a
      nlinarith [abs_nonneg (dsin N j a), sq_abs (dsin N j a)]
    have hsq : (Real.exp (-s * mu N j) - theta N s j) ^ 2 ≤
        2 * (Real.exp (-s * mu N j) - Real.exp (-(π ^ 2 / 8) * s * j ^ 2)) ^ 2 +
          2 * (Real.exp (-(π ^ 2 / 8) * s * j ^ 2) - theta N s j) ^ 2 := by
      nlinarith [sq_nonneg (Real.exp (-s * mu N j) - 2 * Real.exp (-(π ^ 2 / 8) * s * j ^ 2) +
        theta N s j)]
    calc (Real.exp (-s * mu N j) - theta N s j) ^ 2 * dsin N j a ^ 2
        ≤ (Real.exp (-s * mu N j) - theta N s j) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hd (sq_nonneg _)
      _ ≤ _ := by rw [mul_one]; exact hsq
  refine (sum_le_sum h1).trans ?_
  rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  have hA := sum_exp_mu_sub_sq_le N hN hs
  have hB := sum_exp_sub_theta_sq_le N hN hs hsN
  have : 2 * (cS1 + cS2) * (Real.sqrt s)⁻¹ * ((N : ℝ) ^ 4 * s ^ 2)⁻¹ =
      2 * (cS1 * (Real.sqrt s)⁻¹ * ((N : ℝ) ^ 4 * s ^ 2)⁻¹) +
        2 * (cS2 * (Real.sqrt s)⁻¹ * ((N : ℝ) ^ 4 * s ^ 2)⁻¹) := by ring
  rw [this]
  linarith

end SupercriticalLQGUniqueness.B2.QPos.P7
