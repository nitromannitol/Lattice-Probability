import Mathlib
import LatticeProb.Walk.ContinuousHeat
import LatticeProb.Walk.LineKernelLocalLimit

/-!
# The local limit theorem for the continuous-time walk on `ℤ^d`

`ctGauss d t x = ∏ᵢ lineGauss (t / d) (xᵢ) = (2πt/d)^{-d/2} e^{-d|x|²/(2t)}` is the Gaussian
counterpart of `ctHeat`. Because both kernels are products over the coordinates, the
one-dimensional local limit theorem with its Gaussian-weighted error passes to `ℤ^d` by
telescoping the product: for `t ≥ 1`,
`|ctHeat d t x - ctGauss d t x| ≤ C t^{-(d+2)/2} exp(-c|x|²/(t + |x|))`
(`exists_abs_ctHeat_sub_ctGauss_le`).
-/

open MeasureTheory Filter Topology

noncomputable section

namespace LatticeProb.ContinuousTime

variable {d : ℕ}

/-- The Gaussian counterpart of `ctHeat`, the product of the one-dimensional Gaussians at
time `t / d`. -/
def ctGauss (d : ℕ) (t : ℝ) (x : Site d) : ℝ := ∏ i, lineGauss (t / d) (x i)

/-- The Gaussian counterpart is continuous at positive times. -/
theorem continuousOn_ctGauss (x : Site d) : ContinuousOn (fun t => ctGauss d t x) (Set.Ioi 0) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp only [ctGauss, Finset.univ_eq_empty, Finset.prod_empty]
    exact continuousOn_const
  · unfold ctGauss
    apply continuousOn_finsetProd
    intro i _
    unfold lineGauss
    apply ContinuousOn.mul
    · apply ContinuousOn.inv₀
      · exact Real.continuous_sqrt.comp_continuousOn (by fun_prop)
      · intro t ht
        have htd : 0 < t / (d : ℝ) := div_pos ht (by exact_mod_cast hd)
        exact ne_of_gt (Real.sqrt_pos.mpr (mul_pos (by positivity) htd))
    · apply Real.continuous_exp.comp_continuousOn
      apply ContinuousOn.div
      · exact continuousOn_const
      · exact continuousOn_const.mul (continuousOn_id.div_const (d : ℝ))
      · intro t ht
        have htd : 0 < t / (d : ℝ) := div_pos ht (by exact_mod_cast hd)
        positivity

/-- The Gaussian counterpart in closed form:
`ḡ_t(x) = (2π/d)^{-d/2} t^{-d/2} e^{-(d|x|²/2)/t}`. -/
theorem ctGauss_eq (hd : 1 ≤ d) {t : ℝ} (ht : 0 < t) (x : Site d) :
    ctGauss d t x = (2 * Real.pi / d) ^ (-(d : ℝ) / 2)
      * (t ^ (-((d : ℝ) / 2)) * Real.exp (-(d * euclidNorm x ^ 2 / 2) / t)) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := ne_of_gt hdpos
  have htd : 0 < t / (d : ℝ) := div_pos ht hdpos
  have hy : 0 < 2 * Real.pi * (t / (d : ℝ)) := mul_pos (by positivity) htd
  have hsqrt : ((Real.sqrt (2 * Real.pi * (t / (d : ℝ))))⁻¹) ^ d
      = (2 * Real.pi * (t / (d : ℝ))) ^ (-(d : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hy.le (1 / 2), ← Real.rpow_natCast,
      ← Real.rpow_mul hy.le]
    congr 1
    ring
  have hmul : (2 * Real.pi * (t / (d : ℝ))) ^ (-(d : ℝ) / 2)
      = (2 * Real.pi / d) ^ (-(d : ℝ) / 2) * t ^ (-(d : ℝ) / 2) := by
    have hbase : 2 * Real.pi * (t / (d : ℝ)) = (2 * Real.pi / d) * t := by
      field_simp
    rw [hbase, Real.mul_rpow (le_of_lt (div_pos (by positivity) hdpos)) ht.le]
  have hterm : ∀ i : Fin d, -((x i : ℝ) ^ 2) / (2 * (t / (d : ℝ)))
      = (-(d / 2) / t) * (x i : ℝ) ^ 2 := by
    intro i
    field_simp
  have hexp : (∑ i, -((x i : ℝ) ^ 2) / (2 * (t / (d : ℝ))))
      = -(d * euclidNorm x ^ 2 / 2) / t := by
    calc ∑ i, -((x i : ℝ) ^ 2) / (2 * (t / (d : ℝ)))
        = ∑ i, (-(d / 2) / t) * (x i : ℝ) ^ 2 :=
          Finset.sum_congr rfl (fun i _ => hterm i)
      _ = (-(d / 2) / t) * ∑ i, (x i : ℝ) ^ 2 := by
          rw [Finset.mul_sum]
      _ = (-(d / 2) / t) * euclidNorm x ^ 2 := by
          congr 1
          rw [euclidNorm, Real.sq_sqrt (by positivity)]
      _ = -(d * euclidNorm x ^ 2 / 2) / t := by ring
  unfold ctGauss lineGauss
  rw [Finset.prod_mul_distrib, Fin.prod_const, ← Real.exp_sum, hsqrt, hmul, hexp]
  ring_nf

/-- The absolute value of a product is bounded by `A^n` times the product of `m`,
given `|a i| ≤ A * m i`. -/
private lemma abs_prod_le {n : ℕ} {A : ℝ} (a m : Fin n → ℝ)
    (ha : ∀ i, |a i| ≤ A * m i) :
    |∏ i, a i| ≤ A ^ n * ∏ i, m i := by
  rw [Finset.abs_prod]
  calc
    ∏ i : Fin n, |a i| ≤ ∏ i : Fin n, A * m i :=
      Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => ha i)
    _ = (∏ _i : Fin n, A) * ∏ i : Fin n, m i := Finset.prod_mul_distrib
    _ = A ^ n * ∏ i : Fin n, m i := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The algebraic identity closing the induction step of `abs_prod_sub_prod_le`. -/
private lemma prod_succ_bound_eq (A B m0 M : ℝ) (n : ℕ) :
    (B * m0) * (A ^ n * M) + (A * m0) * ((n : ℝ) * A ^ (n - 1) * B * M)
      = ((n + 1 : ℕ) : ℝ) * A ^ n * B * (m0 * M) := by
  rcases n with _ | n
  · simp only [Nat.zero_sub, pow_zero, Nat.cast_zero, zero_mul, mul_zero, add_zero, one_mul]
    ring
  · rw [Nat.add_sub_cancel, pow_succ]
    push_cast
    ring

/-- The telescoping bound for a difference of products: if `|aᵢ|, |bᵢ| ≤ A mᵢ` and
`|aᵢ - bᵢ| ≤ B mᵢ` then `|∏ aᵢ - ∏ bᵢ| ≤ n A^{n-1} B ∏ mᵢ`. -/
theorem abs_prod_sub_prod_le {n : ℕ} {A B : ℝ} (a b m : Fin n → ℝ) (hA : 0 ≤ A)
    (hm : ∀ i, 0 ≤ m i) (ha : ∀ i, |a i| ≤ A * m i) (hb : ∀ i, |b i| ≤ A * m i)
    (hab : ∀ i, |a i - b i| ≤ B * m i) :
    |∏ i, a i - ∏ i, b i| ≤ n * A ^ (n - 1) * B * ∏ i, m i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.prod_univ_succ a, Fin.prod_univ_succ b, Fin.prod_univ_succ m]
      set P : ℝ := ∏ i : Fin n, a i.succ with hP
      set Q : ℝ := ∏ i : Fin n, b i.succ with hQ
      set M : ℝ := ∏ i : Fin n, m i.succ with hM
      have hP_le : |P| ≤ A ^ n * M := by
        rw [hP, hM]
        exact abs_prod_le (fun i => a i.succ) (fun i => m i.succ) (fun i => ha _)
      have hPQ_le : |P - Q| ≤ n * A ^ (n - 1) * B * M := by
        rw [hP, hQ, hM]
        exact ih (fun i => a i.succ) (fun i => b i.succ) (fun i => m i.succ)
          (fun i => hm _) (fun i => ha _) (fun i => hb _) (fun i => hab _)
      calc
        |a 0 * P - b 0 * Q| = |(a 0 - b 0) * P + b 0 * (P - Q)| := by
          congr 1
          ring
        _ ≤ |(a 0 - b 0) * P| + |b 0 * (P - Q)| := abs_add_le _ _
        _ = |a 0 - b 0| * |P| + |b 0| * |P - Q| := by rw [abs_mul, abs_mul]
        _ ≤ (B * m 0) * (A ^ n * M) + (A * m 0) * ((n : ℝ) * A ^ (n - 1) * B * M) := by
          apply add_le_add
          · exact mul_le_mul (hab 0) hP_le (abs_nonneg _)
              (le_trans (abs_nonneg _) (hab 0))
          · exact mul_le_mul (hb 0) hPQ_le (abs_nonneg _) (mul_nonneg hA (hm 0))
        _ = ((n + 1 : ℕ) : ℝ) * A ^ n * B * (m 0 * M) := prod_succ_bound_eq A B (m 0) M n
        _ = ((n + 1 : ℕ) : ℝ) * A ^ ((n + 1) - 1) * B * (m 0 * M) := by
          rw [Nat.add_sub_cancel]

/-- The Gaussian weights of the coordinates combine:
`|x|²/(s + |x|) ≤ ∑ᵢ xᵢ²/(s + |xᵢ|)`. -/
theorem sq_div_le_sum_sq_div {s : ℝ} (hs : 0 < s) (x : Site d) :
    euclidNorm x ^ 2 / (s + euclidNorm x)
      ≤ ∑ i, ((x i : ℤ) : ℝ) ^ 2 / (s + |((x i : ℤ) : ℝ)|) := by
  have hsum_nonneg : 0 ≤ ∑ i : Fin d, ((x i : ℤ) : ℝ) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hnorm_sq : euclidNorm x ^ 2 = ∑ i : Fin d, ((x i : ℤ) : ℝ) ^ 2 := by
    rw [euclidNorm, Real.sq_sqrt hsum_nonneg]
  rw [hnorm_sq, Finset.sum_div]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have hle : |((x i : ℤ) : ℝ)| ≤ euclidNorm x := by
    apply Real.abs_le_sqrt
    exact Finset.single_le_sum (f := fun j : Fin d => ((x j : ℤ) : ℝ) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  apply div_le_div_of_nonneg_left (sq_nonneg _)
  · positivity
  · linarith

/-- **The local limit theorem for the continuous-time kernel on `ℤ^d`**, with a
Gaussian-weighted error: for `t ≥ 1`,
`|q_t(x) - ḡ_t(x)| ≤ C t^{-(d+2)/2} exp(-c|x|²/(t + |x|))`. -/
theorem exists_abs_ctHeat_sub_ctGauss_le (hd : 1 ≤ d) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ t : ℝ, 1 ≤ t → ∀ x : Site d,
      |ctHeat d t x - ctGauss d t x|
        ≤ C * t ^ (-((d : ℝ) + 2) / 2)
          * Real.exp (-c * euclidNorm x ^ 2 / (t + euclidNorm x)) := by
  obtain ⟨C₀, hC₀, h₀⟩ := exists_abs_lineKernel_sub_lineGauss_le
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set A : ℝ := 1 + C₀ * d with hA
  have hApos : 0 ≤ A := by positivity
  refine ⟨d * A ^ (d - 1) * C₀ * (d : ℝ) ^ (((d : ℝ) + 2) / 2), 1 / 10, by positivity,
    by norm_num, fun t ht x => ?_⟩
  have htpos : 0 < t := by linarith
  set s : ℝ := t / d with hs
  have hspos : 0 < s := div_pos htpos hdpos
  have hsinv : s⁻¹ ≤ d := by
    rw [hs, inv_div, div_le_iff₀ htpos]
    nlinarith
  set E : Fin d → ℝ := fun i =>
    Real.exp (-((x i : ℤ) : ℝ) ^ 2 / (10 * (s + |((x i : ℤ) : ℝ)|)))
    with hE
  set m : Fin d → ℝ := fun i => s ^ (-(1 : ℝ) / 2) * E i with hm
  have hmnn : ∀ i, 0 ≤ m i := fun i => by rw [hm]; positivity
  have h32 : s ^ (-(3 : ℝ) / 2) = s⁻¹ * s ^ (-(1 : ℝ) / 2) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hspos]; norm_num
  have hgauss : ∀ i, |lineGauss s (x i)| ≤ m i := by
    intro i
    have hsq : Real.sqrt s ≤ Real.sqrt (2 * Real.pi * s) :=
      Real.sqrt_le_sqrt (by nlinarith [Real.pi_gt_three])
    have hsqpos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hspos
    rw [lineGauss, abs_of_nonneg (by positivity), hm]
    simp only
    have hhalf : s ^ (-(1 : ℝ) / 2) = (Real.sqrt s)⁻¹ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hspos.le]; norm_num
    rw [hhalf]
    gcongr
    rw [hE]
    simp only
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
      (by nlinarith [abs_nonneg ((x i : ℤ) : ℝ)])
  have hdiff : ∀ i, |lineKernel s (x i) - lineGauss s (x i)| ≤ C₀ / s * m i := by
    intro i
    refine (h₀ s hspos (x i)).trans (le_of_eq ?_)
    rw [h32, hm, hE]
    ring
  have hkernel : ∀ i, |lineKernel s (x i)| ≤ A * m i := by
    intro i
    have h1 : |lineKernel s (x i)| ≤ |lineGauss s (x i)|
        + |lineKernel s (x i) - lineGauss s (x i)| := by
      have := abs_add_le (lineGauss s (x i)) (lineKernel s (x i) - lineGauss s (x i))
      rwa [add_sub_cancel] at this
    have h2 : C₀ / s * m i ≤ C₀ * d * m i := by
      rw [div_eq_mul_inv]
      gcongr
    calc |lineKernel s (x i)| ≤ m i + C₀ * d * m i := h1.trans (add_le_add (hgauss i)
          ((hdiff i).trans h2))
      _ = A * m i := by rw [hA]; ring
  have hprod := abs_prod_sub_prod_le (fun i => lineKernel s (x i)) (fun i => lineGauss s (x i)) m
    hApos hmnn hkernel (fun i => (hgauss i).trans (le_mul_of_one_le_left (hmnn i)
      (by rw [hA]; nlinarith))) hdiff
  have hprodm : ∏ i, m i = s ^ (-(d : ℝ) / 2) * ∏ i, E i := by
    rw [hm, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← Real.rpow_natCast, ← Real.rpow_mul hspos.le]
    congr 2
    ring
  have hprodE : ∏ i, E i ≤ Real.exp (-(1 / 10) * euclidNorm x ^ 2 / (t + euclidNorm x)) := by
    rw [hE, ← Real.exp_sum]
    apply Real.exp_le_exp.mpr
    have hx0 : 0 ≤ euclidNorm x := euclidNorm_nonneg x
    have hsum := sq_div_le_sum_sq_div hspos x
    have hst : s ≤ t := by
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
      rw [hs, div_le_iff₀ hdpos]
      nlinarith
    have h1 : euclidNorm x ^ 2 / (t + euclidNorm x) ≤ euclidNorm x ^ 2 / (s + euclidNorm x) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
    have h2 : ∑ i, -((x i : ℤ) : ℝ) ^ 2 / (10 * (s + |((x i : ℤ) : ℝ)|))
        = -(1 / 10) * ∑ i, ((x i : ℤ) : ℝ) ^ 2 / (s + |((x i : ℤ) : ℝ)|) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp
    rw [h2, mul_div_assoc]
    nlinarith
  have hsd : s ^ (-(1 : ℝ)) * s ^ (-(d : ℝ) / 2)
      = (d : ℝ) ^ (((d : ℝ) + 2) / 2) * t ^ (-((d : ℝ) + 2) / 2) := by
    rw [← Real.rpow_add hspos, hs, Real.div_rpow htpos.le hdpos.le,
      show -(1 : ℝ) + -(d : ℝ) / 2 = -(((d : ℝ) + 2) / 2) by ring,
      Real.rpow_neg hdpos.le, show -((d : ℝ) + 2) / 2 = -(((d : ℝ) + 2) / 2) by ring]
    field_simp
  unfold ctHeat ctGauss
  calc |∏ i, lineKernel s (x i) - ∏ i, lineGauss s (x i)|
      ≤ d * A ^ (d - 1) * (C₀ / s) * ∏ i, m i := hprod
    _ = d * A ^ (d - 1) * C₀ * (s ^ (-(1 : ℝ)) * s ^ (-(d : ℝ) / 2)) * ∏ i, E i := by
        rw [hprodm, Real.rpow_neg_one]; ring
    _ ≤ d * A ^ (d - 1) * C₀ * (s ^ (-(1 : ℝ)) * s ^ (-(d : ℝ) / 2))
          * Real.exp (-(1 / 10) * euclidNorm x ^ 2 / (t + euclidNorm x)) := by gcongr
    _ = _ := by rw [hsd]; ring

end LatticeProb.ContinuousTime
