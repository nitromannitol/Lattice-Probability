/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistGaussianBudgetAlgebra at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistGaussianBudgetReal

 

set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Pt

def ptDistGeometricTwoArmReal
    (q A C Clam : ℝ) (n k₀ : ℕ) : ℝ :=
  let b (k : ℕ) := 2 * A * q ^ k
  let ell (k : ℕ) := C * A * q ^ k
  let term := Clam * A * q ^ n
  let arm := ∑ j ∈ Finset.range (n - k₀),
    (b (k₀ + (j + 1)) + ell (k₀ + (j + 1)) + b (k₀ + j))
  term + arm + (b k₀ + ell k₀ + b k₀) + arm + term

theorem pt_dist_geometric_two_arm_real_le
    (q A C Clam : ℝ) (n k₀ : ℕ) (hkn : k₀ ≤ n)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hClam : 0 ≤ Clam) :
    ptDistGeometricTwoArmReal q A C Clam n k₀ ≤
      A * q ^ k₀ *
        (2 * Clam + 4 + C + 6 * (2 + C) / (1 - q)) := by
  let b (k : ℕ) := 2 * A * q ^ k
  let ell (k : ℕ) := C * A * q ^ k
  let term := Clam * A * q ^ n
  let arm := ∑ j ∈ Finset.range (n - k₀),
    (b (k₀ + (j + 1)) + ell (k₀ + (j + 1)) + b (k₀ + j))
  let S := ∑ j ∈ Finset.range (n - k₀),
    (q ^ (k₀ + (j + 1)) + q ^ (k₀ + (j + 1)) + q ^ (k₀ + j))
  have hqpow : q ^ n ≤ q ^ k₀ := by
    have htail : q ^ (n - k₀) ≤ 1 := pow_le_one₀ hq0 hq1.le
    calc
      q ^ n = q ^ k₀ * q ^ (n - k₀) := by
        rw [← pow_add, Nat.add_sub_of_le hkn]
      _ ≤ q ^ k₀ * 1 :=
        mul_le_mul_of_nonneg_left htail (pow_nonneg hq0 _)
      _ = _ := mul_one _
  have hterm : term ≤ Clam * A * q ^ k₀ := by
    dsimp [term]
    exact mul_le_mul_of_nonneg_left hqpow (mul_nonneg hClam hA)
  have hstep (j : ℕ) :
      b (k₀ + (j + 1)) + ell (k₀ + (j + 1)) + b (k₀ + j) ≤
      (2 + C) * A *
        (q ^ (k₀ + (j + 1)) + q ^ (k₀ + (j + 1)) + q ^ (k₀ + j)) := by
    dsimp [b, ell]
    have hp : 0 ≤ q ^ (k₀ + (j + 1)) := pow_nonneg hq0 _
    have hc : 0 ≤ q ^ (k₀ + j) := pow_nonneg hq0 _
    nlinarith [mul_nonneg (mul_nonneg hC hA) hp,
      mul_nonneg (mul_nonneg hC hA) hc,
      mul_nonneg hA hp]
  have harm : arm ≤ (2 + C) * A * S := by
    dsimp [arm, S]
    calc
      _ ≤ ∑ j ∈ Finset.range (n - k₀),
        (2 + C) * A *
          (q ^ (k₀ + (j + 1)) + q ^ (k₀ + (j + 1)) + q ^ (k₀ + j)) :=
          Finset.sum_le_sum fun j _ => hstep j
      _ = _ := by rw [Finset.mul_sum]
  have hsum : S ≤ 3 * q ^ k₀ / (1 - q) :=
    pt_dist_geometric_arm_le q hq0 hq1 k₀ (n - k₀)
  have hArm : arm ≤ (2 + C) * A *
      (3 * q ^ k₀ / (1 - q)) :=
    harm.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
  change term + arm + (b k₀ + ell k₀ + b k₀) + arm + term ≤ _
  calc
    _ ≤ Clam * A * q ^ k₀ +
        ((2 + C) * A * (3 * q ^ k₀ / (1 - q))) +
        (b k₀ + ell k₀ + b k₀) +
        ((2 + C) * A * (3 * q ^ k₀ / (1 - q))) +
        Clam * A * q ^ k₀ := by
          exact add_le_add
            (add_le_add
              (add_le_add
                (add_le_add hterm hArm) le_rfl) hArm) hterm
    _ = _ := by dsimp [b, ell]; ring

end SupercriticalLQGUniqueness.B2.DG20Pt
