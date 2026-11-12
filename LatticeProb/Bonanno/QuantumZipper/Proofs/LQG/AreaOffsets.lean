/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.LQG.AreaOffsets at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaOffsetsModulus

/-!
* `ae_hasAreaLimit`: for the free field, almost surely `HasAreaLimit γ (X ω) (qAreaMeasure γ (X ω))`
  (vague convergence on `ℍ`, uniformly in the offset `a ∈ [1,2]`). Same grid-plus-modulus
  argument as `AllOffsets.ae_hasBdryLimit`, on the compacts `K_n` of `ℍ`, at scales
  `2 · 2^{-k} ≤ d_n` where folded circles are genuine circles.
* `ae_isLQGGood`: **almost surely `IsLQGGood γ (X ω)`** (regularity, boundary B4, area B4).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Real Set
open scoped NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace AreaOffsets

open BdryExist GaussTK TwoRadius TwoRadiusC AreaExist AllOffsets GoodSample VagueH

/-! ## Dense family along `goodFilter` -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-! ## Pathwise bound -/

/-! ## Expectation at a fixed level -/

/-! ## Summation over the scales -/

theorem summable_bndβ {β : ℝ} (hβ : 0 < β) {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) :
    Summable (fun k : ℕ => A * θm ^ (⌊β * k / 2⌋₊) +
      (2 ^ (⌊β * k / 2⌋₊) + 1) * (C * exp (-β * (k * log 2)))) := by
  have hlθ : log θm < 0 := log_neg θm_pos θm_lt_one
  have hl2 : 0 < log 2 := log_pos one_lt_two
  set q₁ := exp (β / 2 * log θm) with hq₁
  set q₂ := exp (-(β / 2) * log 2) with hq₂
  have hq₁1 : q₁ < 1 := exp_lt_one_iff.2 (mul_neg_of_pos_of_neg (by positivity) hlθ)
  have hq₂1 : q₂ < 1 := exp_lt_one_iff.2 (by nlinarith)
  have b1 : ∀ k : ℕ, θm ^ (⌊β * k / 2⌋₊) ≤ θm⁻¹ * q₁ ^ k := by
    intro k
    have hk1 : β * k / 2 - 1 < (⌊β * k / 2⌋₊ : ℝ) := by
      have := Nat.lt_floor_add_one (β * k / 2); linarith
    have e1 : θm ^ (⌊β * k / 2⌋₊) = exp ((⌊β * k / 2⌋₊ : ℝ) * log θm) := by
      rw [Real.exp_nat_mul, Real.exp_log θm_pos]
    have e2 : θm⁻¹ * q₁ ^ k = exp ((β * k / 2 - 1) * log θm) := by
      rw [hq₁, ← Real.exp_nat_mul, show θm⁻¹ = exp (-log θm) by rw [exp_neg, exp_log θm_pos],
        ← exp_add]
      congr 1; ring
    rw [e1, e2]
    exact exp_le_exp.2 (by nlinarith)
  have b2 : ∀ k : ℕ, (2 ^ (⌊β * k / 2⌋₊) + 1) * exp (-β * (k * log 2)) ≤ 2 * q₂ ^ k := by
    intro k
    have hk1 : (⌊β * k / 2⌋₊ : ℝ) ≤ β * k / 2 := Nat.floor_le (by positivity)
    have h1 : (1 : ℝ) ≤ 2 ^ (⌊β * k / 2⌋₊) := one_le_pow₀ (by norm_num)
    have e1 : (2 : ℝ) ^ (⌊β * k / 2⌋₊) = exp ((⌊β * k / 2⌋₊ : ℝ) * log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log two_pos]
    have h2 : (2 : ℝ) ^ (⌊β * k / 2⌋₊) * exp (-β * (k * log 2)) ≤ q₂ ^ k := by
      rw [e1, ← exp_add, hq₂, ← Real.exp_nat_mul]
      exact exp_le_exp.2 (by nlinarith)
    calc (2 ^ (⌊β * k / 2⌋₊) + 1) * exp (-β * (k * log 2))
        ≤ (2 * 2 ^ (⌊β * k / 2⌋₊)) * exp (-β * (k * log 2)) :=
          mul_le_mul_of_nonneg_right (by linarith) (exp_pos _).le
      _ = 2 * (2 ^ (⌊β * k / 2⌋₊) * exp (-β * (k * log 2))) := by ring
      _ ≤ 2 * q₂ ^ k := mul_le_mul_of_nonneg_left h2 (by norm_num)
  refine Summable.of_nonneg_of_le (fun k => add_nonneg (mul_nonneg hA (pow_nonneg θm_pos.le _))
    (mul_nonneg (by positivity) (mul_nonneg hC (exp_pos _).le))) (fun k => ?_)
    (((summable_geometric_of_lt_one (exp_pos _).le hq₁1).mul_left (A * θm⁻¹)).add
      ((summable_geometric_of_lt_one (exp_pos _).le hq₂1).mul_left (C * 2)))
  have := θm_pos
  calc A * θm ^ (⌊β * k / 2⌋₊) + (2 ^ (⌊β * k / 2⌋₊) + 1) * (C * exp (-β * (k * log 2)))
      = A * θm ^ (⌊β * k / 2⌋₊) + C * ((2 ^ (⌊β * k / 2⌋₊) + 1) * exp (-β * (k * log 2))) := by
        ring
    _ ≤ A * (θm⁻¹ * q₁ ^ k) + C * (2 * q₂ ^ k) :=
        add_le_add (mul_le_mul_of_nonneg_left (b1 k) hA) (mul_le_mul_of_nonneg_left (b2 k) hC)
    _ = A * θm⁻¹ * q₁ ^ k + C * 2 * q₂ ^ k := by ring

/-! ## Almost sure uniform convergence for the normalized field -/

/-! ## Back to the free field -/

end AreaOffsets
end QuantumZipper
