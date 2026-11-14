/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistRateSum at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistRateLinear

 


set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_rate_sum_large (a α : ℝ) (ha : 0 < a) (hα : 0 < α) :
    ∃ H : ℝ, 3 ≤ H ∧
      ∀ L : ℝ, H ≤ L → ∀ n : ℕ,
        ∑ k ∈ Finset.range n,
          (4 : ℝ) ^ k * Real.exp
            (-a * ((L + α * (k : ℝ)) ^ 2 /
              Real.log (L + α * (k : ℝ)))) ≤
        2 * Real.exp (-(a / 2) * (L ^ 2 / Real.log L)) := by
  obtain ⟨H, hH, hboost⟩ := pt_dist_rate_boost_large a α ha hα
  refine ⟨H, hH, ?_⟩
  intro L hL n
  have hstep (k : ℕ) :
      (4 : ℝ) ^ k * Real.exp
        (-a * ((L + α * (k : ℝ)) ^ 2 /
          Real.log (L + α * (k : ℝ)))) ≤
      (1 / 2 : ℝ) ^ k *
        Real.exp (-(a / 2) * (L ^ 2 / Real.log L)) := by
    have hr := hboost L hL k
    have he : Real.exp (Real.log 8 * (k : ℝ)) = (8 : ℝ) ^ k := by
      rw [mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num)]
    calc
      (4 : ℝ) ^ k * Real.exp
          (-a * ((L + α * (k : ℝ)) ^ 2 /
            Real.log (L + α * (k : ℝ)))) ≤
        (4 : ℝ) ^ k * Real.exp
          (-((a / 2) * (L ^ 2 / Real.log L) +
            Real.log 8 * (k : ℝ))) := by
          apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
          positivity
      _ = (4 : ℝ) ^ k *
          (Real.exp (-(a / 2) * (L ^ 2 / Real.log L)) *
            Real.exp (-(Real.log 8 * (k : ℝ)))) := by
          rw [← Real.exp_add]
          congr 1
          ring_nf
      _ = (4 : ℝ) ^ k *
          (Real.exp (-(a / 2) * (L ^ 2 / Real.log L)) *
            ((8 : ℝ) ^ k)⁻¹) := by rw [Real.exp_neg, he]
      _ = (1 / 2 : ℝ) ^ k *
          Real.exp (-(a / 2) * (L ^ 2 / Real.log L)) := by
          have hp : (4 : ℝ) ^ k / (8 : ℝ) ^ k = (1 / 2 : ℝ) ^ k := by
            rw [← div_pow]
            norm_num
          calc
            _ = ((4 : ℝ) ^ k / (8 : ℝ) ^ k) *
                Real.exp (-(a / 2) * (L ^ 2 / Real.log L)) := by ring
            _ = _ := by rw [hp]
  calc
    ∑ k ∈ Finset.range n,
        (4 : ℝ) ^ k * Real.exp
          (-a * ((L + α * (k : ℝ)) ^ 2 /
            Real.log (L + α * (k : ℝ)))) ≤
      ∑ k ∈ Finset.range n,
        (1 / 2 : ℝ) ^ k *
          Real.exp (-(a / 2) * (L ^ 2 / Real.log L)) :=
        Finset.sum_le_sum fun k _ => hstep k
    _ = (∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ k) *
        Real.exp (-(a / 2) * (L ^ 2 / Real.log L)) := by
          rw [Finset.sum_mul]
    _ ≤ 2 * Real.exp (-(a / 2) * (L ^ 2 / Real.log L)) :=
      mul_le_mul_of_nonneg_right (sum_geometric_two_le n) (Real.exp_nonneg _)

 
theorem pt_dist_gaussian_sum_large (b β : ℝ) (hb : 0 < b) (hβ : 0 < β) :
    ∃ H : ℝ, 0 < H ∧
      ∀ L : ℝ, H ≤ L → ∀ n : ℕ,
        ∑ k ∈ Finset.range n,
          (4 : ℝ) ^ k * Real.exp
            (-b * (L + β * (k : ℝ)) ^ 2) ≤
        2 * Real.exp (-(b / 2) * L ^ 2) := by
  let H : ℝ := max 1 (Real.log 8 / (b * β))
  have hH : 0 < H := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨H, hH, ?_⟩
  intro L hL n
  have hL0 : 0 ≤ L := by
    have hh : (1 : ℝ) ≤ L := (le_max_left _ _).trans hL
    linarith
  have hLlarge : Real.log 8 ≤ b * β * L := by
    have hh : Real.log 8 / (b * β) ≤ L := (le_max_right _ _).trans hL
    simpa only [mul_comm L] using
      (div_le_iff₀ (by positivity : 0 < b * β)).mp hh
  have hstep (k : ℕ) :
      (4 : ℝ) ^ k * Real.exp (-b * (L + β * (k : ℝ)) ^ 2) ≤
      (1 / 2 : ℝ) ^ k * Real.exp (-(b / 2) * L ^ 2) := by
    have hk : (b / 2) * L ^ 2 + Real.log 8 * (k : ℝ) ≤
        b * (L + β * (k : ℝ)) ^ 2 := by
      have hkn : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
      have hbk : Real.log 8 * (k : ℝ) ≤ b * β * L * (k : ℝ) :=
        mul_le_mul_of_nonneg_right hLlarge hkn
      nlinarith [sq_nonneg (β * (k : ℝ)),
        mul_nonneg (mul_nonneg hb.le hL0) (mul_nonneg hβ.le hkn)]
    have he : Real.exp (Real.log 8 * (k : ℝ)) = (8 : ℝ) ^ k := by
      rw [mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num)]
    calc
      (4 : ℝ) ^ k * Real.exp (-b * (L + β * (k : ℝ)) ^ 2) ≤
          (4 : ℝ) ^ k * Real.exp
            (-((b / 2) * L ^ 2 + Real.log 8 * (k : ℝ))) := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
        positivity
      _ = (4 : ℝ) ^ k *
          (Real.exp (-(b / 2) * L ^ 2) *
            Real.exp (-(Real.log 8 * (k : ℝ)))) := by
        rw [← Real.exp_add]
        congr 1
        ring_nf
      _ = (4 : ℝ) ^ k *
          (Real.exp (-(b / 2) * L ^ 2) * ((8 : ℝ) ^ k)⁻¹) := by
        rw [Real.exp_neg, he]
      _ = (1 / 2 : ℝ) ^ k * Real.exp (-(b / 2) * L ^ 2) := by
        have hp : (4 : ℝ) ^ k / (8 : ℝ) ^ k = (1 / 2 : ℝ) ^ k := by
          rw [← div_pow]
          norm_num
        calc
          _ = ((4 : ℝ) ^ k / (8 : ℝ) ^ k) *
              Real.exp (-(b / 2) * L ^ 2) := by ring
          _ = _ := by rw [hp]
  calc
    ∑ k ∈ Finset.range n, (4 : ℝ) ^ k *
        Real.exp (-b * (L + β * (k : ℝ)) ^ 2) ≤
      ∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ k *
        Real.exp (-(b / 2) * L ^ 2) :=
        Finset.sum_le_sum fun k _ => hstep k
    _ = (∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ k) *
        Real.exp (-(b / 2) * L ^ 2) := by rw [Finset.sum_mul]
    _ ≤ 2 * Real.exp (-(b / 2) * L ^ 2) :=
      mul_le_mul_of_nonneg_right (sum_geometric_two_le n) (Real.exp_nonneg _)

end SupercriticalLQGUniqueness.B2.DG20Pt
