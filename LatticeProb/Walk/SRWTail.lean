/-
Hoeffding's Gaussian bound on the tail of the one-dimensional simple walk.

`srwTail m y` is `P_0(X_m > y)` for the simple walk on `ℤ`.  The bound proved
here is the Chernoff bound with the exact moment generating function of the
walk: the steps are `±1` with equal probability, so
`E_0 e^{θ X_m} = (cosh θ)^m ≤ e^{m θ^2 / 2}`, and at `θ = y / m`,

  `P_0(X_m > y) ≤ e^{-θ y} E_0 e^{θ X_m} ≤ e^{-y^2 / (2m)}`.

The generating function is computed from the nearest-neighbour recursion rather
than from any measure: `srwSum m f`, the kernel at time `m` paired with a test
function, satisfies `srwSum (m+1) f = (srwSum m (f (· + 1)) + srwSum m (f (· - 1)))/2`,
which for `f = e^{θ ·}` is multiplication by `cosh θ`.  The sums are over a box
that contains the support of the kernel, so nothing infinite appears.
-/
import LatticeProb.Walk.SRW

noncomputable section

namespace LatticeProb

open Finset

/-- The kernel of the one-dimensional walk vanishes outside `[-m, m]`. -/
theorem srwHeat_one_eq_zero_of_abs_gt {m : ℕ} {a : ℤ} (h : (m : ℤ) < |a|) :
    srwHeat 1 m ![a] = 0 := by
  refine srwHeat_eq_zero_of_lt ?_
  have hn : graphNorm (![a] : Site 1) = a.natAbs := by simp [graphNorm]
  rw [hn, ← Int.natCast_natAbs] at *
  omega

/-- The kernel at time `m` paired with a test function, over the box that
carries it. -/
def srwSum (m : ℕ) (f : ℤ → ℝ) : ℝ :=
  ∑ a ∈ Finset.Icc (-(m : ℤ)) (m : ℤ), srwHeat 1 m ![a] * f a

/-- Any box containing `[-m, m]` gives the same pairing. -/
theorem sum_eq_srwSum {m : ℕ} {s : Finset ℤ} (hs : Finset.Icc (-(m : ℤ)) (m : ℤ) ⊆ s)
    (f : ℤ → ℝ) : ∑ a ∈ s, srwHeat 1 m ![a] * f a = srwSum m f := by
  refine (Finset.sum_subset hs ?_).symm
  intro a _ ha
  have : (m : ℤ) < |a| := by
    rw [Finset.mem_Icc] at ha
    rcases abs_cases a with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  rw [srwHeat_one_eq_zero_of_abs_gt this, zero_mul]

/-- The pairing over one step of the nearest-neighbour recursion. -/
theorem srwSum_succ (m : ℕ) (f : ℤ → ℝ) :
    srwSum (m + 1) f
      = (srwSum m (fun b => f (b + 1)) + srwSum m (fun b => f (b - 1))) / 2 := by
  have hsplit : srwSum (m + 1) f
      = (∑ a ∈ Finset.Icc (-((m : ℤ) + 1)) ((m : ℤ) + 1), srwHeat 1 m ![a - 1] * f a
          + ∑ a ∈ Finset.Icc (-((m : ℤ) + 1)) ((m : ℤ) + 1), srwHeat 1 m ![a + 1] * f a) / 2 := by
    rw [srwSum]
    push_cast
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [srwHeat_one_succ]
    ring
  have h1 : ∑ a ∈ Finset.Icc (-((m : ℤ) + 1)) ((m : ℤ) + 1), srwHeat 1 m ![a - 1] * f a
      = srwSum m (fun b => f (b + 1)) := by
    have hmap : (Finset.Icc (-((m : ℤ) + 2)) ((m : ℤ))).map (addRightEmbedding (1 : ℤ))
        = Finset.Icc (-((m : ℤ) + 1)) ((m : ℤ) + 1) := by
      rw [Finset.map_add_right_Icc]
      congr 1
    rw [← hmap, Finset.sum_map]
    simp only [addRightEmbedding_apply, add_sub_cancel_right]
    refine sum_eq_srwSum ?_ _
    intro a ha
    rw [Finset.mem_Icc] at ha ⊢
    omega
  have h2 : ∑ a ∈ Finset.Icc (-((m : ℤ) + 1)) ((m : ℤ) + 1), srwHeat 1 m ![a + 1] * f a
      = srwSum m (fun b => f (b - 1)) := by
    have hmap : (Finset.Icc (-((m : ℤ))) ((m : ℤ) + 2)).map (addRightEmbedding (-1 : ℤ))
        = Finset.Icc (-((m : ℤ) + 1)) ((m : ℤ) + 1) := by
      rw [Finset.map_add_right_Icc]
      congr 1 <;> ring
    rw [← hmap, Finset.sum_map]
    simp only [addRightEmbedding_apply]
    have hcast : ∀ a : ℤ, a + -1 + 1 = a := by intro a; ring
    simp only [hcast]
    refine sum_eq_srwSum ?_ _
    intro a ha
    rw [Finset.mem_Icc] at ha ⊢
    omega
  rw [hsplit, h1, h2]

/-- The moment generating function of the one-dimensional walk. -/
theorem srwSum_exp (θ : ℝ) (m : ℕ) :
    srwSum m (fun a => Real.exp (θ * a)) = Real.cosh θ ^ m := by
  induction m with
  | zero =>
      have hset : Finset.Icc (-((0 : ℕ) : ℤ)) ((0 : ℕ) : ℤ) = {0} := by decide
      have h0 : (![(0 : ℤ)] : Site 1) = 0 := by funext i; fin_cases i; rfl
      rw [srwSum, hset, Finset.sum_singleton, srwHeat_zero, h0, if_pos rfl]
      norm_num
  | succ m ih =>
      rw [srwSum_succ]
      have e1 : ∀ b : ℤ, Real.exp (θ * ((b + 1 : ℤ) : ℝ))
          = Real.exp θ * Real.exp (θ * b) := by
        intro b
        rw [← Real.exp_add]
        push_cast
        ring_nf
      have e2 : ∀ b : ℤ, Real.exp (θ * ((b - 1 : ℤ) : ℝ))
          = Real.exp (-θ) * Real.exp (θ * b) := by
        intro b
        rw [← Real.exp_add]
        push_cast
        ring_nf
      have hpull : ∀ c : ℝ, srwSum m (fun b => c * Real.exp (θ * b))
          = c * srwSum m (fun b => Real.exp (θ * b)) := by
        intro c
        rw [srwSum, srwSum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by ring
      simp only [e1, e2]
      rw [hpull, hpull, ih, Real.cosh_eq]
      ring

/-- The tail sum as a sum over the sites beyond `y`. -/
theorem srwTail_eq_sum_Icc (m : ℕ) (y : ℤ) :
    srwTail m y = ∑ a ∈ Finset.Icc (y + 1) (y + 1 + m), srwHeat 1 m ![a] := by
  rw [srwTail]
  refine Finset.sum_nbij' (i := fun k : ℕ => y + 1 + (k : ℤ))
    (j := fun a : ℤ => (a - y - 1).toNat) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_range] at hk
    rw [Finset.mem_Icc]
    omega
  · intro a ha
    rw [Finset.mem_Icc] at ha
    rw [Finset.mem_range]
    omega
  · intro k hk
    rw [Finset.mem_range] at hk
    omega
  · intro a ha
    rw [Finset.mem_Icc] at ha
    omega
  · intro k _
    rfl

/-- **Hoeffding's bound for the one-dimensional simple walk.**
`P_0(X_m > y) ≤ exp(-y^2 / (2m))`. -/
theorem srwTail_le (m : ℕ) (hm : 1 ≤ m) {y : ℤ} (hy : 0 ≤ y) :
    srwTail m y ≤ Real.exp (-((y : ℝ) ^ 2) / (2 * m)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  set θ : ℝ := (y : ℝ) / m with hθ
  have hθ0 : 0 ≤ θ := div_nonneg (by exact_mod_cast hy) (le_of_lt hm0)
  -- the Chernoff step
  have hchernoff : srwTail m y
      ≤ Real.exp (-(θ * y)) * srwSum m (fun a => Real.exp (θ * a)) := by
    have hbox : Finset.Icc (-(m : ℤ)) (m : ℤ) ⊆ Finset.Icc (-(m : ℤ)) (y + 1 + m) := by
      intro a ha
      rw [Finset.mem_Icc] at ha ⊢
      omega
    have hsub : Finset.Icc (y + 1) (y + 1 + m) ⊆ Finset.Icc (-(m : ℤ)) (y + 1 + m) := by
      intro a ha
      rw [Finset.mem_Icc] at ha ⊢
      omega
    have hrhs : Real.exp (-(θ * y)) * srwSum m (fun a => Real.exp (θ * a))
        = ∑ a ∈ Finset.Icc (-(m : ℤ)) (y + 1 + m),
            srwHeat 1 m ![a] * Real.exp (θ * ((a : ℝ) - y)) := by
      rw [sum_eq_srwSum hbox (fun a => Real.exp (θ * ((a : ℝ) - y))), srwSum, srwSum,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← mul_assoc, mul_comm (Real.exp (-(θ * y))), mul_assoc, ← Real.exp_add]
      ring_nf
    rw [hrhs, srwTail_eq_sum_Icc]
    refine le_trans (Finset.sum_le_sum ?_) (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_)
    · intro a ha
      rw [Finset.mem_Icc] at ha
      have h1 : (1 : ℝ) ≤ Real.exp (θ * ((a : ℝ) - y)) := by
        refine Real.one_le_exp ?_
        have : (y : ℝ) + 1 ≤ (a : ℝ) := by exact_mod_cast ha.1
        nlinarith
      nlinarith [srwHeat_nonneg (d := 1) m ![a]]
    · intro a _ _
      exact mul_nonneg (srwHeat_nonneg _ _) (Real.exp_nonneg _)
  -- the moment generating function
  have hmgf : srwSum m (fun a => Real.exp (θ * a)) ≤ Real.exp (m * θ ^ 2 / 2) := by
    rw [srwSum_exp]
    calc Real.cosh θ ^ m ≤ Real.exp (θ ^ 2 / 2) ^ m :=
          pow_le_pow_left₀ (le_of_lt (Real.cosh_pos θ)) (Real.cosh_le_exp_half_sq θ) m
      _ = Real.exp (m * θ ^ 2 / 2) := by
          rw [← Real.exp_nat_mul]
          ring_nf
  have hfinal : Real.exp (-(θ * y)) * Real.exp ((m : ℝ) * θ ^ 2 / 2)
      = Real.exp (-((y : ℝ) ^ 2) / (2 * m)) := by
    rw [← Real.exp_add]
    congr 1
    have hmne : (m : ℝ) ≠ 0 := ne_of_gt hm0
    rw [hθ]
    field_simp
    ring
  calc srwTail m y ≤ Real.exp (-(θ * y)) * srwSum m (fun a => Real.exp (θ * a)) := hchernoff
    _ ≤ Real.exp (-(θ * y)) * Real.exp ((m : ℝ) * θ ^ 2 / 2) := by
        exact mul_le_mul_of_nonneg_left hmgf (Real.exp_nonneg _)
    _ = Real.exp (-((y : ℝ) ^ 2) / (2 * m)) := hfinal

end LatticeProb

end
