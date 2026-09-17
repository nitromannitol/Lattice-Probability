/-
The simple random walk kernel on `ℤ^d` and its truncated Green function.

`srwHeat d j` is `P^j(0, ·)`, the law of the walk at time `j` started at the
origin, built as the `j`-th iterate of `LatticeProb.walkOp` on the indicator of
the origin, and `srwGreen d m = ∑_{j < m} srwHeat d j`.  The lazy walk of
`LatticeProb/Walk/Lazy.lean` is a different operator; the simple walk carries a
parity constraint the lazy one does not, and that constraint is what this file
records first: the kernel vanishes off the ball of radius `j`, and inside it
vanishes unless the `ℓ¹` norm of the site agrees with `j` in parity.
-/
import Mathlib
import LatticeProb.Walk.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb

open Finset

variable {d : ℕ}

/-! ### The `ℓ¹` norm of a site -/

/-- The graph distance from the origin: the `ℓ¹` norm of a site. -/
def graphNorm {d : ℕ} (x : Site d) : ℕ := ∑ i, (x i).natAbs

@[simp] theorem graphNorm_zero : graphNorm (0 : Site d) = 0 := by simp [graphNorm]

theorem graphNorm_eq_zero_iff {x : Site d} : graphNorm x = 0 ↔ x = 0 := by
  constructor
  · intro h
    funext i
    have h0 : ∀ j ∈ (univ : Finset (Fin d)), (x j).natAbs = 0 :=
      Finset.sum_eq_zero_iff.mp h
    simpa using Int.natAbs_eq_zero.mp (h0 i (Finset.mem_univ i))
  · rintro rfl; simp

theorem graphNorm_add_le (x y : Site d) :
    graphNorm (x + y) ≤ graphNorm x + graphNorm y := by
  rw [graphNorm, graphNorm, graphNorm, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => Int.natAbs_add_le _ _

theorem graphNorm_neg (x : Site d) : graphNorm (-x) = graphNorm x := by
  simp [graphNorm]

@[simp] theorem graphNorm_dirVec (a : Dir d) : graphNorm (dirVec a) = 1 := by
  classical
  rw [graphNorm]
  rw [Finset.sum_eq_single a.1]
  · cases hb : a.2 <;> simp [dirVec, hb]
  · intro i _ hi; simp [dirVec, hi]
  · intro h; exact absurd (Finset.mem_univ a.1) h

theorem graphNorm_le_succ_of_add_dirVec (x : Site d) (a : Dir d) :
    graphNorm x ≤ graphNorm (x + dirVec a) + 1 := by
  have h := graphNorm_add_le (x + dirVec a) (-dirVec a)
  simpa [graphNorm_neg] using h

/-- An integer and its absolute value agree modulo two. -/
theorem natAbs_cast_zmod (n : ℤ) : ((n.natAbs : ℕ) : ZMod 2) = (n : ZMod 2) := by
  rcases Int.natAbs_eq n with h | h
  · conv_rhs => rw [h]
    rw [Int.cast_natCast]
  · conv_rhs => rw [h]
    rw [Int.cast_neg, Int.cast_natCast, CharTwo.neg_eq]

/-- The `ℓ¹` norm and the sum of the coordinates agree in parity. -/
theorem graphNorm_cast_zmod (x : Site d) :
    ((graphNorm x : ℕ) : ZMod 2) = ((∑ i, x i : ℤ) : ZMod 2) := by
  rw [graphNorm]
  push_cast
  exact Finset.sum_congr rfl fun i _ => natAbs_cast_zmod (x i)

theorem graphNorm_add_dirVec_zmod (x : Site d) (a : Dir d) :
    ((graphNorm (x + dirVec a) : ℕ) : ZMod 2) = ((graphNorm x : ℕ) : ZMod 2) + 1 := by
  classical
  rw [graphNorm_cast_zmod, graphNorm_cast_zmod]
  have hsum : (∑ i, (x + dirVec a) i) = (∑ i, x i) + (∑ i, dirVec a i) := by
    simp [Finset.sum_add_distrib]
  have hd : (∑ i, dirVec a i) = if a.2 then (1 : ℤ) else -1 := by
    rw [Finset.sum_eq_single a.1]
    · cases hb : a.2 <;> simp [dirVec, hb]
    · intro i _ hi; simp [dirVec, hi]
    · intro h; exact absurd (Finset.mem_univ a.1) h
  rw [hsum, hd]
  cases hb : a.2
  · rw [if_neg (by simp)]
    push_cast
    rw [CharTwo.neg_eq]
  · rw [if_pos (by simp)]
    push_cast
    ring

/-! ### The kernel -/

/-- `P^j(0, x)`, the `j`-step transition probability of the simple random walk
started at the origin. -/
noncomputable def srwHeat (d : ℕ) : ℕ → Site d → ℝ
  | 0 => fun x => if x = 0 then 1 else 0
  | j + 1 => fun x => walkOp (srwHeat d j) x

/-- The truncated Green function `g_m(x) = ∑_{j < m} P^j(0, x)`. -/
noncomputable def srwGreen (d : ℕ) (m : ℕ) (x : Site d) : ℝ :=
  ∑ j ∈ Finset.range m, srwHeat d j x

@[simp] theorem srwHeat_zero (x : Site d) :
    srwHeat d 0 x = if x = 0 then 1 else 0 := rfl

@[simp] theorem srwHeat_succ (j : ℕ) (x : Site d) :
    srwHeat d (j + 1) x = walkOp (srwHeat d j) x := rfl

theorem srwHeat_succ_eq_sum_dir (j : ℕ) (x : Site d) :
    srwHeat d (j + 1) x = (∑ a : Dir d, srwHeat d j (x + dirVec a)) / (2 * d) := by
  rw [srwHeat_succ, walkOp_eq_sum_dir]

@[simp] theorem srwGreen_zero (x : Site d) : srwGreen d 0 x = 0 := by simp [srwGreen]

theorem srwGreen_succ (m : ℕ) (x : Site d) :
    srwGreen d (m + 1) x = srwGreen d m x + srwHeat d m x := by
  rw [srwGreen, srwGreen, Finset.sum_range_succ]

theorem srwHeat_nonneg (j : ℕ) (x : Site d) : 0 ≤ srwHeat d j x := by
  induction j generalizing x with
  | zero => by_cases h : x = 0 <;> simp [h]
  | succ j ih =>
      rw [srwHeat_succ_eq_sum_dir]
      exact div_nonneg (Finset.sum_nonneg fun a _ => ih _) (by positivity)

theorem srwGreen_nonneg (m : ℕ) (x : Site d) : 0 ≤ srwGreen d m x :=
  Finset.sum_nonneg fun j _ => srwHeat_nonneg j x

/-- The kernel vanishes outside the ball of radius `j`. -/
theorem srwHeat_eq_zero_of_lt {j : ℕ} {x : Site d} (h : j < graphNorm x) :
    srwHeat d j x = 0 := by
  induction j generalizing x with
  | zero =>
      have hx : x ≠ 0 := fun hx => by simp [hx] at h
      simp [hx]
  | succ j ih =>
      rw [srwHeat_succ_eq_sum_dir]
      have : ∀ a : Dir d, srwHeat d j (x + dirVec a) = 0 := by
        intro a
        refine ih ?_
        have := graphNorm_le_succ_of_add_dirVec x a
        omega
      simp [this]

/-- Inside the ball the kernel still vanishes unless the parity of the `ℓ¹`
norm agrees with the parity of the time. -/
theorem srwHeat_eq_zero_of_parity {j : ℕ} {x : Site d}
    (h : ((graphNorm x : ℕ) : ZMod 2) ≠ ((j : ℕ) : ZMod 2)) : srwHeat d j x = 0 := by
  induction j generalizing x with
  | zero =>
      have hx : x ≠ 0 := by
        rintro rfl
        exact h (by simp)
      simp [hx]
  | succ j ih =>
      rw [srwHeat_succ_eq_sum_dir]
      have : ∀ a : Dir d, srwHeat d j (x + dirVec a) = 0 := by
        intro a
        refine ih ?_
        rw [graphNorm_add_dirVec_zmod]
        intro hcon
        apply h
        push_cast
        rw [← hcon, add_assoc, CharTwo.add_self_eq_zero, add_zero]
      simp [this]

end LatticeProb

namespace LatticeProb

open Finset

/-! ### Dimension one: the exact gradient of the truncated Green function -/

/-- In dimension one the kernel satisfies the nearest-neighbour recursion. -/
theorem srwHeat_one_succ (m : ℕ) (a : ℤ) :
    srwHeat 1 (m + 1) ![a] = (srwHeat 1 m ![a - 1] + srwHeat 1 m ![a + 1]) / 2 := by
  rw [srwHeat_succ_eq_sum_dir]
  have hplus : (![a] : Site 1) + dirVec ((0, true) : Dir 1) = ![a + 1] := by
    funext i
    fin_cases i
    simp [dirVec]
  have hminus : (![a] : Site 1) + dirVec ((0, false) : Dir 1) = ![a - 1] := by
    funext i
    fin_cases i
    simp [dirVec, sub_eq_add_neg]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_one, Fintype.sum_bool]
  rw [hplus, hminus, Nat.cast_one, mul_one, add_comm]

/-- `P_0(X_m > y)`, written as a finite sum; the terms beyond the support of
the kernel are zero. -/
noncomputable def srwTail (m : ℕ) (y : ℤ) : ℝ :=
  ∑ k ∈ Finset.range (m + 1), srwHeat 1 m ![y + 1 + (k : ℤ)]

/-- Lengthening the horizon does not change the tail sum. -/
theorem sum_range_srwHeat_eq (m : ℕ) {y : ℤ} (hy : 0 ≤ y) {N : ℕ} (hN : m + 1 ≤ N) :
    ∑ k ∈ Finset.range N, srwHeat 1 m ![y + 1 + (k : ℤ)] = srwTail m y := by
  rw [srwTail, ← Finset.sum_range_add_sum_Ico _ hN]
  have : ∀ k ∈ Finset.Ico (m + 1) N, srwHeat 1 m ![y + 1 + (k : ℤ)] = 0 := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    refine srwHeat_eq_zero_of_lt ?_
    have hk' : (m : ℤ) + 1 ≤ (k : ℤ) := by exact_mod_cast hk.1
    have hval : (0 : ℤ) ≤ y + 1 + (k : ℤ) := by omega
    have : graphNorm (![y + 1 + (k : ℤ)] : Site 1) = (y + 1 + (k : ℤ)).natAbs := by
      simp [graphNorm]
    rw [this]
    omega
  rw [Finset.sum_eq_zero this, add_zero]

/-- The kernel vanishes past the horizon in dimension one. -/
theorem srwHeat_one_eq_zero_of_gt {m : ℕ} {a : ℤ} (ha : (m : ℤ) < a) :
    srwHeat 1 m ![a] = 0 := by
  refine srwHeat_eq_zero_of_lt ?_
  have : graphNorm (![a] : Site 1) = a.natAbs := by simp [graphNorm]
  rw [this]
  omega

/-- **The exact gradient of the truncated Green function in dimension one.**
For `y ≥ 0`, `g_m(y) - g_m(y+1) = 2 P_0(X_m > y)`. -/
theorem srwGreen_one_sub (m : ℕ) {y : ℤ} (hy : 0 ≤ y) :
    srwGreen 1 m ![y] - srwGreen 1 m ![y + 1] = 2 * srwTail m y := by
  induction m with
  | zero =>
      simp [srwTail, srwHeat_zero]
      intro h
      exfalso
      have : (![y + 1] : Site 1) 0 = 0 := by rw [h]; simp
      simp at this
      omega
  | succ m ih =>
      rw [srwGreen_succ, srwGreen_succ]
      have hstep : srwTail (m + 1) y - srwTail m y =
          (srwHeat 1 m ![y] - srwHeat 1 m ![y + 1]) / 2 := by
        set g : ℕ → ℝ := fun k => srwHeat 1 m ![y + (k : ℤ)] with hg
        have hA : srwTail (m + 1) y
            = ∑ k ∈ Finset.range (m + 3), srwHeat 1 (m + 1) ![y + 1 + (k : ℤ)] :=
          (sum_range_srwHeat_eq (m + 1) hy (by omega)).symm
        have hB : srwTail m y
            = ∑ k ∈ Finset.range (m + 3), srwHeat 1 m ![y + 1 + (k : ℤ)] :=
          (sum_range_srwHeat_eq m hy (by omega)).symm
        rw [hA, hB, ← Finset.sum_sub_distrib]
        have hterm : ∀ k ∈ Finset.range (m + 3),
            srwHeat 1 (m + 1) ![y + 1 + (k : ℤ)] - srwHeat 1 m ![y + 1 + (k : ℤ)]
              = ((g k - g (k + 1)) + (g (k + 2) - g (k + 1))) / 2 := by
          intro k _
          rw [show (y + 1 + (k : ℤ)) = (y + 1 + (k : ℤ)) from rfl]
          have h1 := srwHeat_one_succ m (y + 1 + (k : ℤ))
          rw [h1]
          have e1 : y + 1 + (k : ℤ) - 1 = y + (k : ℤ) := by ring
          have e2 : y + 1 + (k : ℤ) + 1 = y + ((k : ℤ) + 2) := by ring
          have e3 : y + 1 + (k : ℤ) = y + ((k : ℤ) + 1) := by ring
          rw [e1, e2, e3]
          simp only [hg]
          push_cast
          ring
        rw [Finset.sum_congr rfl hterm]
        rw [← Finset.sum_div]
        rw [Finset.sum_add_distrib]
        have hs1 : ∑ k ∈ Finset.range (m + 3), (g k - g (k + 1)) = g 0 - g (m + 3) :=
          Finset.sum_range_sub' g (m + 3)
        have hs2 : ∑ k ∈ Finset.range (m + 3), (g (k + 2) - g (k + 1))
            = g (m + 3 + 1) - g 1 := by
          have := Finset.sum_range_sub (fun k => g (k + 1)) (m + 3)
          simpa using this
        rw [hs1, hs2]
        have hz1 : g (m + 3) = 0 := by
          refine srwHeat_one_eq_zero_of_gt ?_
          push_cast
          omega
        have hz2 : g (m + 3 + 1) = 0 := by
          refine srwHeat_one_eq_zero_of_gt ?_
          push_cast
          omega
        rw [hz1, hz2]
        simp only [hg]
        push_cast
        ring_nf
      have : srwTail (m + 1) y = srwTail m y + (srwHeat 1 m ![y] - srwHeat 1 m ![y + 1]) / 2 := by
        linarith [hstep]
      rw [this]
      linarith [ih]

end LatticeProb
