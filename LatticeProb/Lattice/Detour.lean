module

/-
Long injective nearest-neighbour detours that avoid a site while their bounding
rectangle contains it.

Fix a site `x` of `ℤ^d` with `d ≥ 2`, two distinct coordinate directions `i0 ≠ i1`, and a
parameter `R ≥ 1`.  The detour runs along the direction `i0` through the row `x - e_{i1}`,
from `x - R e_{i0} - e_{i1}` to `x + R e_{i0} - e_{i1}`, and then takes one step in the
direction `e_{i1}` to `x + R e_{i0}`.  Its points are pairwise distinct, consecutive points are
nearest neighbours, and no point equals `x`, while the rectangle spanned by the points contains
`x`: the first point lies below `x` in every coordinate and the last point lies above it.

The detour is total in its index: the formula is given for every natural index, and only the
first `2 R + 2` points are used by the statement.
-/
public import Mathlib
public import LatticeProb.Site

@[expose] public section

namespace LatticeProb

open Filter

/-- A power of the logarithm is eventually at most a fifth of the argument: for every real
exponent `γ` there is a threshold `n1` with `5 (log n)^γ ≤ n` for all natural `n ≥ n1`. -/
theorem exists_five_log_rpow_le (γ : ℝ) :
    ∃ n1 : ℕ, ∀ n : ℕ, n1 ≤ n → 5 * Real.log (n : ℝ) ^ γ ≤ (n : ℝ) := by
  have h := isLittleO_log_rpow_rpow_atTop γ (zero_lt_one : (0 : ℝ) < 1)
  have h5 := h.def (by norm_num : (0 : ℝ) < 1 / 5)
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.1 h5
  refine ⟨⌈max X 1⌉₊, fun n hn => ?_⟩
  have hnX : max X 1 ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
  have h1 : (1 : ℝ) ≤ (n : ℝ) := le_trans (le_max_right _ _) hnX
  have h2 := hX (n : ℝ) (le_trans (le_max_left _ _) hnX)
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg h1
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hlog γ),
    Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) 1), Real.rpow_one] at h2
  linarith

variable {d : ℕ}

/-- The coefficient of the first direction in the detour at index `i`, for parameter `R`:
`i - R` on the row `0, …, 2R`, and `R` at the final index. -/
def detourF (R i : ℕ) : ℤ := if i ≤ 2 * R then (i : ℤ) - R else R

/-- The coefficient of the second direction in the detour at index `i`: `-1` on the row,
and `0` at the final index. -/
def detourG (R i : ℕ) : ℤ := if i ≤ 2 * R then -1 else 0

/-- The detour at index `i`: `x + F_i e_{i0} + G_i e_{i1}`. -/
def detour (i0 i1 : Fin d) (x : Site d) (R i : ℕ) : Site d :=
  x + detourF R i • unit i0 + detourG R i • unit i1

theorem detourF_of_le {R i : ℕ} (h : i ≤ 2 * R) : detourF R i = (i : ℤ) - R := by
  simp [detourF, h]

theorem detourF_of_gt {R i : ℕ} (h : ¬ i ≤ 2 * R) : detourF R i = R := by
  simp [detourF, h]

theorem detourG_of_le {R i : ℕ} (h : i ≤ 2 * R) : detourG R i = -1 := by
  simp [detourG, h]

theorem detourG_of_gt {R i : ℕ} (h : ¬ i ≤ 2 * R) : detourG R i = 0 := by
  simp [detourG, h]

theorem detourF_bounds {R i : ℕ} : -(R : ℤ) ≤ detourF R i ∧ detourF R i ≤ R := by
  by_cases h : i ≤ 2 * R
  · rw [detourF_of_le h]
    constructor <;> omega
  · rw [detourF_of_gt h]
    constructor <;> omega

theorem detourG_bounds {R i : ℕ} : -1 ≤ detourG R i ∧ detourG R i ≤ 0 := by
  by_cases h : i ≤ 2 * R
  · rw [detourG_of_le h]
    constructor <;> norm_num
  · rw [detourG_of_gt h]
    constructor <;> norm_num

theorem detour_apply (i0 i1 : Fin d) (x : Site d) (R i : ℕ) (j : Fin d) :
    detour i0 i1 x R i j = x j + detourF R i * (if j = i0 then 1 else 0)
      + detourG R i * (if j = i1 then 1 else 0) := by
  simp [detour, unit, Pi.single_apply]

theorem detour_fst (i0 i1 : Fin d) (hne : i0 ≠ i1) (x : Site d) (R i : ℕ) :
    detour i0 i1 x R i i0 = x i0 + detourF R i := by
  simp [detour_apply, hne]

theorem detour_snd (i0 i1 : Fin d) (hne : i0 ≠ i1) (x : Site d) (R i : ℕ) :
    detour i0 i1 x R i i1 = x i1 + detourG R i := by
  simp [detour_apply, Ne.symm hne]

theorem lattice_adj_of_eq {a b : Site d} {k : Fin d} (h : b = a + unit k) :
    (lattice d).Adj a b := by
  show ∃ k : Fin d, b = a + unit k ∨ a = b + unit k
  exact ⟨k, Or.inl h⟩

theorem detour_succ_fst (i0 i1 : Fin d) (x : Site d) (R i : ℕ) (h : i + 1 ≤ 2 * R) :
    detour i0 i1 x R (i + 1) = detour i0 i1 x R i + unit i0 := by
  have hF : detourF R (i + 1) = detourF R i + 1 := by
    rw [detourF_of_le h, detourF_of_le (by omega : i ≤ 2 * R)]
    push_cast
    ring
  have hG : detourG R (i + 1) = detourG R i := by
    rw [detourG_of_le h, detourG_of_le (by omega : i ≤ 2 * R)]
  simp only [detour, hF, hG, add_smul, one_smul]
  abel

theorem detour_succ_snd (i0 i1 : Fin d) (x : Site d) (R : ℕ) :
    detour i0 i1 x R (2 * R + 1) = detour i0 i1 x R (2 * R) + unit i1 := by
  have hle : ¬ (2 * R + 1 ≤ 2 * R) := by omega
  have hF : detourF R (2 * R + 1) = detourF R (2 * R) := by
    rw [detourF_of_gt hle, detourF_of_le (le_refl (2 * R))]
    push_cast
    ring
  have hG : detourG R (2 * R + 1) = detourG R (2 * R) + 1 := by
    rw [detourG_of_gt hle, detourG_of_le (le_refl (2 * R))]
    norm_num
  simp only [detour, hF, hG, add_smul, one_smul]
  abel

theorem detour_zero_le (i0 i1 : Fin d) (x : Site d) (R : ℕ) (j : Fin d) :
    detour i0 i1 x R 0 j ≤ x j := by
  rw [detour_apply, detourF_of_le (Nat.zero_le (2 * R)),
    detourG_of_le (Nat.zero_le (2 * R))]
  have hR : (0 : ℤ) ≤ R := by positivity
  push_cast
  split_ifs <;> linarith

theorem le_detour_last (i0 i1 : Fin d) (x : Site d) (R : ℕ) (j : Fin d) :
    x j ≤ detour i0 i1 x R (2 * R + 1) j := by
  have hle : ¬ (2 * R + 1 ≤ 2 * R) := by omega
  rw [detour_apply, detourF_of_gt hle, detourG_of_gt hle]
  have hR : (0 : ℤ) ≤ R := by positivity
  split_ifs <;> linarith

theorem detour_ne (i0 i1 : Fin d) (hne : i0 ≠ i1) (x : Site d) (R i : ℕ) (hR : 1 ≤ R) :
    detour i0 i1 x R i ≠ x := by
  intro h
  have hG : detourG R i = 0 := by
    have h1 := congrFun h i1
    rw [detour_snd i0 i1 hne] at h1
    linarith
  by_cases hle : i ≤ 2 * R
  · rw [detourG_of_le hle] at hG
    norm_num at hG
  · have h0 := congrFun h i0
    rw [detour_fst i0 i1 hne, detourF_of_gt hle] at h0
    have hR' : (1 : ℤ) ≤ R := by exact_mod_cast hR
    linarith

/-- **Long detour.**  For `d ≥ 2`, a site `x`, a real exponent `γ`, and a threshold `n0`,
there are an ambient box size `n ≥ n0`, a length `m` with `(log n)^γ ≤ m`, and a total map `z`
whose first `m` points lie in the box `[-n, n]^d`, are pairwise distinct, form a nearest-neighbour
path, avoid `x`, and have a bounding rectangle that contains `x`. -/
theorem exists_long_lattice_path_avoiding_site {d : ℕ} (hd : 2 ≤ d) (x : Site d)
    (γ : ℝ) (n0 : ℕ) :
    ∃ (n m : ℕ) (z : ℕ → Site d), n0 ≤ n ∧ Real.log (n : ℝ) ^ γ ≤ (m : ℝ) ∧
      (∀ i, i < m → ∀ j, |z i j| ≤ (n : ℤ)) ∧
      (∀ i j, i < m → j < m → z i = z j → i = j) ∧
      (∀ i, i + 1 < m → (lattice d).Adj (z i) (z (i + 1))) ∧
      (∀ j, (∃ i, i < m ∧ z i j ≤ x j) ∧ (∃ i, i < m ∧ x j ≤ z i j)) ∧
      (∀ i, i < m → z i ≠ x) := by
  obtain ⟨i0, i1, hne⟩ : ∃ i0 i1 : Fin d, i0 ≠ i1 :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩
  obtain ⟨n1, hn1⟩ := exists_five_log_rpow_le γ
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ j, |x j| ≤ (M : ℤ) := by
    refine ⟨∑ k, (x k).natAbs, fun j => ?_⟩
    have h : (x j).natAbs ≤ ∑ k, (x k).natAbs :=
      Finset.single_le_sum (f := fun k => (x k).natAbs) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ j)
    rw [Int.abs_eq_natAbs]
    exact_mod_cast h
  obtain ⟨R, hR⟩ : ∃ R : ℕ, R = n1 + n0 + M + 2 := ⟨_, rfl⟩
  have hR1 : 1 ≤ R := by omega
  have hnR : R + M + 1 ≤ 2 * R + 2 := by omega
  refine ⟨R + M + 1, 2 * R + 2, detour i0 i1 x R, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : (1 : ℝ) ≤ ((R + M + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ R + M + 1)
    have hnn : 0 ≤ Real.log ((R + M + 1 : ℕ) : ℝ) ^ γ :=
      Real.rpow_nonneg (Real.log_nonneg h1) γ
    have h5 := hn1 (R + M + 1) (by omega)
    have hle : ((R + M + 1 : ℕ) : ℝ) ≤ ((2 * R + 2 : ℕ) : ℝ) := by exact_mod_cast hnR
    linarith
  · intro i _ j
    obtain ⟨hF1, hF2⟩ := detourF_bounds (R := R) (i := i)
    obtain ⟨hG1, hG2⟩ := detourG_bounds (R := R) (i := i)
    obtain ⟨hx1, hx2⟩ := abs_le.mp (hM j)
    rw [detour_apply, abs_le]
    push_cast
    split_ifs <;> constructor <;> linarith
  · intro i j hi hj hij
    have hF : detourF R i = detourF R j := by
      have h0 := congrFun hij i0
      rw [detour_fst i0 i1 hne x R i, detour_fst i0 i1 hne x R j] at h0
      linarith
    have hG : detourG R i = detourG R j := by
      have h1 := congrFun hij i1
      rw [detour_snd i0 i1 hne x R i, detour_snd i0 i1 hne x R j] at h1
      linarith
    simp only [detourF] at hF
    simp only [detourG] at hG
    split_ifs at hF hG <;> omega
  · intro i hi
    by_cases h : i + 1 ≤ 2 * R
    · exact lattice_adj_of_eq (detour_succ_fst i0 i1 x R i h)
    · have hi' : i = 2 * R := by omega
      subst hi'
      exact lattice_adj_of_eq (detour_succ_snd i0 i1 x R)
  · intro j
    exact ⟨⟨0, by omega, detour_zero_le i0 i1 x R j⟩,
      ⟨2 * R + 1, by omega, le_detour_last i0 i1 x R j⟩⟩
  · intro i _
    exact detour_ne i0 i1 hne x R i hR1

end LatticeProb
