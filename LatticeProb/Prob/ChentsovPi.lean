/-
The multi-parameter Kolmogorov-Chentsov theorem.

A process indexed by `Fin k → ℝ` (the product sup pseudo-emetric) whose
increments satisfy `∫⁻ edist (X s) (X t) ^ p ≤ M * edist s t ^ q` with
`q > k` has a modification with continuous paths.  The proof is the
k-parameter analogue of the one-parameter chaining in `LatticeProb.Prob.DyadicChain`
and `LatticeProb.Prob.Chentsov`: the level-`n` dyadic grid of the box of
radius `n` in `k` coordinates has `≈ 2 ^ (n k)` points rather than `2 ^ n`,
and it is the comparison of `2 ^ (n k)` with `2 ^ (- n q)` that forces the
exponent condition `k < q`.  Two grid points whose indices differ by one
step in one coordinate are neighbours; a chain between two grid points at
sup-distance `δ` has at most `k` links per level, which is where the factor
`k` enters and nothing else changes.
-/
import Mathlib
import LatticeProb.Prob.Chentsov

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace LatticeProb

section Grid

variable {k : ℕ}

/-- The grid point of level `n` with integer index `j`. -/
def gridPt (n : ℕ) (j : Fin k → ℤ) : Fin k → ℝ := fun i => (j i : ℝ) / 2 ^ n

/-- The coordinatewise dyadic truncation of `z` at level `n`. -/
def dtruncPi (n : ℕ) (z : Fin k → ℝ) : Fin k → ℝ :=
  gridPt n fun i => ⌊z i * 2 ^ n⌋

theorem dtruncPi_eq (n : ℕ) (z : Fin k → ℝ) (i : Fin k) :
    dtruncPi n z i = (⌊z i * 2 ^ n⌋ : ℝ) / 2 ^ n := rfl

theorem dtruncPi_le (n : ℕ) (z : Fin k → ℝ) (i : Fin k) :
    dtruncPi n z i ≤ z i := by
  rw [dtruncPi_eq]
  have h := (Int.floor_le (z i * 2 ^ n) : ((⌊z i * 2 ^ n⌋ : ℤ) : ℝ) ≤ z i * 2 ^ n)
  rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 ^ n)]
  linarith

theorem sub_dtruncPi_lt (n : ℕ) (z : Fin k → ℝ) (i : Fin k) :
    z i - dtruncPi n z i < 1 / 2 ^ n := by
  have h1 : z i * 2 ^ n < ((⌊z i * 2 ^ n⌋ : ℤ) + 1 : ℝ) := by
    have := Int.lt_floor_add_one (z i * 2 ^ n)
    linarith
  have h2 := (Int.floor_le (z i * 2 ^ n) : ((⌊z i * 2 ^ n⌋ : ℤ) : ℝ) ≤ z i * 2 ^ n)
  rw [dtruncPi_eq, lt_div_iff₀ (by positivity : (0:ℝ) < 2 ^ n), sub_mul,
    div_mul_cancel₀ _ (by positivity : (2:ℝ) ^ n ≠ 0)]
  linarith

/-- The level-`(n+1)` index of `x` is twice its level-`n` index, or one more. -/
theorem floor_succ_level_real (n : ℕ) (x : ℝ) :
    ⌊x * 2 ^ (n + 1)⌋ = 2 * ⌊x * 2 ^ n⌋ ∨ ⌊x * 2 ^ (n + 1)⌋ = 2 * ⌊x * 2 ^ n⌋ + 1 := by
  set m := ⌊x * 2 ^ n⌋ with hm
  have hlow : (m : ℝ) ≤ x * 2 ^ n := Int.floor_le _
  have hhigh : x * 2 ^ n < (m : ℝ) + 1 := by
    have := Int.lt_floor_add_one (x * 2 ^ n)
    linarith
  have h1 : 2 * m ≤ ⌊x * 2 ^ (n + 1)⌋ := by
    refine Int.le_floor.mpr ?_
    push_cast
    rw [pow_succ]
    calc (2:ℝ) * m = m * 2 := by ring
      _ ≤ (x * 2 ^ n) * 2 := by gcongr
      _ = x * (2 ^ n * 2) := by ring
  have h2 : ⌊x * 2 ^ (n + 1)⌋ < 2 * m + 2 := by
    rw [Int.floor_lt]
    push_cast
    rw [pow_succ]
    calc x * (2 ^ n * 2) = (x * 2 ^ n) * 2 := by ring
      _ < ((m : ℝ) + 1) * 2 := by gcongr
      _ = (2:ℝ) * m + 2 := by ring
  omega

theorem gridPt_two_mul (n : ℕ) (j : Fin k → ℤ) :
    gridPt (n + 1) (fun i => 2 * j i) = gridPt n j := by
  funext i
  rw [gridPt, gridPt]
  push_cast
  rw [pow_succ]
  ring

theorem dtruncPi_eq_gridPt_two_mul (n : ℕ) (z : Fin k → ℝ) :
    dtruncPi n z = gridPt (n + 1) (fun i => 2 * ⌊z i * 2 ^ n⌋) := by
  funext i
  rw [dtruncPi_eq, gridPt_two_mul]
  rfl

theorem edist_gridPt_step (n : ℕ) (j : Fin k → ℤ) (i : Fin k) :
    edist (gridPt n (j + Pi.single i 1)) (gridPt n j) = ENNReal.ofReal (1 / 2 ^ n) := by
  have hstep : ∀ l : Fin k, gridPt n (j + Pi.single i 1) l
      = gridPt n j l + (if l = i then 1 / 2 ^ n else 0) := by
    intro l
    rw [gridPt, gridPt, Pi.add_apply, Pi.single_apply]
    push_cast
    split
    · ring
    · ring
  have hcoord : ∀ l : Fin k, edist (gridPt n (j + Pi.single i 1) l) (gridPt n j l)
      = ENNReal.ofReal (if l = i then 1 / 2 ^ n else 0) := by
    intro l
    rw [hstep l, edist_dist, Real.dist_eq]
    split_ifs
    · rw [add_sub_cancel_left, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / 2 ^ n)]
    · rw [add_zero, sub_self, abs_zero]
  rw [edist_pi_def]
  refine le_antisymm (Finset.sup_le fun l _ => ?_) ?_
  · rw [hcoord l]
    split_ifs
    · exact le_rfl
    · exact ENNReal.ofReal_le_ofReal (by positivity)
  · refine le_trans ?_ (edist_le_pi_edist _ _ i)
    rw [hcoord i, if_pos rfl]


/-! ### The chaining bound -/

/-- The hypothesis of the chaining argument: every one-step increment of `f`
on the level-`n` grid, inside the box of radius `(n+1) * 2 ^ n` (in grid
units), is at most `a n`. -/
def DyadicIncBoundPi {k : ℕ} (f : (Fin k → ℝ) → ℝ) (a : ℕ → ℝ) (n₀ : ℕ) : Prop :=
  ∀ n, n₀ ≤ n → ∀ (j : Fin k → ℤ), (∀ i, |j i| ≤ (n + 1) * 2 ^ n) → ∀ i : Fin k,
    |f (gridPt n (j + Pi.single i 1)) - f (gridPt n j)| ≤ a n

/-- The index of the chaining path from the level-`n` truncation of `z` to its
level-`(n+1)` truncation: after `m` steps the first `m` coordinates have been
updated. -/
def chainIdx {k : ℕ} (J₀ J₁ : Fin k → ℤ) (m : ℕ) : Fin k → ℤ :=
  fun i => 2 * J₀ i + if i.val < m then J₁ i - 2 * J₀ i else 0

theorem chainIdx_zero {k : ℕ} (J₀ J₁ : Fin k → ℤ) :
    chainIdx J₀ J₁ 0 = fun i => 2 * J₀ i := by
  funext i
  rw [chainIdx]
  simp only [if_neg (Nat.not_lt_zero _)]
  ring

theorem chainIdx_top {k : ℕ} (J₀ J₁ : Fin k → ℤ) :
    chainIdx J₀ J₁ k = J₁ := by
  funext i
  rw [chainIdx]
  simp only [if_pos (Fin.isLt i)]
  ring

theorem chainIdx_succ {k : ℕ} (J₀ J₁ : Fin k → ℤ) {m : ℕ} (hm : m < k) :
    chainIdx J₀ J₁ (m + 1)
      = chainIdx J₀ J₁ m + Pi.single (⟨m, hm⟩ : Fin k) (J₁ ⟨m, hm⟩ - 2 * J₀ ⟨m, hm⟩) := by
  funext i
  simp only [chainIdx, Pi.add_apply, Pi.single_apply]
  by_cases h : i = (⟨m, hm⟩ : Fin k)
  · subst h
    have hval : (⟨m, hm⟩ : Fin k).val = m := Fin.val_mk hm
    split_ifs <;> omega
  · have hval : i.val ≠ m := by
      intro hcon
      exact h (Fin.ext hcon)
    split_ifs <;> omega

theorem chainIdx_range {k : ℕ} (J₀ J₁ : Fin k → ℤ) {n : ℕ} (m : ℕ)
    (hJ₀ : ∀ i, |J₀ i| ≤ n * 2 ^ n) (hstep : ∀ i, |J₁ i - 2 * J₀ i| ≤ 1) :
    ∀ i, |chainIdx J₀ J₁ m i| ≤ 2 * (n * 2 ^ n) + 1 := by
  intro i
  rw [chainIdx]
  split
  · have h1 := hJ₀ i
    have h2 := hstep i
    rw [abs_le] at h1 h2 ⊢
    constructor <;> nlinarith
  · have h1 := hJ₀ i
    rw [abs_le] at h1 ⊢
    constructor <;> nlinarith

theorem floor_range {n : ℕ} {x : ℝ} (hx : |x| ≤ n) :
    |⌊x * 2 ^ n⌋| ≤ n * 2 ^ n := by
  have habs : |x * 2 ^ n| ≤ n * 2 ^ n := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 ^ n)]
    exact mul_le_mul_of_nonneg_right hx (by positivity)
  have habsl := abs_le.mp habs
  have hfl : ⌊(-(n * 2 ^ n : ℝ))⌋ = -(n * 2 ^ n) := by
    have : (-(n * 2 ^ n : ℝ)) = (-(n * 2 ^ n) : ℤ) := by push_cast; ring
    rw [this, Int.floor_intCast]
  have hfr : ⌊(n * 2 ^ n : ℝ)⌋ = n * 2 ^ n := by
    have : (n * 2 ^ n : ℝ) = ((n * 2 ^ n) : ℤ) := by push_cast; ring
    rw [this, Int.floor_intCast]
  rw [abs_le]
  constructor
  · rw [← hfl]
    exact Int.floor_le_floor habsl.1
  · rw [← hfr]
    exact Int.floor_le_floor habsl.2

theorem step_range {n : ℕ} {x : ℝ} (_hx : |x| ≤ n) :
    |⌊x * 2 ^ (n + 1)⌋ - 2 * ⌊x * 2 ^ n⌋| ≤ 1 := by
  rcases floor_succ_level_real n x with h | h <;> rw [h] <;> simp

theorem dtruncPi_step {k : ℕ} {f : (Fin k → ℝ) → ℝ} {a : ℕ → ℝ} {n₀ : ℕ}
    (hb : DyadicIncBoundPi f a n₀) (ha : ∀ n, 0 ≤ a n) {n : ℕ} (hn : n₀ ≤ n + 1)
    {z : Fin k → ℝ} (hz : ∀ i, |z i| ≤ n) :
    |f (dtruncPi (n + 1) z) - f (dtruncPi n z)| ≤ (k : ℝ) * a (n + 1) := by
  set J₀ : Fin k → ℤ := fun i => ⌊z i * 2 ^ n⌋ with hJ₀def
  set J₁ : Fin k → ℤ := fun i => ⌊z i * 2 ^ (n + 1)⌋ with hJ₁def
  have hJ₀ : ∀ i, |J₀ i| ≤ n * 2 ^ n := fun i => floor_range (hz i)
  have hstep : ∀ i, |J₁ i - 2 * J₀ i| ≤ 1 := fun i => step_range (hz i)
  have hkey : ∀ m : ℕ, m ≤ k →
      |f (gridPt (n + 1) (chainIdx J₀ J₁ m)) - f (gridPt (n + 1) (fun i => 2 * J₀ i))|
        ≤ (m : ℝ) * a (n + 1) := by
    intro m
    induction m with
    | zero => intro _; rw [chainIdx_zero]; simp
    | succ m ih =>
      intro hm
      have hmk : m < k := hm
      have ihm := ih (Nat.le_of_succ_le hm)
      have hinc : |f (gridPt (n + 1) (chainIdx J₀ J₁ (m + 1)))
          - f (gridPt (n + 1) (chainIdx J₀ J₁ m))| ≤ a (n + 1) := by
        have hδ : J₁ (⟨m, hmk⟩ : Fin k) - 2 * J₀ (⟨m, hmk⟩ : Fin k) = 0
            ∨ J₁ (⟨m, hmk⟩ : Fin k) - 2 * J₀ (⟨m, hmk⟩ : Fin k) = 1 := by
          rcases floor_succ_level_real n (z (⟨m, hmk⟩ : Fin k)) with h | h
          · left; simp only [hJ₁def, hJ₀def]; omega
          · right; simp only [hJ₁def, hJ₀def]; omega
        rcases hδ with hδ | hδ
        · have hc : chainIdx J₀ J₁ (m + 1) = chainIdx J₀ J₁ m := by
            exact Eq.trans (chainIdx_succ J₀ J₁ hmk) (by rw [hδ, Pi.single_zero]; simp)
          rw [hc, sub_self, abs_zero]
          exact ha (n + 1)
        · have hrange : ∀ i, |chainIdx J₀ J₁ m i| ≤ (n + 2) * 2 ^ (n + 1) := by
            intro i
            have hcr := chainIdx_range J₀ J₁ m hJ₀ hstep i
            have hp : ((n : ℤ) + 2) * 2 ^ (n + 1) = 2 * (n * 2 ^ n) + 4 * 2 ^ n := by
              rw [pow_succ]
              ring
            have h1 : (1 : ℤ) ≤ 4 * 2 ^ n := by
              have h0 : (0 : ℤ) < 2 ^ n := by positivity
              omega
            have h2 : (2 : ℤ) * (n * 2 ^ n) + 1 ≤ (n + 2) * 2 ^ (n + 1) := by
              rw [hp]
              omega
            omega
          have hbb := hb (n + 1) hn (chainIdx J₀ J₁ m) hrange (⟨m, hmk⟩ : Fin k)
          have hc : gridPt (n + 1) (chainIdx J₀ J₁ (m + 1))
              = gridPt (n + 1) (chainIdx J₀ J₁ m + Pi.single (⟨m, hmk⟩ : Fin k) 1) := by
            exact congrArg (gridPt (n + 1)) (Eq.trans (chainIdx_succ J₀ J₁ hmk) (by rw [hδ]))
          rw [hc]
          exact hbb
      have htri : ∀ x y w : ℝ, |x - w| ≤ |x - y| + |y - w| := by
        intro x y w
        have h := dist_triangle x y w
        rwa [Real.dist_eq, Real.dist_eq, Real.dist_eq] at h
      calc |f (gridPt (n + 1) (chainIdx J₀ J₁ (m + 1)))
              - f (gridPt (n + 1) (fun i => 2 * J₀ i))|
          ≤ |f (gridPt (n + 1) (chainIdx J₀ J₁ (m + 1)))
              - f (gridPt (n + 1) (chainIdx J₀ J₁ m))|
            + |f (gridPt (n + 1) (chainIdx J₀ J₁ m))
              - f (gridPt (n + 1) (fun i => 2 * J₀ i))| := htri _ _ _
        _ ≤ a (n + 1) + (m : ℝ) * a (n + 1) := add_le_add hinc ihm
        _ = ((m + 1 : ℕ) : ℝ) * a (n + 1) := by push_cast [Nat.cast_succ]; ring
  have h1 : dtruncPi (n + 1) z = gridPt (n + 1) (chainIdx J₀ J₁ k) := by
    rw [chainIdx_top]
    rfl
  have h2 : dtruncPi n z = gridPt (n + 1) (fun i => 2 * J₀ i) := by
    rw [dtruncPi_eq_gridPt_two_mul]
  rw [h1, h2]
  have hfin := hkey k (Nat.le_refl k)
  linarith


/-- Two points at sup-distance at most `2 ^ (-m)` have level-`m` floor indices
differing by `-1`, `0` or `1` per coordinate. -/
theorem floor_diff_le_one (m : ℕ) {s t : Fin k → ℝ} (hst : ∀ i, |t i - s i| ≤ 1 / 2 ^ m)
    (i : Fin k) : ⌊t i * 2 ^ m⌋ - ⌊s i * 2 ^ m⌋ = 0 ∨ ⌊t i * 2 ^ m⌋ - ⌊s i * 2 ^ m⌋ = 1
    ∨ ⌊t i * 2 ^ m⌋ - ⌊s i * 2 ^ m⌋ = -1 := by
  have habs := hst i
  rw [abs_le] at habs
  have h1 : (s i * 2 ^ m - 1 : ℝ) ≤ t i * 2 ^ m := by
    have h3 : s i - t i ≤ 1 / 2 ^ m := by linarith
    have h4 : (0 : ℝ) < 2 ^ m := by positivity
    have h6 : (1 : ℝ) / 2 ^ m * 2 ^ m = 1 := div_mul_cancel₀ _ (by positivity)
    have h5 : (s i - t i) * 2 ^ m ≤ (1 : ℝ) / 2 ^ m * 2 ^ m := by gcongr
    nlinarith
  have h2 : (t i * 2 ^ m : ℝ) ≤ s i * 2 ^ m + 1 := by
    have h3 : t i - s i ≤ 1 / 2 ^ m := habs.2
    have h4 : (0 : ℝ) < 2 ^ m := by positivity
    have h6 : (1 : ℝ) / 2 ^ m * 2 ^ m = 1 := div_mul_cancel₀ _ (by positivity)
    have h5 : (t i - s i) * 2 ^ m ≤ (1 : ℝ) / 2 ^ m * 2 ^ m := by gcongr
    nlinarith
  have h7 : ⌊s i * 2 ^ m - 1⌋ ≤ ⌊t i * 2 ^ m⌋ := Int.floor_le_floor h1
  have h8 : ⌊t i * 2 ^ m⌋ ≤ ⌊s i * 2 ^ m + 1⌋ := Int.floor_le_floor h2
  have h9 : ⌊s i * 2 ^ m - 1⌋ = ⌊s i * 2 ^ m⌋ - 1 := by
    have := Int.floor_sub_intCast (s i * 2 ^ m) (1 : ℤ)
    rw [Int.cast_one] at this
    exact this
  have h10 : ⌊s i * 2 ^ m + 1⌋ = ⌊s i * 2 ^ m⌋ + 1 := by
    have := Int.floor_add_intCast (s i * 2 ^ m) (1 : ℤ)
    rw [Int.cast_one] at this
    exact this
  rw [h9] at h7
  rw [h10] at h8
  omega

/-- Interpolant between the level-`m` floor indices of `s` and `t`. -/
def closeIdx (Ks Kt : Fin k → ℤ) (m : ℕ) : Fin k → ℤ :=
  fun i => if i.val < m then Kt i else Ks i

theorem closeIdx_zero (Ks Kt : Fin k → ℤ) : closeIdx Ks Kt 0 = Ks := by
  funext i
  simp [closeIdx]

theorem closeIdx_top (Ks Kt : Fin k → ℤ) : closeIdx Ks Kt k = Kt := by
  funext i
  have : i.val < k := i.isLt
  simp [closeIdx, this]

theorem closeIdx_succ (Ks Kt : Fin k → ℤ) {m : ℕ} (hm : m < k) :
    closeIdx Ks Kt (m + 1) = closeIdx Ks Kt m + Pi.single (⟨m, hm⟩ : Fin k) (Kt ⟨m, hm⟩ - Ks ⟨m, hm⟩) := by
  funext i
  by_cases h : i.val < m + 1
  · by_cases him : i.val = m
    · have hieq : i = ⟨m, hm⟩ := Fin.ext him
      subst hieq
      simp [closeIdx]
    · have hlt : i.val < m := by omega
      have hne : i ≠ ⟨m, hm⟩ := by
        intro hieq
        rw [hieq] at him
        simp at him
      simp [closeIdx, h, hlt, hne]
  · have hnm : ¬ i.val < m := by omega
    have hne : i ≠ ⟨m, hm⟩ := by
      intro hieq
      rw [hieq] at h
      simp at h
    simp [closeIdx, h, hnm, hne]

theorem closeIdx_range {B : ℤ} (Ks Kt : Fin k → ℤ) {m : ℕ} (hs : ∀ i, |Ks i| ≤ B)
    (ht : ∀ i, |Kt i| ≤ B) (i : Fin k) : |closeIdx Ks Kt m i| ≤ B := by
  by_cases h : i.val < m
  · simp only [closeIdx, if_pos h]
    exact ht i
  · simp only [closeIdx, if_neg h]
    exact hs i

/-- Two points of the box of radius `m` at sup-distance at most `2 ^ (-m)` have
level-`m` truncations whose `f`-values differ by at most `k * a m`. -/
theorem dtruncPi_close {k : ℕ} {f : (Fin k → ℝ) → ℝ} {a : ℕ → ℝ} {n₀ : ℕ}
    (hb : DyadicIncBoundPi f a n₀) (ha : ∀ n, 0 ≤ a n)
    {m : ℕ} (hm : n₀ ≤ m) {s t : Fin k → ℝ}
    (hs : ∀ i, |s i| ≤ (m : ℝ)) (ht : ∀ i, |t i| ≤ (m : ℝ))
    (hst : ∀ i, |t i - s i| ≤ 1 / 2 ^ m) :
    |f (dtruncPi m t) - f (dtruncPi m s)| ≤ (k : ℝ) * a m := by
  set Ks : Fin k → ℤ := fun i => ⌊s i * 2 ^ m⌋ with hKsdef
  set Kt : Fin k → ℤ := fun i => ⌊t i * 2 ^ m⌋ with hKtdef
  have hKs : ∀ i, |Ks i| ≤ m * 2 ^ m := fun i => floor_range (hs i)
  have hKt : ∀ i, |Kt i| ≤ m * 2 ^ m := fun i => floor_range (ht i)
  have hkey : ∀ j ≤ k, |f (gridPt m (closeIdx Ks Kt j)) - f (gridPt m Ks)| ≤
      (j : ℝ) * a m := by
    intro j
    induction j with
    | zero =>
      intro _
      simp [closeIdx_zero]
    | succ j ihj =>
      intro hjk
      have hjk' : j < k := hjk
      have hrange : ∀ i, |closeIdx Ks Kt j i| ≤ (m + 1) * 2 ^ m := by
        intro i
        have hcr := closeIdx_range (m := j) Ks Kt hKs hKt i
        have hp : ((m : ℤ) + 1) * 2 ^ m = m * 2 ^ m + 2 ^ m := by ring
        have h0 : (0 : ℤ) ≤ 2 ^ m := by positivity
        omega
      have hδ : Kt (⟨j, hjk'⟩ : Fin k) - Ks (⟨j, hjk'⟩ : Fin k) = 0
          ∨ Kt (⟨j, hjk'⟩ : Fin k) - Ks (⟨j, hjk'⟩ : Fin k) = 1
          ∨ Kt (⟨j, hjk'⟩ : Fin k) - Ks (⟨j, hjk'⟩ : Fin k) = -1 := by
        exact floor_diff_le_one m hst (⟨j, hjk'⟩ : Fin k)
      have hc : closeIdx Ks Kt (j + 1) = closeIdx Ks Kt j
          + Pi.single (⟨j, hjk'⟩ : Fin k) (Kt (⟨j, hjk'⟩ : Fin k) - Ks (⟨j, hjk'⟩ : Fin k)) :=
        closeIdx_succ Ks Kt hjk'
      have hinc : |f (gridPt m (closeIdx Ks Kt (j + 1))) - f (gridPt m (closeIdx Ks Kt j))| ≤
          a m := by
        rcases hδ with h0 | h1 | hneg
        · rw [h0] at hc
          have hz : closeIdx Ks Kt j
              + Pi.single (⟨j, hjk'⟩ : Fin k) (0 : ℤ) = closeIdx Ks Kt j := by
            funext i
            simp
          rw [hc, hz, sub_self, abs_zero]
          exact ha m
        · rw [h1] at hc
          have hbb := hb m hm (closeIdx Ks Kt j) hrange (⟨j, hjk'⟩ : Fin k)
          rwa [← hc] at hbb
        · rw [hneg] at hc
          have hrange1 : ∀ i, |closeIdx Ks Kt (j + 1) i| ≤ (m + 1) * 2 ^ m := by
            intro i
            have hcr := closeIdx_range (m := j + 1) Ks Kt hKs hKt i
            have hp : ((m : ℤ) + 1) * 2 ^ m = m * 2 ^ m + 2 ^ m := by ring
            have h0 : (0 : ℤ) ≤ 2 ^ m := by positivity
            omega
          have hbb := hb m hm (closeIdx Ks Kt (j + 1)) hrange1 (⟨j, hjk'⟩ : Fin k)
          have heq : closeIdx Ks Kt (j + 1)
              + Pi.single (⟨j, hjk'⟩ : Fin k) (1 : ℤ) = closeIdx Ks Kt j := by
            rw [hc]
            funext i
            by_cases hii : i = ⟨j, hjk'⟩
            · subst hii
              simp
            · simp [hii]
          rw [heq] at hbb
          rwa [abs_sub_comm] at hbb
      calc |f (gridPt m (closeIdx Ks Kt (j + 1))) - f (gridPt m Ks)|
          ≤ |f (gridPt m (closeIdx Ks Kt (j + 1))) - f (gridPt m (closeIdx Ks Kt j))|
            + |f (gridPt m (closeIdx Ks Kt j)) - f (gridPt m Ks)| := by
              have := dist_triangle (f (gridPt m (closeIdx Ks Kt (j + 1)))) (f (gridPt m (closeIdx Ks Kt j))) (f (gridPt m Ks))
              rwa [Real.dist_eq, Real.dist_eq, Real.dist_eq] at this
        _ ≤ a m + (j : ℝ) * a m := add_le_add hinc (ihj (Nat.le_of_lt hjk'))
        _ = ((j + 1 : ℕ) : ℝ) * a m := by push_cast [Nat.cast_succ]; ring
  have h1 : dtruncPi m t = gridPt m (closeIdx Ks Kt k) := by
    rw [closeIdx_top]
    rfl
  have h2 : dtruncPi m s = gridPt m Ks := by
    rfl
  rw [h1, h2]
  exact hkey k (Nat.le_refl k)

end Grid

end LatticeProb

end
