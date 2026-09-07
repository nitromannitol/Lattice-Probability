/-
Counting the lattice by sup-norm shells, and the two elementary series the
proof of `lem:gamma-sum` sums over them.

The sum of `lem:gamma-sum` is over the whole lattice, and every summand is a
function of the distance from the origin alone.  The box of radius `r` is a
product of intervals, so it carries `(2r+1)^d` sites, and the shell at radius
`k` carries the difference of two such counts, which is at most
`2d(2k+1)^{d-1}`.  Summing a power `(1+k)^{-p}` against that count is what
turns the pointwise bound `Γ_m(y) ≤ C(1+|y|)^{2-2d}` into a constant when
`d ≥ 3` and into a logarithm when `d = 2`.
-/
import Mathlib
import LatticeProb.Walk.SRW
import LatticeProb.ParticleHoleLemmas

noncomputable section

namespace LatticeProb

open Finset

variable {d : ℕ}

/-- The sup-norm of a lattice site, `|x|_∞ = max_i |x_i|`. -/
def supNorm {d : ℕ} (x : Site d) : ℕ := Finset.univ.sup fun i => (x i).natAbs

/-! ### The box and its cardinality -/

theorem supNorm_le_iff {x : Site d} {r : ℕ} : supNorm x ≤ r ↔ ∀ i, |x i| ≤ (r : ℤ) := by
  unfold supNorm
  rw [Finset.sup_le_iff]
  constructor
  · intro h i
    have h' := h i (Finset.mem_univ i)
    have : ((x i).natAbs : ℤ) ≤ (r : ℤ) := by exact_mod_cast h'
    rwa [Int.abs_eq_natAbs]
  · intro h i _
    have h' := h i
    rw [Int.abs_eq_natAbs] at h'
    exact_mod_cast h'

theorem mem_boxFinset_zero_iff {x : Site d} {r : ℕ} :
    x ∈ boxFinset (0 : Site d) r ↔ supNorm x ≤ r := by
  rw [LatticeProb.mem_boxFinset_iff, supNorm_le_iff]
  simp

theorem card_boxFinset_zero (r : ℕ) :
    (boxFinset (0 : Site d) r).card = (2 * r + 1) ^ d := by
  unfold LatticeProb.boxFinset
  rw [Fintype.card_piFinset]
  have : ∀ i : Fin d, (Finset.Icc ((0 : Site d) i - r) ((0 : Site d) i + r)).card = 2 * r + 1 := by
    intro i
    rw [Int.card_Icc]
    simp
    omega
  rw [Finset.prod_congr rfl fun i _ => this i]
  simp

theorem boxFinset_zero_subset {r s : ℕ} (h : r ≤ s) :
    boxFinset (0 : Site d) r ⊆ boxFinset (0 : Site d) s := by
  intro x hx
  rw [mem_boxFinset_zero_iff] at hx ⊢
  omega

/-- The number of sites at sup-distance exactly `k` from the origin. -/
def shellCard (d k : ℕ) : ℕ := (2 * k + 1) ^ d - (2 * k - 1) ^ d

theorem card_sdiff_box (n : ℕ) :
    ((boxFinset (0 : Site d) (n + 1)) \ (boxFinset (0 : Site d) n)).card
      = shellCard d (n + 1) := by
  rw [Finset.card_sdiff_of_subset (boxFinset_zero_subset (Nat.le_succ n)), card_boxFinset_zero,
    card_boxFinset_zero, shellCard]
  have : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
  rw [this]

theorem supNorm_eq_of_mem_sdiff {n : ℕ} {y : Site d}
    (hy : y ∈ (boxFinset (0 : Site d) (n + 1)) \ (boxFinset (0 : Site d) n)) :
    supNorm y = n + 1 := by
  rw [Finset.mem_sdiff, mem_boxFinset_zero_iff, mem_boxFinset_zero_iff] at hy
  omega

/-- A radial sum over the box of radius `n`, read shell by shell. -/
theorem sum_box_radial (f : ℕ → ℝ) (n : ℕ) :
    ∑ y ∈ boxFinset (0 : Site d) n, f (supNorm y)
      = f 0 + ∑ k ∈ Finset.Icc 1 n, (shellCard d k : ℝ) * f k := by
  induction n with
  | zero =>
      have h0 : boxFinset (0 : Site d) 0 = {0} := by
        ext x
        rw [mem_boxFinset_zero_iff, Finset.mem_singleton]
        constructor
        · intro hx
          funext i
          have h1 : |x i| ≤ ((0 : ℕ) : ℤ) := (supNorm_le_iff.mp hx) i
          have : x i = 0 := by
            rcases abs_le.mp h1 with ⟨h2, h3⟩
            omega
          simpa using this
        · rintro rfl
          simp [supNorm]
      rw [h0]
      have hsup : (Finset.univ.sup fun i : Fin d => ((0 : Site d) i).natAbs) = 0 := by
        simp
      simp only [Finset.sum_singleton, supNorm, hsup]
      norm_num
  | succ n ih =>
      rw [← Finset.sum_sdiff (boxFinset_zero_subset (Nat.le_succ n) (d := d)), ih,
        Finset.sum_Icc_succ_top (Nat.le_add_left 1 n)]
      have hconst : ∑ y ∈ (boxFinset (0 : Site d) (n + 1)) \ (boxFinset (0 : Site d) n),
          f (supNorm y)
          = (shellCard d (n + 1) : ℝ) * f (n + 1) := by
        rw [Finset.sum_congr rfl fun y hy => by rw [supNorm_eq_of_mem_sdiff hy],
          Finset.sum_const, card_sdiff_box, nsmul_eq_mul]
      rw [hconst]
      ring


/-! ### The size of a shell -/

theorem pow_sub_pow_le {a b : ℝ} (hb : 0 ≤ b) (hab : b ≤ a) (n : ℕ) :
    a ^ n - b ^ n ≤ (n : ℝ) * (a - b) * a ^ (n - 1) := by
  have ha : 0 ≤ a := le_trans hb hab
  induction n with
  | zero => simp
  | succ n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · have hpow : a ^ (n - 1) * a = a ^ n := by
          rw [← pow_succ]
          congr 1
          omega
        have h1 : a * (a ^ n - b ^ n) ≤ a * ((n : ℝ) * (a - b) * a ^ (n - 1)) :=
          mul_le_mul_of_nonneg_left ih ha
        have h2 : (a - b) * b ^ n ≤ (a - b) * a ^ n :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb hab n) (by linarith)
        have hexp : a ^ (n + 1) - b ^ (n + 1) = a * (a ^ n - b ^ n) + (a - b) * b ^ n := by
          ring
        have hkey : a * ((n : ℝ) * (a - b) * a ^ (n - 1)) = (n : ℝ) * (a - b) * a ^ n := by
          rw [← hpow]; ring
        have : ((n : ℕ) + 1 : ℝ) * (a - b) * a ^ (n + 1 - 1) = (n : ℝ) * (a - b) * a ^ n
            + (a - b) * a ^ n := by
          simp only [Nat.add_sub_cancel]
          ring
        rw [hexp]
        push_cast
        push_cast at this
        rw [this]
        rw [hkey] at h1
        linarith

theorem shellCard_le (d : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    (shellCard d k : ℝ) ≤ 2 * d * (2 * (k : ℝ) + 1) ^ (d - 1) := by
  have hle : (2 * k - 1) ^ d ≤ (2 * k + 1) ^ d := Nat.pow_le_pow_left (by omega) d
  have hcast : (shellCard d k : ℝ) = ((2 * k + 1 : ℕ) : ℝ) ^ d - ((2 * k - 1 : ℕ) : ℝ) ^ d := by
    rw [shellCard, Nat.cast_sub hle]
    push_cast
    ring
  have hsub : ((2 * k - 1 : ℕ) : ℝ) = 2 * (k : ℝ) - 1 := by
    have : (2 * k - 1 : ℕ) + 1 = 2 * k := by omega
    have := congrArg (fun m : ℕ => (m : ℝ)) this
    push_cast at this
    linarith
  have hadd : ((2 * k + 1 : ℕ) : ℝ) = 2 * (k : ℝ) + 1 := by push_cast; ring
  rw [hcast, hsub, hadd]
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have := pow_sub_pow_le (a := 2 * (k : ℝ) + 1) (b := 2 * (k : ℝ) - 1) (by linarith) (by linarith) d
  calc (2 * (k : ℝ) + 1) ^ d - (2 * (k : ℝ) - 1) ^ d
      ≤ (d : ℝ) * ((2 * (k : ℝ) + 1) - (2 * (k : ℝ) - 1)) * (2 * (k : ℝ) + 1) ^ (d - 1) := this
    _ = 2 * d * (2 * (k : ℝ) + 1) ^ (d - 1) := by ring

/-! ### Two elementary series -/

theorem log_step (j : ℕ) :
    (1 : ℝ) / ((j : ℝ) + 2) ≤ Real.log ((j : ℝ) + 2) - Real.log ((j : ℝ) + 1) := by
  have hlog : Real.log (((j : ℝ) + 1) / ((j : ℝ) + 2)) ≤ ((j : ℝ) + 1) / ((j : ℝ) + 2) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (by positivity) (by positivity)] at hlog
  have hval : ((j : ℝ) + 1) / ((j : ℝ) + 2) - 1 = -(1 / ((j : ℝ) + 2)) := by
    field_simp
    ring
  rw [hval] at hlog
  linarith

theorem sum_inv_succ_le_log (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / ((k : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (Nat.le_add_left 1 n)]
      have hstep := log_step n
      have : ((n : ℝ) + 1 + 1) = ((n : ℝ) + 2) := by ring
      push_cast
      rw [show ((n : ℝ) + 1 + 1) = ((n : ℝ) + 2) by ring]
      linarith

theorem telescope_inv (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, ((1 : ℝ) / (k : ℝ) - 1 / ((k : ℝ) + 1)) = 1 - 1 / ((n : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (Nat.le_add_left 1 n), ih]
      have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      push_cast
      field_simp
      ring

theorem sum_inv_sq_succ_le_one (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / ((k : ℝ) + 1) ^ 2 ≤ 1 := by
  have hterm : ∀ k ∈ Finset.Icc 1 n, (1 : ℝ) / ((k : ℝ) + 1) ^ 2
      ≤ 1 / (k : ℝ) - 1 / ((k : ℝ) + 1) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
    have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
    have h1 : (1 : ℝ) / (k : ℝ) - 1 / ((k : ℝ) + 1) = 1 / ((k : ℝ) * ((k : ℝ) + 1)) := by
      field_simp
      ring
    rw [h1]
    apply one_div_le_one_div_of_le
    · positivity
    · nlinarith
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [telescope_inv]
  have : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
  linarith

/-! ### The sup norm is below the graph norm -/

theorem supNorm_le_graphNorm (x : Site d) : supNorm x ≤ graphNorm x := by
  refine Finset.sup_le fun i _ => ?_
  exact Finset.single_le_sum (f := fun i : Fin d => (x i).natAbs)
    (fun j _ => Nat.zero_le _) (Finset.mem_univ i)

/-! ### The split at the square root -/

theorem sum_inv_sq_Ioc_le {M : ℕ} (hM : 1 ≤ M) (n : ℕ) :
    ∑ k ∈ Finset.Ioc M n, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 1 / (M : ℝ) := by
  rcases le_or_gt n M with hn | hn
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]
    positivity
  · have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    have key : ∀ p : ℕ, M ≤ p →
        ∑ k ∈ Finset.Ioc M p, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 1 / (M : ℝ) - 1 / (p : ℝ) := by
      intro p hp
      induction p, hp using Nat.le_induction with
      | base => simp
      | succ p hp ih =>
          rw [Finset.sum_Ioc_succ_top hp]
          have hpR : (1 : ℝ) ≤ (p : ℝ) := le_trans hMR (by exact_mod_cast hp)
          have hppos : (0 : ℝ) < (p : ℝ) := by linarith
          have hstep : (1 : ℝ) / (((p + 1 : ℕ) : ℝ)) ^ 2 ≤ 1 / (p : ℝ) - 1 / ((p : ℝ) + 1) := by
            have h1 : (1 : ℝ) / (p : ℝ) - 1 / ((p : ℝ) + 1) = 1 / ((p : ℝ) * ((p : ℝ) + 1)) := by
              field_simp
              ring
            rw [h1]
            push_cast
            apply one_div_le_one_div_of_le
            · positivity
            · nlinarith
          have hcast : (((p + 1 : ℕ) : ℝ)) = (p : ℝ) + 1 := by push_cast; ring
          rw [hcast] at hstep ⊢
          linarith
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      have : (1 : ℝ) ≤ (M : ℝ) := hMR
      have : M < n := hn
      have : (0 : ℝ) < (M : ℝ) := by linarith
      have hMn : (M : ℝ) < (n : ℝ) := by exact_mod_cast hn
      linarith
    have := key n (le_of_lt hn)
    have hinv : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
    linarith

theorem sum_min_le_sqrt {n : ℕ} (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Icc 1 n, (min 1 ((n : ℝ) / (k : ℝ) ^ 2)) ^ 2 ≤ 5 * Real.sqrt (n : ℝ) := by
  set M := Nat.sqrt n with hM
  have hM1 : 1 ≤ M := by
    rw [hM]
    exact Nat.le_sqrt.mpr (by simpa using hn)
  have hMn : M ≤ n := Nat.sqrt_le_self n
  have hsplit : ∑ k ∈ Finset.Icc 1 n, (min 1 ((n : ℝ) / (k : ℝ) ^ 2)) ^ 2
      = ∑ k ∈ Finset.Ioc 0 M, (min 1 ((n : ℝ) / (k : ℝ) ^ 2)) ^ 2
        + ∑ k ∈ Finset.Ioc M n, (min 1 ((n : ℝ) / (k : ℝ) ^ 2)) ^ 2 := by
    have hIcc : Finset.Icc 1 n = Finset.Ioc 0 n := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_Ioc]
      omega
    rw [hIcc, Finset.sum_Ioc_consecutive _ (Nat.zero_le M) hMn]
  have hfirst : ∑ k ∈ Finset.Ioc 0 M, (min 1 ((n : ℝ) / (k : ℝ) ^ 2)) ^ 2 ≤ (M : ℝ) := by
    have hterm : ∀ k ∈ Finset.Ioc 0 M, (min 1 ((n : ℝ) / (k : ℝ) ^ 2)) ^ 2 ≤ 1 := by
      intro k _
      have h0 : (0 : ℝ) ≤ min 1 ((n : ℝ) / (k : ℝ) ^ 2) := by
        refine le_min (by norm_num) (by positivity)
      have h1 : min 1 ((n : ℝ) / (k : ℝ) ^ 2) ≤ 1 := min_le_left _ _
      nlinarith
    calc ∑ k ∈ Finset.Ioc 0 M, (min 1 ((n : ℝ) / (k : ℝ) ^ 2)) ^ 2
        ≤ ∑ _k ∈ Finset.Ioc 0 M, (1 : ℝ) := Finset.sum_le_sum hterm
      _ = (M : ℝ) := by
          rw [Finset.sum_const, Nat.card_Ioc]
          simp
  have hsecond : ∑ k ∈ Finset.Ioc M n, (min 1 ((n : ℝ) / (k : ℝ) ^ 2)) ^ 2 ≤ 4 * (M : ℝ) := by
    have hterm : ∀ k ∈ Finset.Ioc M n, (min 1 ((n : ℝ) / (k : ℝ) ^ 2)) ^ 2
        ≤ (n : ℝ) * ((1 : ℝ) / (k : ℝ) ^ 2) := by
      intro k hk
      rw [Finset.mem_Ioc] at hk
      have hkpos : (0 : ℝ) < (k : ℝ) := by
        have : 0 < k := by omega
        exact_mod_cast this
      have h0 : (0 : ℝ) ≤ min 1 ((n : ℝ) / (k : ℝ) ^ 2) := le_min (by norm_num) (by positivity)
      have h1 : min 1 ((n : ℝ) / (k : ℝ) ^ 2) ≤ 1 := min_le_left _ _
      have h2 : min 1 ((n : ℝ) / (k : ℝ) ^ 2) ≤ (n : ℝ) / (k : ℝ) ^ 2 := min_le_right _ _
      have : (min 1 ((n : ℝ) / (k : ℝ) ^ 2)) ^ 2 ≤ min 1 ((n : ℝ) / (k : ℝ) ^ 2) := by
        nlinarith
      calc (min 1 ((n : ℝ) / (k : ℝ) ^ 2)) ^ 2 ≤ min 1 ((n : ℝ) / (k : ℝ) ^ 2) := this
        _ ≤ (n : ℝ) / (k : ℝ) ^ 2 := h2
        _ = (n : ℝ) * ((1 : ℝ) / (k : ℝ) ^ 2) := by ring
    have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
    have hnM : (n : ℝ) ≤ 4 * (M : ℝ) ^ 2 := by
      have h1 : n < (M + 1) * (M + 1) := Nat.lt_succ_sqrt n
      have h2 : (M + 1) * (M + 1) ≤ 4 * (M * M) := by nlinarith
      have : (n : ℝ) ≤ ((4 * (M * M) : ℕ) : ℝ) := by exact_mod_cast le_of_lt (lt_of_lt_of_le h1 h2)
      push_cast at this
      nlinarith
    calc ∑ k ∈ Finset.Ioc M n, (min 1 ((n : ℝ) / (k : ℝ) ^ 2)) ^ 2
        ≤ ∑ k ∈ Finset.Ioc M n, (n : ℝ) * ((1 : ℝ) / (k : ℝ) ^ 2) := Finset.sum_le_sum hterm
      _ = (n : ℝ) * ∑ k ∈ Finset.Ioc M n, (1 : ℝ) / (k : ℝ) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ (n : ℝ) * (1 / (M : ℝ)) := by
          refine mul_le_mul_of_nonneg_left (sum_inv_sq_Ioc_le hM1 n) (by positivity)
      _ ≤ 4 * (M : ℝ) := by
          rw [mul_one_div, div_le_iff₀ hMR]
          nlinarith
  have hMsqrt : (M : ℝ) ≤ Real.sqrt (n : ℝ) := by
    have hMsq : (M : ℝ) ^ 2 ≤ (n : ℝ) := by
      have : M ^ 2 ≤ n := Nat.sqrt_le' n
      have : ((M ^ 2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
      push_cast at this
      nlinarith
    rw [show (M : ℝ) = Real.sqrt ((M : ℝ) ^ 2) by
      rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt hMsq
  rw [hsplit]
  linarith

end LatticeProb

end
