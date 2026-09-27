import LatticeProb.Site
import LatticeProb.Network.KilledGreen
import LatticeProb.Graph.Zd
import LatticeProb.Network.MaximumPrinciple
import LatticeProb.Walk.SRW
import LatticeProb.Walk.GreenTwoSided
import LatticeProb.Walk.Harnack.G3_GreenEstimates

/-!
# Small R and the Harnack inequality

The Harnack inequality for `R ≥ 4` (`le_mul_of_nonneg_harmonicOn`), from the shell representation
and the Green-function comparison; a neighbour-chaining bound `u x ≤ (2d)^{2Rd} u y` valid for
every `R ≥ 1`, used to cover the small-`R` cases; and the final theorem `harnack`, combining both
regimes.
-/

open Finset
open scoped Classical

namespace LatticeProb

variable {d : ℕ}

/-! ### Small `R`: chaining the one-step bound -/

-- 2d u x = nbrSum u x = ∑_j (u(x+e_j) + u(x-e_j)); every term ≥ 0 (neighbours lie in box (2R-1+1)
-- = box (2R) by unit_add_sub_mem_box_succ, omega using 1 ≤ R); Finset.single_le_sum at j = i, then
-- le_add_of_nonneg_right / le_add_of_nonneg_left.
/-- Each unit-neighbour value `u (x ± unit i)` is at most `2d * u x`, since `2d * u x` is a sum
of nonnegative neighbour values including that term. -/
private theorem le_two_mul_mul_of_add_unit {R : ℕ} (hR : 1 ≤ R) (u : Site d → ℝ)
    (hpos : ∀ x ∈ box d (2 * R), 0 ≤ u x)
    (hharm : ∀ x ∈ box d (2 * R - 1), nbrSum u x = 2 * (d : ℝ) * u x)
    {x : Site d} (hx : x ∈ box d (2 * R - 1)) (i : Fin d) :
    u (x + unit i) ≤ 2 * (d : ℝ) * u x ∧ u (x - unit i) ≤ 2 * (d : ℝ) * u x := by
  have hR2 : 2 * R - 1 + 1 = 2 * R := Nat.sub_add_cancel (by omega)
  have key : u (x + unit i) + u (x - unit i) ≤ 2 * (d : ℝ) * u x := by
    have hle := Finset.single_le_sum (s := (Finset.univ : Finset (Fin d)))
      (f := fun i' : Fin d => u (x + unit i') + u (x - unit i'))
      (fun i' _ => by
        obtain ⟨h1, h2⟩ := unit_add_sub_mem_box_succ (2 * R - 1) x i' hx
        rw [hR2] at h1 h2
        exact add_nonneg (hpos _ h1) (hpos _ h2))
      (Finset.mem_univ i)
    have hle' : u (x + unit i) + u (x - unit i) ≤ nbrSum u x := by
      simpa [nbrSum] using hle
    simpa [hharm x hx] using hle'
  obtain ⟨h1, h2⟩ := unit_add_sub_mem_box_succ (2 * R - 1) x i hx
  rw [hR2] at h1 h2
  exact ⟨by linarith [key, hpos _ h2], by linarith [key, hpos _ h1]⟩


-- Finset.add_sum_erase at i on both sums; off i the summands agree (Finset.sum_congr,
-- Finset.ne_of_mem_erase); at i use hi; omega.
/-- If `x'` agrees with `x` off coordinate `i` and its `i`-th distance to `y` is one less, then
`∑_j |x'_j - y_j| + 1 = ∑_j |x_j - y_j|`. -/
private theorem sum_natAbs_succ_eq_of_ne {x' x y : Site d} (i : Fin d)
    (hoff : ∀ j, j ≠ i → x' j = x j)
    (hi : (x' i - y i).natAbs + 1 = (x i - y i).natAbs) :
    (∑ j, (x' j - y j).natAbs) + 1 = ∑ j, (x j - y j).natAbs := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have h : ∑ j ∈ Finset.univ.erase i, (x' j - y j).natAbs
      = ∑ j ∈ Finset.univ.erase i, (x j - y j).natAbs :=
    Finset.sum_congr rfl fun j hj => by rw [hoff j (Finset.ne_of_mem_erase hj)]
  rw [h]
  omega

-- Stepping coordinate i toward y i keeps x in box R: coordinates j ≠ i unchanged
-- (Pi.single_eq_of_ne), coordinate i moves strictly between x i and y i (abs_le, omega).
/-- Stepping coordinate `i` of `x` up toward `y` keeps the result in `box d R`, when `x_i < y_i`. -/
private theorem add_unit_mem_box_of_lt {R : ℕ} {x y : Site d} (hx : x ∈ box d R) (hy : y ∈ box d R)
    {i : Fin d}
    (h : x i < y i) : x + unit i ∈ box d R := by
  intro j
  rcases eq_or_ne j i with rfl | hji
  · have h1 := abs_le.mp (hx j)
    have h2 := abs_le.mp (hy j)
    simp only [Pi.add_apply, unit, Pi.single_eq_same]
    rw [abs_le]
    constructor <;> omega
  · simp only [Pi.add_apply, unit, Pi.single_eq_of_ne hji, add_zero]
    exact hx j

-- Same as add_unit_mem_box_of_lt with x - unit i.
/-- Stepping coordinate `i` of `x` down toward `y` keeps the result in `box d R`, when `y_i <
x_i`. -/
private theorem sub_unit_mem_box_of_lt {R : ℕ} {x y : Site d} (hx : x ∈ box d R) (hy : y ∈ box d R)
    {i : Fin d}
    (h : y i < x i) : x - unit i ∈ box d R := by
  intro j
  rcases eq_or_ne j i with rfl | hji
  · have h1 := abs_le.mp (hx j)
    have h2 := abs_le.mp (hy j)
    simp only [Pi.sub_apply, unit, Pi.single_eq_same]
    rw [abs_le]
    constructor <;> omega
  · simp only [Pi.sub_apply, unit, Pi.single_eq_of_ne hji, sub_zero]
    exact hx j

-- Pick i with x i ≠ y i (Function.funext_iff).  If y i < x i take x' := x - unit i (x = x' + unit
-- i),
-- else x' := x + unit i (x = x' - unit i).  x' ∈ box R coordinatewise (unit, Pi.single_apply,
-- abs_le,
-- omega).  Distance: Finset.add_sum_erase at i on both sums; off i the summands agree
-- (Pi.single_eq_of_ne), at i natAbs drops by one (omega).  SPLIT?
/-- For `x ≠ y` in `box d R`, there is a neighbour `x'` of `x` in `box d R`, reached by a single
step toward `y`, whose `L¹` distance to `y` is one less than that of `x`. -/
private theorem exists_step_sum_natAbs_add_one_eq {R : ℕ} {x y : Site d} (hx : x ∈ box d R)
    (hy : y ∈ box d R)
    (hxy : x ≠ y) :
    ∃ x' ∈ box d R, ∃ i : Fin d, (x = x' + unit i ∨ x = x' - unit i) ∧
      (∑ j, (x' j - y j).natAbs) + 1 = ∑ j, (x j - y j).natAbs := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
    by_contra h
    exact hxy (funext fun j => by by_contra hj; exact h ⟨j, hj⟩)
  rcases lt_or_gt_of_ne hi with h | h
  · refine ⟨x + unit i, add_unit_mem_box_of_lt hx hy h, i,
      Or.inr (add_sub_cancel_right x (unit i)).symm, sum_natAbs_succ_eq_of_ne i ?_ ?_⟩
    · intro j hji
      simp [unit, Pi.single_eq_of_ne hji]
    · simp only [Pi.add_apply, unit, Pi.single_eq_same]
      omega
  · refine ⟨x - unit i, sub_unit_mem_box_of_lt hx hy h, i,
      Or.inl (sub_add_cancel x (unit i)).symm, sum_natAbs_succ_eq_of_ne i ?_ ?_⟩
    · intro j hji
      simp [unit, Pi.single_eq_of_ne hji]
    · simp only [Pi.sub_apply, unit, Pi.single_eq_same]
      omega

-- Induction on n generalizing x.  n = 0: all natAbs are 0 (Finset.sum_eq_zero_iff), so x = y
-- (funext, Int.natAbs_eq_zero, sub_eq_zero); pow_zero, one_mul.  n + 1: x ≠ y (else sum 0);
-- exists_step_sum_natAbs_add_one_eq gives x'; u x ≤ 2d u x' by le_two_mul_mul_of_add_unit at x' (x'
-- ∈ box (2R-1) via
-- mem_box_of_le, omega); IH at x'; pow_succ, mul_le_mul_of_nonneg_left (0 ≤ 2d).
/-- If the `L¹` distance from `x` to `y` is `n+1`, then `x ≠ y`. -/
private theorem ne_of_sum_natAbs_eq_succ {d : ℕ} {n : ℕ} {x y : Site d}
    (h : ∑ j, (x j - y j).natAbs = n + 1) : x ≠ y := by
  intro hxy
  rw [hxy] at h
  simp at h

/-- `a * (a^n * t) = a^{n+1} * t`. -/
private theorem mul_pow_mul_eq_pow_succ_mul (a t : ℝ) (n : ℕ) : a * (a ^ n * t) = a ^ (n + 1) * t :=
    by
  rw [pow_succ]; ring

/-- The neighbour chain bound: `u x ≤ (2d)^n * u y` whenever `x, y ∈ box d R` are at `L¹`
distance `n`, by induction along `exists_step_sum_natAbs_add_one_eq`. -/
private theorem le_two_mul_pow_mul_of_sum_natAbs_eq {R : ℕ} (hR : 1 ≤ R) (u : Site d → ℝ)
    (hpos : ∀ x ∈ box d (2 * R), 0 ≤ u x)
    (hharm : ∀ x ∈ box d (2 * R - 1), nbrSum u x = 2 * (d : ℝ) * u x) :
    ∀ (n : ℕ) (x y : Site d), x ∈ box d R → y ∈ box d R →
      ∑ j, (x j - y j).natAbs = n → u x ≤ (2 * (d : ℝ)) ^ n * u y := by
  intro n x y hx hy hsum
  revert x y
  induction n with
  | zero =>
    intro x y hx hy hsum
    have hxy : x = y := funext fun j => by
      have hle : (x j - y j).natAbs ≤ ∑ i : Fin d, (x i - y i).natAbs :=
        Finset.single_le_sum (f := fun i : Fin d => (x i - y i).natAbs)
          (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
      rw [hsum] at hle
      have h0 : (x j - y j).natAbs = 0 := Nat.le_zero.mp hle
      exact sub_eq_zero.mp (Int.natAbs_eq_zero.mp h0)
    rw [hxy, pow_zero, one_mul]
  | succ n ih =>
    intro x y hx hy hsum
    have hne : x ≠ y := ne_of_sum_natAbs_eq_succ hsum
    obtain ⟨x', hx', i, hstep, hsum'⟩ := exists_step_sum_natAbs_add_one_eq hx hy hne
    have hx'B : x' ∈ box d (2 * R - 1) := mem_box_of_le (by omega) hx'
    have hih : u x' ≤ (2 * (d : ℝ)) ^ n * u y := ih x' y hx' hy (by omega)
    rcases hstep with h | h
    · rw [h]
      calc u (x' + unit i) ≤ 2 * (d : ℝ) * u x' :=
          (le_two_mul_mul_of_add_unit hR u hpos hharm hx'B i).1
        _ ≤ 2 * (d : ℝ) * ((2 * (d : ℝ)) ^ n * u y) := mul_le_mul_of_nonneg_left hih (by positivity)
        _ = (2 * (d : ℝ)) ^ (n + 1) * u y := mul_pow_mul_eq_pow_succ_mul (2 * (d : ℝ)) (u y) n
    · rw [h]
      calc u (x' - unit i) ≤ 2 * (d : ℝ) * u x' :=
          (le_two_mul_mul_of_add_unit hR u hpos hharm hx'B i).2
        _ ≤ 2 * (d : ℝ) * ((2 * (d : ℝ)) ^ n * u y) := mul_le_mul_of_nonneg_left hih (by positivity)
        _ = (2 * (d : ℝ)) ^ (n + 1) * u y := mul_pow_mul_eq_pow_succ_mul (2 * (d : ℝ)) (u y) n


-- Finset.sum_le_card_nsmul with bound 2R per coordinate (|x j - y j| ≤ |x j| + |y j| ≤ 2R:
-- abs_le, omega on natAbs via Int.natAbs_le / Int.ofNat_le); Finset.card_univ, Fintype.card_fin,
-- smul_eq_mul; nlinarith/ring_nf for d * (2R) = 2 * R * d.
/-- The `L¹` distance between two points of `box d R` is at most `2Rd`. -/
private theorem sum_natAbs_le_two_mul_mul {R : ℕ} {x y : Site d} (hx : x ∈ box d R)
    (hy : y ∈ box d R) :
    ∑ j, (x j - y j).natAbs ≤ 2 * R * d := by
  have hx' : ∀ j : Fin d, (x j).natAbs ≤ R := fun j =>
    Int.ofNat_le.mp (Int.abs_eq_natAbs (x j) ▸ hx j)
  have hy' : ∀ j : Fin d, (y j).natAbs ≤ R := fun j =>
    Int.ofNat_le.mp (Int.abs_eq_natAbs (y j) ▸ hy j)
  have hterm : ∀ j : Fin d, (x j - y j).natAbs ≤ 2 * R := fun j =>
    le_trans (Int.natAbs_sub_le (x j) (y j))
      (le_trans (Nat.add_le_add (hx' j) (hy' j)) (le_of_eq (Nat.two_mul R).symm))
  have hsum : ∑ j : Fin d, (x j - y j).natAbs ≤ ∑ j : Fin d, (2 * R) :=
    Finset.sum_le_sum (fun j _ => hterm j)
  have hconst : ∑ j : Fin d, (2 * R) = 2 * R * d := (by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact Nat.mul_comm d (2 * R))
  omega


-- le_two_mul_pow_mul_of_sum_natAbs_eq with n := ∑ natAbs, then pow_le_pow_right₀ (1 ≤ 2d since 1 ≤
-- d) with sum_natAbs_le_two_mul_mul
-- and mul_le_mul_of_nonneg_right (0 ≤ u y by hpos, mem_box_of_le R ≤ 2R).
/-- The small-`R` Harnack bound `u x ≤ (2d)^{2Rd} * u y` for `x, y ∈ box d R`, combining the
neighbour chain bound with the `L¹` diameter of the box. -/
private theorem le_two_mul_pow_mul_of_mem_box (hd : 1 ≤ d) {R : ℕ} (hR : 1 ≤ R) (u : Site d → ℝ)
    (hpos : ∀ x ∈ box d (2 * R), 0 ≤ u x)
    (hharm : ∀ x ∈ box d (2 * R - 1), nbrSum u x = 2 * (d : ℝ) * u x)
    {x y : Site d} (hx : x ∈ box d R) (hy : y ∈ box d R) :
    u x ≤ (2 * (d : ℝ)) ^ (2 * R * d) * u y := by
  have hdR : (1 : ℝ) ≤ (d : ℝ) := (by exact_mod_cast hd)
  have h1d : (1 : ℝ) ≤ 2 * (d : ℝ) := (by linarith)
  have h34 : ∑ j, (x j - y j).natAbs ≤ 2 * R * d := sum_natAbs_le_two_mul_mul hx hy
  have h33 : u x ≤ (2 * (d : ℝ)) ^ (∑ j, (x j - y j).natAbs) * u y :=
      le_two_mul_pow_mul_of_sum_natAbs_eq hR u hpos hharm (∑ j, (x j - y j).natAbs) x y hx hy rfl
  have hpow : (2 * (d : ℝ)) ^ (∑ j, (x j - y j).natAbs) ≤ (2 * (d : ℝ)) ^ (2 * R * d) :=
      pow_le_pow_right₀ h1d h34
  have hybox : y ∈ box d (2 * R) := mem_box_of_le (by omega) hy
  exact le_trans h33 (mul_le_mul_of_nonneg_right hpow (hpos y hybox))


/-! ### The Harnack inequality -/

/-- The Harnack inequality: for `d ≥ 1` there is `C > 0` such that every `u` nonnegative on `box
d (2R)` and harmonic on `box d (2R-1)` satisfies `u x ≤ C * u y` for all `x, y ∈ box d R`,
uniformly in `R ≥ 1`. -/
theorem harnack (d : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℕ) (u : Site d → ℝ), 1 ≤ R →
      (∀ x ∈ box d (2 * R), 0 ≤ u x) →
      (∀ x ∈ box d (2 * R - 1), nbrSum u x = 2 * (d : ℝ) * u x) →
      ∀ x ∈ box d R, ∀ y ∈ box d R, u x ≤ C * u y := by
  obtain ⟨C₂, hC₂, hbig⟩ := le_mul_of_nonneg_harmonicOn hd
  have h2d : (1 : ℝ) ≤ 2 * (d : ℝ) := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  refine ⟨(2 * (d : ℝ)) ^ (8 * d) + C₂, by positivity, ?_⟩
  intro R u hR hpos hharm x hx y hy
  have huy : 0 ≤ u y := hpos y (mem_box_of_le (by omega) hy)
  have hpow0 : 0 ≤ (2 * (d : ℝ)) ^ (8 * d) := by positivity
  by_cases hR4 : 4 ≤ R
  · have h := hbig R u hR4 hpos hharm x hx y hy
    nlinarith
  · have h := le_two_mul_pow_mul_of_mem_box hd hR u hpos hharm hx hy
    have hle : (2 * (d : ℝ)) ^ (2 * R * d) ≤ (2 * (d : ℝ)) ^ (8 * d) :=
      pow_le_pow_right₀ h2d (by nlinarith)
    nlinarith

end LatticeProb
