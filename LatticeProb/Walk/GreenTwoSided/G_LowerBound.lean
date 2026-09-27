import LatticeProb.Site
import LatticeProb.Graph.Zd
import LatticeProb.Graph.ExitDecomp
import LatticeProb.Network.Killed
import LatticeProb.Network.KilledGreen
import LatticeProb.Walk.SRWGaussBound
import LatticeProb.Walk.GreenIdentity
import LatticeProb.Walk.Decomp
import LatticeProb.Walk.LocalCLTOne
import LatticeProb.Walk.SRWOneDim
import LatticeProb.Walk.LocalCLT
import LatticeProb.Walk.ExitBox
import LatticeProb.Walk.GreenTwoSided.F_ChainingBound

/-!
# Small scales and the lower bound

The lower bound for the killed Green function of a set containing a box: for `B ⊇ box d (m+ρ)` and
`x, y ∈ box d m` with `m ≤ Kρ`, `g_B(x,y) ≥ c(K) ρ^{2-d}`, combining the chained near-diagonal
bound of `F_ChainingBound` (large `ρ`) with a monotone-lattice-path bound (small `ρ`). This file
proves the module's second main public result, `killedGreenReal_ge_box`.
-/

open Finset
open scoped Classical

namespace LatticeProb

namespace GreenTwoSided

variable {d : ℕ}

-- One step: x ∈ B, x' = x ± unit i: killedHeat (n+1) x y ≥ killedHeat n x' y / (2d).
-- Graph.Zd.killedHeat_succ_walkOp, if_pos, LatticeProb.walkOp = nbrSum/(2d), the single term
-- ≤ nbrSum (Finset.single_le_sum, Network.killedHeat_nonneg, le_add_of_nonneg_right/left).
/-- A single step of the killed walk from a neighbour `x' = x ± unit i` of `x ∈ C` contributes at
least `killedHeat n x' y / (2d)` to `killedHeat (n+1) x y`. -/
private theorem killedHeat_div_two_mul_le_killedHeat_succ (hd : 1 ≤ d) (C : Set (Site d)) (n : ℕ)
    {x x' : Site d} (hx : x ∈ C)
    (i : Fin d) (hx' : x' = x + unit i ∨ x' = x - unit i) (y : Site d) :
    Graph.killedHeat (lattice d) C n x' y / (2 * (d : ℝ))
      ≤ Graph.killedHeat (lattice d) C (n + 1) x y := by
  have hnn : ∀ z : Site d, 0 ≤ Graph.killedHeat (lattice d) C n z y :=
    fun z => Network.killedHeat_nonneg (G := lattice d) C n z y
  rw [Graph.Zd.killedHeat_succ_walkOp, if_pos hx, LatticeProb.walkOp, LatticeProb.nbrSum]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  rcases hx' with h | h
  · rw [h]
    exact le_trans (le_add_of_nonneg_right (hnn (x - unit i)))
      (Finset.single_le_sum (fun j _ => add_nonneg (hnn (x + unit j)) (hnn (x - unit j)))
        (Finset.mem_univ i))
  · rw [h]
    exact le_trans (le_add_of_nonneg_left (hnn (x + unit i)))
      (Finset.single_le_sum (fun j _ => add_nonneg (hnn (x + unit j)) (hnn (x - unit j)))
        (Finset.mem_univ i))


-- Finset.add_sum_erase at i on both sides; the erased sums agree termwise (Finset.sum_congr,
-- Finset.ne_of_mem_erase, hoff); omega.
/-- If `x'` agrees with `x` off coordinate `i` and its `i`-th distance to `y` is one less, then
`∑_j |x'_j - y_j| + 1 = ∑_j |x_j - y_j|`. -/
private theorem sum_natAbs_add_one_eq_of_ne {x' x y : Site d} (i : Fin d)
    (hoff : ∀ j, j ≠ i → x' j = x j)
    (hi : (x' i - y i).natAbs + 1 = (x i - y i).natAbs) :
    (∑ j, (x' j - y j).natAbs) + 1 = ∑ j, (x j - y j).natAbs := by
  rw [← Finset.add_sum_erase _ (fun j => (x' j - y j).natAbs) (Finset.mem_univ i),
      ← Finset.add_sum_erase _ (fun j => (x j - y j).natAbs) (Finset.mem_univ i)]
  rw [add_right_comm, hi]
  congr 1
  exact Finset.sum_congr rfl (fun j hj => by rw [hoff j (Finset.ne_of_mem_erase hj)])

-- intro j; j = i: Pi.add_apply, unit, Pi.single_eq_same, abs_le (hx i, hy i), omega;
-- j ≠ i: Pi.single_eq_of_ne, add_zero, hx j.
/-- Stepping coordinate `i` of `x` up by one toward `y` keeps the result in `box d m`, when `x_i
< y_i`. -/
private theorem add_unit_mem_box_of_lt {m : ℕ} {x y : Site d} (hx : x ∈ box d m) (hy : y ∈ box d m)
    {i : Fin d} (h : x i < y i) : x + unit i ∈ box d m := by
  intro j
  by_cases hji : j = i
  · subst hji
    rw [Pi.add_apply, unit, Pi.single_eq_same]
    have h1 := hx j
    have h2 := hy j
    have h3 : x j < y j := h
    rw [abs_le] at h1 h2 ⊢
    omega
  · rw [Pi.add_apply, unit, Pi.single_eq_of_ne hji, add_zero]
    exact hx j

-- As add_unit_mem_box_of_lt with Pi.sub_apply, sub_zero.
/-- Stepping coordinate `i` of `x` down by one toward `y` keeps the result in `box d m`, when
`y_i < x_i`. -/
private theorem sub_unit_mem_box_of_lt {m : ℕ} {x y : Site d} (hx : x ∈ box d m) (hy : y ∈ box d m)
    {i : Fin d} (h : y i < x i) : x - unit i ∈ box d m := by
  intro j
  by_cases hji : j = i
  · subst hji
    rw [Pi.sub_apply, unit, Pi.single_eq_same]
    have h1 := hx j
    have h2 := hy j
    have h3 : y j < x j := h
    rw [abs_le] at h1 h2 ⊢
    omega
  · rw [Pi.sub_apply, unit, Pi.single_eq_of_ne hji, sub_zero]
    exact hx j

-- unfold graphNorm, Pi.sub_apply; sum_natAbs_add_one_eq_of_ne i (off-diagonal: unit,
-- Pi.single_eq_of_ne,
-- add_zero; diagonal: Pi.single_eq_same, omega using h).
/-- Stepping toward `y` in coordinate `i` (with `x_i < y_i`) decreases the `graphNorm` distance
to `y` by exactly one. -/
private theorem graphNorm_add_unit_sub_add_one_eq {x y : Site d} {i : Fin d} (h : x i < y i) :
    graphNorm (x + unit i - y) + 1 = graphNorm (x - y) := by
  unfold graphNorm
  rw [← Finset.add_sum_erase _ (fun j => ((x + unit i - y) j).natAbs) (Finset.mem_univ i),
      ← Finset.add_sum_erase _ (fun j => ((x - y) j).natAbs) (Finset.mem_univ i)]
  rw [add_right_comm]
  congr 1
  · simp only [Pi.add_apply, Pi.sub_apply, unit, Pi.single_eq_same]
    have h1 : (((x i + 1 - y i).natAbs : ℤ)) = y i - x i - 1 := by
      rw [show x i + 1 - y i = -((y i - x i) - 1) by ring, Int.natAbs_neg,
        Int.natAbs_of_nonneg (by omega)]
    have h2 : (((x i - y i).natAbs : ℤ)) = y i - x i := by
      rw [show x i - y i = -(y i - x i) by ring, Int.natAbs_neg,
        Int.natAbs_of_nonneg (by omega)]
    omega
  · exact Finset.sum_congr rfl (fun j hj => by
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      have hxj : (x + unit i - y) j = (x - y) j := by
        simp only [Pi.add_apply, Pi.sub_apply, unit, Pi.single_eq_of_ne hji, add_zero]
      rw [hxj])

-- As graphNorm_add_unit_sub_add_one_eq with x - unit i (Pi.sub_apply, sub_zero).
/-- The symmetric statement of `graphNorm_add_unit_sub_add_one_eq` for `y_i < x_i`. -/
private theorem graphNorm_sub_unit_sub_add_one_eq {x y : Site d} {i : Fin d} (h : y i < x i) :
    graphNorm (x - unit i - y) + 1 = graphNorm (x - y) := by
  unfold graphNorm
  rw [← Finset.add_sum_erase _ (fun j => ((x - unit i - y) j).natAbs) (Finset.mem_univ i),
      ← Finset.add_sum_erase _ (fun j => ((x - y) j).natAbs) (Finset.mem_univ i)]
  rw [add_right_comm]
  congr 1
  · simp only [Pi.sub_apply, unit, Pi.single_eq_same]
    have h1 : (((x i - 1 - y i).natAbs : ℤ)) = x i - y i - 1 := by
      rw [show x i - 1 - y i = (x i - y i) - 1 by ring,
        Int.natAbs_of_nonneg (by omega)]
    have h2 : (((x i - y i).natAbs : ℤ)) = x i - y i :=
      Int.natAbs_of_nonneg (by omega)
    omega
  · exact Finset.sum_congr rfl (fun j hj => by
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      have hxj : (x - unit i - y) j = (x - y) j := by
        simp only [Pi.sub_apply, unit, Pi.single_eq_of_ne hji, sub_zero]
      rw [hxj])

-- ∃ i, x i ≠ y i (by_contra, funext, push_neg); lt_or_gt_of_ne: x + unit i with
-- add_unit_mem_box_of_lt, graphNorm_add_unit_sub_add_one_eq (Or.inl rfl), or x - unit i with
-- sub_unit_mem_box_of_lt,
-- graphNorm_sub_unit_sub_add_one_eq (Or.inr rfl).
/-- For `x ≠ y` in `box d m`, there is a neighbour `x'` of `x` in `box d m`, obtained by a single
lattice step toward `y`, whose `graphNorm` distance to `y` is one less than that of `x`. -/
private theorem exists_step_graphNorm_add_one_eq {m : ℕ} {x y : Site d} (hx : x ∈ box d m)
    (hy : y ∈ box d m)
    (hxy : x ≠ y) :
    ∃ x' ∈ box d m, ∃ i : Fin d, (x' = x + unit i ∨ x' = x - unit i) ∧
      graphNorm (x' - y) + 1 = graphNorm (x - y) := by
  have hex : ∃ i : Fin d, x i ≠ y i := by
    by_contra h
    exact hxy (funext fun i => by simpa using not_not.mp (not_exists.mp h i))
  obtain ⟨i, hi⟩ := hex
  rcases lt_or_gt_of_ne hi with hlt | hgt
  · exact ⟨x + unit i, add_unit_mem_box_of_lt hx hy hlt, i, Or.inl rfl,
      graphNorm_add_unit_sub_add_one_eq hlt⟩
  · exact ⟨x - unit i, sub_unit_mem_box_of_lt hx hy hgt, i, Or.inr rfl,
      graphNorm_sub_unit_sub_add_one_eq hgt⟩

-- pow_zero; graphNorm_eq_zero_iff, sub_eq_zero give x = y (subst); Network.killedHeat_zero,
-- if_pos hx, if_pos rfl.
/-- The base case `(2d)⁻¹^0 ≤ killedHeat C 0 x y` when `x ∈ C` and `graphNorm (x-y) = 0`. -/
private theorem inv_two_mul_pow_zero_le_killedHeat_zero (C : Set (Site d)) {x y : Site d}
    (hx : x ∈ C)
    (h : graphNorm (x - y) = 0) :
    (2 * (d : ℝ))⁻¹ ^ 0 ≤ Graph.killedHeat (lattice d) C 0 x y := by
  rw [pow_zero, Network.killedHeat_zero, if_pos hx]
  have hxy : x = y := by
    have h1 : x - y = 0 := graphNorm_eq_zero_iff.mp h
    simpa using sub_eq_zero.mp h1
  rw [if_pos hxy]

-- Monotone lattice path.  Induction on n generalizing x.  n = 0: x = y (graphNorm_eq_zero_iff),
-- killedHeat 0 = 1 (Network.killedHeat_zero, hB).  n+1: x ≠ y; step toward y (as
-- exists_step_sum_natAbs_add_one_eq:
-- x' := x ∓ unit i ∈ box m with graphNorm (x' - y) = n); killedHeat_div_two_mul_le_killedHeat_succ;
-- pow_succ.  SPLIT?
/-- The monotone-lattice-path lower bound: `(2d)⁻¹^n ≤ killedHeat C n x y` whenever `box d m ⊆
C`, `x, y ∈ box d m`, and `graphNorm (x-y) = n`. -/
private theorem inv_two_mul_pow_le_killedHeat_of_graphNorm_eq (hd : 1 ≤ d) (m : ℕ)
    (C : Set (Site d)) (hB : ∀ z ∈ box d m, z ∈ C) :
    ∀ (n : ℕ) (x y : Site d), x ∈ box d m → y ∈ box d m → graphNorm (x - y) = n →
      (2 * (d : ℝ))⁻¹ ^ n ≤ Graph.killedHeat (lattice d) C n x y := by
  have hdR : (0 : ℝ) < 2 * (d : ℝ) := by
    have h : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    linarith
  intro n
  induction n with
  | zero =>
    intro x y hx _ h
    exact inv_two_mul_pow_zero_le_killedHeat_zero C (hB x hx) h
  | succ n ih =>
    intro x y hx hy h
    have hxy : x ≠ y := by
      rintro rfl
      rw [sub_self, graphNorm_zero] at h
      omega
    obtain ⟨x', hx', i, hrel, hnorm⟩ := exists_step_graphNorm_add_one_eq hx hy hxy
    have h' : graphNorm (x' - y) = n := by omega
    have h50 := killedHeat_div_two_mul_le_killedHeat_succ hd C n (hB x hx) i hrel y
    have hih := ih x' y hx' hy h'
    calc (2 * (d : ℝ))⁻¹ ^ (n + 1) = (2 * (d : ℝ))⁻¹ ^ n / (2 * (d : ℝ)) := by
          rw [pow_succ, div_eq_mul_inv]
      _ ≤ Graph.killedHeat (lattice d) C n x' y / (2 * (d : ℝ)) :=
          div_le_div_of_nonneg_right hih hdR.le
      _ ≤ Graph.killedHeat (lattice d) C (n + 1) x y := h50

-- killedGreenReal_eq_tsum_killedHeat_div and Summable.le_tsum / le_tsum
-- (Network.summable_killedHeat, q ∉ B,
-- Network.killedHeat_nonneg); div_le_div_of_nonneg_right.
/-- `killedHeat B k x y / (2d) ≤ killedGreenReal B x y`, since the Green function is the full
series and each term is nonnegative. -/
private theorem killedHeat_div_two_mul_le_killedGreenReal (hd : 1 ≤ d) (B : Finset (Site d)) (k : ℕ)
    (x y : Site d) :
    Graph.killedHeat (lattice d) (B : Set (Site d)) k x y / (2 * (d : ℝ))
      ≤ Graph.killedGreenReal (lattice d) (B : Set (Site d)) x y := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨q, hq⟩ := Infinite.exists_notMem_finset B
  have hsum : Summable (fun k => Graph.killedHeat (lattice d) (B : Set (Site d)) k x y) :=
    Network.summable_killedHeat (Graph.Zd.latticeConnected d) B hq x y
  have hk : Graph.killedHeat (lattice d) (B : Set (Site d)) k x y
      ≤ ∑' j, Graph.killedHeat (lattice d) (B : Set (Site d)) j x y :=
    Summable.le_tsum hsum k (fun j _ => Network.killedHeat_nonneg _ j x y)
  rw [killedGreenReal_eq_tsum_killedHeat_div hd B x y]
  exact div_le_div_of_nonneg_right hk (by positivity)


-- ρ ↦ s conversion: s ≤ ρ ≤ 2 M s ⇒ ρ^{2-d} ≤ 2M s^{2-d}.  d = 1: zpow_one; d ≥ 2:
-- zpow_le_zpow_left₀-type antitonicity for nonpositive exponents (s ≤ ρ), and 1 ≤ 2M.
/-- For `s ≤ ρ ≤ 2Ms`, `ρ^{2-d} ≤ 2M s^{2-d}`. -/
private theorem rpow_two_sub_le_two_mul_rpow_two_sub (M s ρ : ℕ) (hM : 1 ≤ M) (hs : 1 ≤ s)
    (hsρ : s ≤ ρ) (hρ : ρ ≤ 2 * M * s)
    (hd : 1 ≤ d) :
    (ρ : ℝ) ^ ((2 : ℤ) - d) ≤ 2 * M * (s : ℝ) ^ ((2 : ℤ) - d) := by
  have hs1 : (1 : ℝ) ≤ (s : ℝ) := Nat.one_le_cast.mpr hs
  have hsρ' : (s : ℝ) ≤ (ρ : ℝ) := Nat.cast_le.mpr hsρ
  have hs0 : (0 : ℝ) < (s : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hs)
  have hρ0 : (0 : ℝ) < (ρ : ℝ) := lt_of_lt_of_le hs0 hsρ'
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := Nat.one_le_cast.mpr hM
  by_cases hd2 : 2 ≤ d
  · have hcast : ((d - 2 : ℕ) : ℤ) = (d : ℤ) - 2 := (by rw [Nat.cast_sub (R := ℤ) hd2]; ring)
    have he : ((2 : ℤ) - (d : ℤ)) = -(((d - 2 : ℕ) : ℤ)) := (by rw [hcast]; ring)
    have hpow : (s : ℝ) ^ (d - 2) ≤ (ρ : ℝ) ^ (d - 2) :=
      pow_le_pow_left₀ (le_of_lt hs0) hsρ' _
    have hA : ((ρ : ℝ) ^ (d - 2))⁻¹ ≤ ((s : ℝ) ^ (d - 2))⁻¹ :=
      (inv_le_inv₀ (pow_pos hρ0 _) (pow_pos hs0 _)).mpr hpow
    have hnn : (0 : ℝ) ≤ ((s : ℝ) ^ (d - 2))⁻¹ := inv_nonneg.mpr (pow_nonneg (le_of_lt hs0) _)
    have hM2 : (1 : ℝ) ≤ 2 * (M : ℝ) := (by linarith)
    have hB : ((s : ℝ) ^ (d - 2))⁻¹ ≤ 2 * (M : ℝ) * ((s : ℝ) ^ (d - 2))⁻¹ :=
      le_trans (le_of_eq (one_mul _).symm) (mul_le_mul_of_nonneg_right hM2 hnn)
    calc (ρ : ℝ) ^ ((2 : ℤ) - (d : ℤ))
        = ((ρ : ℝ) ^ (d - 2))⁻¹ := (by rw [he, zpow_neg, zpow_natCast])
      _ ≤ ((s : ℝ) ^ (d - 2))⁻¹ := hA
      _ ≤ 2 * (M : ℝ) * ((s : ℝ) ^ (d - 2))⁻¹ := hB
      _ = 2 * (M : ℝ) * (s : ℝ) ^ ((2 : ℤ) - (d : ℤ)) := (by rw [he, zpow_neg, zpow_natCast])
  · have hd1 : d = 1 := (by omega)
    subst hd1
    have h1e : ((2 : ℤ) - ((1 : ℕ) : ℤ)) = 1 := (by norm_num)
    rw [h1e, zpow_one, zpow_one]
    have hcast : ((2 * M * s : ℕ) : ℝ) = 2 * (M : ℝ) * (s : ℝ) := (by push_cast; ring)
    exact le_trans (Nat.cast_le.mpr hρ) (le_of_eq hcast)


-- For 1 ≤ ρ: ρ^{2-d} ≤ ρ (zpow_le_zpow_right₀ with 2 - d ≤ 1, one_le_cast), zpow_one.
/-- For `ρ ≥ 1`, `ρ^{2-d} ≤ ρ`. -/
private theorem rpow_two_sub_le_self (ρ : ℕ) (hρ : 1 ≤ ρ) (hd : 1 ≤ d) :
    (ρ : ℝ) ^ ((2 : ℤ) - d) ≤ ρ := by
  calc (ρ : ℝ) ^ ((2 : ℤ) - (d : ℤ)) ≤ (ρ : ℝ) ^ (1 : ℤ) :=
        zpow_le_zpow_right₀ (by exact_mod_cast hρ) (by omega)
    _ = ρ := zpow_one _


-- graphNorm (x - y) ≤ 2 d m for x, y ∈ box m (as sum_natAbs_le_two_mul_mul: each |x j - y j| ≤ 2m).
/-- For integers `a, b` with `|a|, |b| ≤ m`, `|a-b| ≤ 2m`. -/
private theorem natAbs_sub_le_two_mul_of_abs_le (m : ℕ) (a b : ℤ) (ha : |a| ≤ (m : ℤ))
    (hb : |b| ≤ (m : ℤ)) :
    (a - b).natAbs ≤ 2 * m := by
  have h1 : |a - b| ≤ (2 * m : ℤ) := by
    calc |a - b| ≤ |a| + |b| := abs_sub a b
      _ ≤ (m : ℤ) + m := add_le_add ha hb
      _ = 2 * m := by ring
  have h2 : ((a - b).natAbs : ℤ) ≤ 2 * m := by
    rw [Int.natCast_natAbs]; exact h1
  exact_mod_cast h2

/-- Implementation lemma for `graphNorm_sub_le_two_mul_mul_of_mem_box`. -/
private theorem graphNorm_sub_le_two_mul_mul_of_mem_box' (m : ℕ) {x y : Site d} (hx : x ∈ box d m)
    (hy : y ∈ box d m) :
    graphNorm (x - y) ≤ 2 * d * m := by
  rw [graphNorm]
  have hsum : ∑ i : Fin d, ((x - y) i).natAbs ≤ ∑ _i : Fin d, (2 * m) :=
    Finset.sum_le_sum (fun i _ => natAbs_sub_le_two_mul_of_abs_le m (x i) (y i) (hx i) (hy i))
  have hconst : (∑ _i : Fin d, (2 * m)) = 2 * d * m := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  rw [hconst] at hsum
  exact hsum

/-- For `x, y ∈ box d m`, `graphNorm (x-y) ≤ 2dm`. -/
private theorem graphNorm_sub_le_two_mul_mul_of_mem_box (m : ℕ) {x y : Site d} (hx : x ∈ box d m)
    (hy : y ∈ box d m) :
    graphNorm (x - y) ≤ 2 * d * m := by
  exact graphNorm_sub_le_two_mul_mul_of_mem_box' m hx hy


-- Box monotonicity: intro i; le_trans (hx i) (Nat.cast_le.mpr hab) (exact_mod_cast).
/-- Box monotonicity: `x ∈ box d a` and `a ≤ b` give `x ∈ box d b`. -/
private theorem mem_box_of_mem_box_of_le {a b : ℕ} (hab : a ≤ b) {x : Site d} (hx : x ∈ box d a) :
    x ∈ box d b := by
  intro i
  exact le_trans (hx i) (by exact_mod_cast hab)

-- Nat.le_div_iff_mul_le (0 < M): (s₂ + 1) * M ≤ ρ (mul_comm).
/-- If `M(s₂+1) ≤ ρ`, then `s₂+1 ≤ ρ/M`. -/
private theorem add_one_le_ediv_of_mul_le (M s₂ ρ : ℕ) (hM : 1 ≤ M) (hρ : M * (s₂ + 1) ≤ ρ) :
    s₂ + 1 ≤ ρ / M := by
  exact (Nat.le_div_iff_mul_le (by omega : 0 < M)).mpr (by rw [Nat.mul_comm]; exact hρ)

-- Nat.lt_div_mul_add (0 < M): ρ < ρ/M * M + M ≤ 2 M (ρ/M) (hs; nlinarith).
/-- If `ρ/M ≥ 1`, then `ρ ≤ 2M(ρ/M)`. -/
private theorem le_two_mul_mul_ediv_of_one_le_ediv (M ρ : ℕ) (hM : 1 ≤ M) (hs : 1 ≤ ρ / M) :
    ρ ≤ 2 * M * (ρ / M) := by
  have hMpos : 0 < M := by omega
  have h1 : ρ < ρ / M * M + M := Nat.lt_div_mul_add hMpos
  have h3 : M ≤ M * (ρ / M) := by
    have := Nat.mul_le_mul_left M hs
    simpa using this
  have h4 : ρ / M * M + M ≤ ρ / M * M + M * (ρ / M) := Nat.add_le_add_left h3 _
  have h5 : ρ / M * M + M * (ρ / M) = 2 * M * (ρ / M) := by ring
  exact le_of_lt (h1.trans_le (h4.trans_eq h5))

-- m ≤ K ρ ≤ K (2 M s) (Nat.mul_le_mul_left); ring_nf / Nat.mul_assoc, Nat.mul_left_comm.
/-- If `m ≤ Kρ` and `ρ ≤ 2Ms`, then `m ≤ 2KMs`. -/
private theorem le_two_mul_mul_mul_of_le_mul (K M s ρ m : ℕ) (hm : m ≤ K * ρ) (hρ : ρ ≤ 2 * M * s) :
    m ≤ 2 * K * M * s := by
  calc m ≤ K * ρ := hm
    _ ≤ K * (2 * M * s) := Nat.mul_le_mul_left K hρ
    _ = 2 * K * M * s := by ring

-- 2 d m ≤ 2 d (K ρ) ≤ 2 d (K ρ₀) (Nat.mul_le_mul_left twice); Nat.mul_assoc.
/-- If `m ≤ Kρ` and `ρ ≤ ρ₀`, then `2dm ≤ 2dKρ₀`. -/
private theorem two_mul_mul_le_two_mul_mul_mul_of_le (K m ρ ρ₀ : ℕ) (hm : m ≤ K * ρ) (hρ : ρ ≤ ρ₀) :
    2 * d * m ≤ 2 * d * K * ρ₀ := by
  calc 2 * d * m ≤ 2 * d * (K * ρ) := Nat.mul_le_mul_left (2 * d) hm
    _ ≤ 2 * d * (K * ρ₀) := Nat.mul_le_mul_left (2 * d) (Nat.mul_le_mul_left K hρ)
    _ = 2 * d * K * ρ₀ := by ring

-- pow_le_pow_of_le_one (inv_nonneg, inv_le_one_of_one_le₀ with 1 ≤ 2 d) (by omega).
/-- Monotonicity of the base case bound in the box radius: `(2d)⁻¹^{L+1} ≤ (2d)⁻¹^{ℓ+1}` when `ℓ
≤ L`. -/
private theorem inv_two_mul_pow_add_one_le_of_le (hd : 1 ≤ d) (ℓ L : ℕ) (h : ℓ ≤ L) :
    (2 * (d : ℝ))⁻¹ ^ (L + 1) ≤ (2 * (d : ℝ))⁻¹ ^ (ℓ + 1) := by
  have hdR : (1 : ℝ) ≤ 2 * (d : ℝ) := by
    have h1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have h0 : (0 : ℝ) ≤ (2 * (d : ℝ))⁻¹ := inv_nonneg.mpr (by linarith)
  have h1 : (2 * (d : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hdR
  exact pow_le_pow_of_le_one h0 h1 (by omega : ℓ + 1 ≤ L + 1)

-- inv_two_mul_pow_le_killedHeat_of_graphNorm_eq hd m (B : Set) (Finset.mem_coe.mpr ∘ hB) (graphNorm
-- (x - y)) x y hx hy rfl,
-- killedHeat_div_two_mul_le_killedGreenReal hd B, pow_succ, div_eq_mul_inv,
-- div_le_div_of_nonneg_right,
-- inv_two_mul_pow_add_one_le_of_le hd _ L hL.
/-- The small-radius Green-function lower bound `(2d)⁻¹^{L+1} ≤ killedGreenReal B x y`, from the
monotone-lattice-path bound and `killedHeat_div_two_mul_le_killedGreenReal`. -/
private theorem inv_two_mul_pow_add_one_le_killedGreenReal (hd : 1 ≤ d) (B : Finset (Site d))
    (m L : ℕ)
    (hB : ∀ z ∈ box d m, z ∈ B) {x y : Site d} (hx : x ∈ box d m) (hy : y ∈ box d m)
    (hL : graphNorm (x - y) ≤ L) :
    (2 * (d : ℝ))⁻¹ ^ (L + 1) ≤ Graph.killedGreenReal (lattice d) (B : Set (Site d)) x y := by
  have hdR : (0 : ℝ) < 2 * (d : ℝ) := by
    have h : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hd)
    linarith
  have h1 : (2 * (d : ℝ))⁻¹ ^ (L + 1) ≤ (2 * (d : ℝ))⁻¹ ^ (graphNorm (x - y) + 1) := by
    have h0 : (0 : ℝ) ≤ (2 * (d : ℝ))⁻¹ := inv_nonneg.mpr hdR.le
    have h1' : (2 * (d : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by
      have h : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      linarith)
    exact pow_le_pow_of_le_one h0 h1' (by omega : graphNorm (x - y) + 1 ≤ L + 1)
  have h2 := inv_two_mul_pow_le_killedHeat_of_graphNorm_eq hd m (B : Set (Site d))
      (fun z hz => Finset.mem_coe.mpr (hB z hz))
    (graphNorm (x - y)) x y hx hy rfl
  have h3 := killedHeat_div_two_mul_le_killedGreenReal hd B (graphNorm (x - y)) x y
  calc (2 * (d : ℝ))⁻¹ ^ (L + 1) ≤ (2 * (d : ℝ))⁻¹ ^ (graphNorm (x - y) + 1) := h1
    _ = (2 * (d : ℝ))⁻¹ ^ (graphNorm (x - y)) / (2 * (d : ℝ)) := by rw [pow_succ, div_eq_mul_inv]
    _ ≤ Graph.killedHeat (lattice d) (B : Set (Site d)) (graphNorm (x - y)) x y / (2 * (d : ℝ)) :=
        div_le_div_of_nonneg_right h2 hdR.le
    _ ≤ Graph.killedGreenReal (lattice d) (B : Set (Site d)) x y := h3

-- c R ≤ (c₃/(2M)) R ≤ (c₃/(2M)) (2 M S) = c₃ S ≤ g: mul_le_mul_of_nonneg_right,
-- mul_le_mul_of_nonneg_left
-- (div_nonneg), field_simp / div_mul_cancel₀.
/-- Interpolation step: `c ≤ c₃/(2M)`, `R ≤ 2MS` and `c₃S ≤ g` together give `cR ≤ g`. -/
private theorem mul_le_of_le_div_two_mul_of_le (c c₃ M R S g : ℝ) (hM : 0 < M)
    (hc : c ≤ c₃ / (2 * M)) (hc₃ : 0 ≤ c₃) (hR0 : 0 ≤ R) (hR : R ≤ 2 * M * S)
    (hg : c₃ * S ≤ g) : c * R ≤ g := by
  have h1 : c * R ≤ (c₃ / (2 * M)) * (2 * M * S) :=
    mul_le_mul hc hR hR0 (by positivity)
  have h2 : (c₃ / (2 * M)) * (2 * M * S) = c₃ * S := by
    field_simp
  linarith

-- c R ≤ c ρ₀ ≤ (a/ρ₀) ρ₀ = a ≤ g: mul_le_mul_of_nonneg_left, mul_le_mul_of_nonneg_right,
-- div_mul_cancel₀.
/-- Interpolation step: `c ≤ a/ρ₀`, `R ≤ ρ₀` and `a ≤ g` together give `cR ≤ g`. -/
private theorem mul_le_of_le_div_of_le (c a R ρ₀ g : ℝ) (hc0 : 0 ≤ c) (hρ₀ : 0 < ρ₀)
    (hc : c ≤ a / ρ₀) (hR : R ≤ ρ₀) (hg : a ≤ g) : c * R ≤ g := by
  have h1 : c * R ≤ c * ρ₀ := mul_le_mul_of_nonneg_left hR hc0
  have h2 : c * ρ₀ ≤ a := by
    have h3 : c * ρ₀ ≤ (a / ρ₀) * ρ₀ := mul_le_mul_of_nonneg_right hc (le_of_lt hρ₀)
    rwa [div_mul_cancel₀ a (ne_of_gt hρ₀)] at h3
  linarith

-- Fix M, (for K' := 2 K M) c₃, s₂ from exists_const_mul_rpow_le_killedGreenReal.  ρ₀ := M (s₂ + 1).
-- ρ ≥ ρ₀: s := ρ / M (Nat.div), s ≥ s₂, s ≤ ρ, ρ ≤ 2 M s, m ≤ Kρ ≤ K'·s,
--   box (m + M s) ⊆ box (m + ρ) (box monotonicity, cf. Harnack.lean),
--   exists_const_mul_rpow_le_killedGreenReal, rpow_two_sub_le_two_mul_rpow_two_sub.
-- ρ < ρ₀: ℓ := graphNorm (x - y) ≤ 2dKρ₀ (graphNorm_sub_le_two_mul_mul_of_mem_box);
-- inv_two_mul_pow_le_killedHeat_of_graphNorm_eq (box m ⊆ B),
-- killedHeat_div_two_mul_le_killedGreenReal:
--   g ≥ (2d)⁻¹^(2dKρ₀+1), and ρ^{2-d} ≤ ρ₀ (rpow_two_sub_le_self).
-- c := min (c₃/(2M)) ((2d)⁻¹^(2dKρ₀+1)/ρ₀).  SPLIT?
/-- For `B` containing `box d (m+ρ)` and `x, y ∈ box d m` with `m ≤ Kρ`, the killed Green
function satisfies `g_B(x,y) ≥ c(K) ρ^{2-d}`, uniformly in `d ≥ 1`. -/
theorem killedGreenReal_ge_box (hd : 1 ≤ d) (K : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (m ρ : ℕ), 1 ≤ ρ → m ≤ K * ρ → ∀ B : Finset (Site d),
      (∀ z ∈ box d (m + ρ), z ∈ B) → ∀ x ∈ box d m, ∀ y ∈ box d m,
        c * (ρ : ℝ) ^ ((2 : ℤ) - d) ≤ Graph.killedGreenReal (lattice d) (B : Set (Site d)) x y := by
  obtain ⟨M, hM1, h49⟩ := exists_const_mul_rpow_le_killedGreenReal hd
  obtain ⟨c₃, hc₃, s₂, _, H⟩ := h49 (2 * K * M)
  have hdR : (0 : ℝ) < 2 * (d : ℝ) := by
    have h : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    linarith
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
  have hρ₀N : 0 < M * (s₂ + 1) := Nat.mul_pos hM1 (Nat.succ_pos s₂)
  have hρ₀R : (0 : ℝ) < ((M * (s₂ + 1) : ℕ) : ℝ) := by exact_mod_cast hρ₀N
  have ha : (0 : ℝ) < (2 * (d : ℝ))⁻¹ ^ (2 * d * K * (M * (s₂ + 1)) + 1) :=
    pow_pos (inv_pos.mpr hdR) _
  have hcpos : (0 : ℝ) < min (c₃ / (2 * (M : ℝ)))
      ((2 * (d : ℝ))⁻¹ ^ (2 * d * K * (M * (s₂ + 1)) + 1) / ((M * (s₂ + 1) : ℕ) : ℝ)) :=
    lt_min (div_pos hc₃ (by linarith)) (div_pos ha hρ₀R)
  refine ⟨_, hcpos, ?_⟩
  intro m ρ hρ hm B hB x hx y hy
  have hR0 : (0 : ℝ) ≤ (ρ : ℝ) ^ ((2 : ℤ) - d) := zpow_nonneg (Nat.cast_nonneg _) _
  by_cases hbig : M * (s₂ + 1) ≤ ρ
  · have hs2 : s₂ + 1 ≤ ρ / M := add_one_le_ediv_of_mul_le M s₂ ρ hM1 hbig
    have hsρ : ρ / M ≤ ρ := Nat.div_le_self ρ M
    have hρs : ρ ≤ 2 * M * (ρ / M) := le_two_mul_mul_ediv_of_one_le_ediv M ρ hM1 (by omega)
    have hMs : M * (ρ / M) ≤ ρ := Nat.mul_div_le ρ M
    have hm' : m ≤ 2 * K * M * (ρ / M) := le_two_mul_mul_mul_of_le_mul K M (ρ / M) ρ m hm hρs
    have hB' : ∀ z ∈ box d (m + M * (ρ / M)), z ∈ B :=
      fun z hz => hB z (mem_box_of_mem_box_of_le (by omega) hz)
    have hg := H (ρ / M) (by omega) m hm' B hB' x hx y hy
    have h53 := rpow_two_sub_le_two_mul_rpow_two_sub M (ρ / M) ρ hM1 (by omega) hsρ hρs hd
    exact mul_le_of_le_div_two_mul_of_le _ c₃ (M : ℝ) _ _ _ hMR (min_le_left _ _) hc₃.le hR0 h53 hg
  · have hρle : ρ ≤ M * (s₂ + 1) := by omega
    have hnorm : graphNorm (x - y) ≤ 2 * d * K * (M * (s₂ + 1)) :=
      le_trans (graphNorm_sub_le_two_mul_mul_of_mem_box m hx hy)
          (two_mul_mul_le_two_mul_mul_mul_of_le K m ρ _ hm hρle)
    have hB' : ∀ z ∈ box d m, z ∈ B :=
      fun z hz => hB z (mem_box_of_mem_box_of_le (by omega) hz)
    have hg := inv_two_mul_pow_add_one_le_killedGreenReal hd B m _ hB' hx hy hnorm
    have hRρ₀ : (ρ : ℝ) ^ ((2 : ℤ) - d) ≤ ((M * (s₂ + 1) : ℕ) : ℝ) :=
      le_trans (rpow_two_sub_le_self ρ hρ hd) (by exact_mod_cast hρle)
    exact mul_le_of_le_div_of_le _ _ _ _ _ hcpos.le hρ₀R (min_le_right _ _) hRρ₀ hg

end GreenTwoSided

end LatticeProb
