import LatticeProb.Graph.LongRangeKernel.Lattice
import LatticeProb.Walk.SRWPos

/-!
# Polynomial volume growth of the reference lattice

The nearest-neighbour graph distance is the sum of coordinate distances. Counting
coordinate cubes inside and outside its closed balls gives polynomial volume growth.
-/

namespace LatticeProb.Graph.LongRangeKernel

open LatticeProb
open scoped ENNReal NNReal

noncomputable section

variable {d : ℕ}

/-- A signed coordinate step is an edge of the reference lattice. -/
theorem lattice_adj_add_dirVec (x : Site d) (a : Dir d) :
    (lattice d).Adj x (x + dirVec a) := by
  rcases a with ⟨i, b⟩
  cases b with
  | false =>
    rw [dirVec_eq_neg_unit, ← sub_eq_add_neg]
    exact Zd.adj_iff.mpr ⟨i, Or.inr rfl⟩
  | true =>
    rw [dirVec_eq_unit]
    exact Zd.adj_iff.mpr ⟨i, Or.inl rfl⟩

/-- Every lattice edge has displacement of graph norm one. -/
theorem graphNorm_sub_eq_one_of_adj {x y : Site d} (h : (lattice d).Adj x y) :
    graphNorm (y - x) = 1 := by
  obtain ⟨i, rfl | rfl⟩ := Zd.adj_iff.mp h
  · simpa only [add_sub_cancel_left, ← dirVec_eq_unit i] using
      graphNorm_dirVec ((i, true) : Dir d)
  · have heq : x - unit i - x = -unit i := by abel
    rw [heq, graphNorm_neg, ← dirVec_eq_unit i, graphNorm_dirVec]

/-- A walk's length bounds the sum of coordinate distances between its endpoints. -/
theorem graphNorm_sub_le_walk_length {x y : Site d} (p : (lattice d).Walk x y) :
    graphNorm (y - x) ≤ p.length := by
  induction p with
  | nil => simp only [sub_self, graphNorm_zero, SimpleGraph.Walk.length_nil, le_refl]
  | @cons x z y h p ih =>
    have heq : y - x = (y - z) + (z - x) := by abel
    rw [heq]
    have ht := graphNorm_add_le (y - z) (z - x)
    rw [graphNorm_sub_eq_one_of_adj h] at ht
    simpa only [SimpleGraph.Walk.length_cons] using ht.trans (Nat.add_le_add_right ih 1)

/-- The nearest-neighbour graph distance is exactly the coordinate `ℓ¹` distance. -/
theorem lattice_dist_eq_graphNorm (hd : 0 < d) (x y : Site d) :
    (lattice d).dist x y = graphNorm (y - x) := by
  have hconn : (lattice d).Connected := weightedLattice_connected hd
  apply Nat.le_antisymm
  · generalize hn : graphNorm (y - x) = n
    induction n using Nat.strong_induction_on generalizing x y with
    | h n ih =>
      by_cases hxy : y - x = 0
      · have hy : y = x := sub_eq_zero.mp hxy
        subst y
        simp only [SimpleGraph.dist_self, Nat.zero_le]
      · obtain ⟨a, ha⟩ := exists_dirVec_graphNorm_eq_sub_one hxy
        have heq : y + dirVec a - x = (y - x) + dirVec a := by abel
        have hnorm : graphNorm (y + dirVec a - x) = n - 1 := by
          rw [heq, ha, hn]
        have hnpos : 0 < n := by
          rw [← hn]
          exact Nat.pos_of_ne_zero (graphNorm_eq_zero_iff.not.mpr hxy)
        have hi := ih (n - 1) (by omega) x (y + dirVec a) hnorm
        have ht := hconn.dist_triangle (u := x) (v := y + dirVec a) (w := y)
        have hedge : (lattice d).dist (y + dirVec a) y = 1 :=
          SimpleGraph.dist_eq_one_iff_adj.mpr (lattice_adj_add_dirVec y a).symm
        rw [hedge] at ht
        omega
  · obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist x y
    rw [← hp]
    exact graphNorm_sub_le_walk_length p

/-- Unit vertex masses identify volume with the translated coordinate-distance count. -/
theorem weightedLattice_volume_eq_tsum (hd : 0 < d) (x : Site d) (r : ℝ) :
    (weightedLattice d hd).volume x r =
      ∑' y : Site d, if (graphNorm y : ℝ) ≤ r then (1 : ℝ≥0∞) else 0 := by
  classical
  unfold WeightedGraph.volume
  simp only [WeightedGraph.ball, weightedLattice_mass, ENNReal.coe_one,
    Set.mem_setOf_eq]
  change (∑' y : Site d,
    if ((lattice d).dist x y : ℝ) ≤ r then (1 : ℝ≥0∞) else 0) = _
  simp_rw [lattice_dist_eq_graphNorm hd]
  have h := (Equiv.addLeft x).tsum_eq (fun y : Site d =>
    if (graphNorm (y - x) : ℝ) ≤ r then (1 : ℝ≥0∞) else 0)
  simpa only [Equiv.coe_addLeft, add_sub_cancel_left] using h.symm

/-- A coordinate cube of radius `n` has graph norm at most `d * n`. -/
theorem graphNorm_le_mul_of_mem_box {n : ℕ} {y : Site d}
    (hy : y ∈ boxFinset (0 : Site d) n) : graphNorm y ≤ d * n := by
  have hc := supNorm_le_iff.mp (mem_boxFinset_zero_iff.mp hy)
  have hb : ∀ i, (y i).natAbs ≤ n := by
    intro i
    have hi := hc i
    rw [Int.abs_eq_natAbs] at hi
    exact_mod_cast hi
  calc
    graphNorm y ≤ ∑ _i : Fin d, n := Finset.sum_le_sum (fun i _ => hb i)
    _ = d * n := by simp only [Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]

/-- The graph ball is bounded above by its enclosing coordinate cube. -/
theorem weightedLattice_volume_le_cube (hd : 0 < d) (x : Site d) {r : ℝ}
    (hr : 0 ≤ r) :
    (weightedLattice d hd).volume x r ≤ ((2 * ⌊r⌋₊ + 1) ^ d : ℕ) := by
  classical
  rw [weightedLattice_volume_eq_tsum hd]
  have hbound : ∀ y : Site d, (graphNorm y : ℝ) ≤ r →
      y ∈ boxFinset (0 : Site d) ⌊r⌋₊ := by
    intro y hy
    apply mem_boxFinset_zero_iff.mpr
    exact (supNorm_le_graphNorm y).trans ((Nat.le_floor_iff hr).mpr hy)
  calc
    (∑' y : Site d, if (graphNorm y : ℝ) ≤ r then (1 : ℝ≥0∞) else 0) ≤
        ∑' y : Site d, if y ∈ boxFinset (0 : Site d) ⌊r⌋₊ then
          (1 : ℝ≥0∞) else 0 := by
      apply ENNReal.tsum_le_tsum
      intro y
      split_ifs with hy hm
      · exact le_rfl
      · exact (hm (hbound y hy)).elim
      · exact zero_le
      · exact le_rfl
    _ = ((2 * ⌊r⌋₊ + 1) ^ d : ℕ) := by
      rw [tsum_eq_sum (s := boxFinset (0 : Site d) ⌊r⌋₊)
        (fun y hy => if_neg hy)]
      simp only [Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const, nsmul_eq_mul,
        mul_one, card_boxFinset_zero]

/-- Every cube whose `d * n` radius fits in the ball contributes its full cardinality. -/
theorem cube_le_weightedLattice_volume (hd : 0 < d) (x : Site d) {r : ℝ}
    (n : ℕ) (hn : (d : ℝ) * n ≤ r) :
    (((2 * n + 1) ^ d : ℕ) : ℝ≥0∞) ≤ (weightedLattice d hd).volume x r := by
  classical
  rw [weightedLattice_volume_eq_tsum hd]
  calc
    (((2 * n + 1) ^ d : ℕ) : ℝ≥0∞) =
        ∑ y ∈ boxFinset (0 : Site d) n, (1 : ℝ≥0∞) := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one, card_boxFinset_zero]
    _ ≤ ∑ y ∈ boxFinset (0 : Site d) n,
        if (graphNorm y : ℝ) ≤ r then (1 : ℝ≥0∞) else 0 := by
      apply Finset.sum_le_sum
      intro y hy
      have hb : (graphNorm y : ℝ) ≤ (d : ℝ) * n := by
        exact_mod_cast graphNorm_le_mul_of_mem_box hy
      rw [if_pos (hb.trans hn)]
    _ ≤ _ := ENNReal.sum_le_tsum _

/-- Closed graph balls of the normalized lattice have uniform polynomial volume growth. -/
theorem weightedLattice_volume_comparable (hd : 0 < d) :
    ∃ C_h : ℝ, 1 < C_h ∧ ∀ (x : Site d) (r : ℝ), 0 < r →
      ENNReal.ofReal (C_h⁻¹ * latticeVolumeProfile d r) ≤
          (weightedLattice d hd).volume x r ∧
      (weightedLattice d hd).volume x r ≤
        ENNReal.ofReal (C_h * latticeVolumeProfile d r) := by
  let B : ℝ := 2 * (1 + d)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hB : 2 ≤ B := by dsimp [B]; nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hBp : 0 < B ^ d := pow_pos (by linarith) d
  refine ⟨B ^ d + 1, by linarith, ?_⟩
  intro x r hr
  have hprofile : 0 ≤ (1 + r) ^ d := by positivity
  have hcast (n : ℕ) : ENNReal.ofReal ((2 * (n : ℝ) + 1) ^ d) =
      (((2 * n + 1) ^ d : ℕ) : ℝ≥0∞) := by
    have heq : ((((2 * n + 1) ^ d : ℕ) : ℝ)) = (2 * (n : ℝ) + 1) ^ d := by
      push_cast
      rfl
    rw [← heq, ENNReal.ofReal_natCast]
  constructor
  · let n : ℕ := ⌊r / (d : ℝ)⌋₊
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hnle : (n : ℝ) ≤ r / (d : ℝ) := Nat.floor_le (by positivity)
    have hnlt : r / (d : ℝ) < (n : ℝ) + 1 := Nat.lt_floor_add_one _
    have hnr : (d : ℝ) * n ≤ r := by
      have := (le_div_iff₀ hdR).mp hnle
      nlinarith
    have hsmall : 1 + r ≤ B * (2 * (n : ℝ) + 1) := by
      have hrl := (div_lt_iff₀ hdR).mp hnlt
      dsimp [B]
      nlinarith
    have hpow : (1 + r) ^ d ≤ (B ^ d + 1) * (2 * (n : ℝ) + 1) ^ d := by
      calc
        (1 + r) ^ d ≤ (B * (2 * (n : ℝ) + 1)) ^ d :=
          pow_le_pow_left₀ (by linarith) hsmall d
        _ = B ^ d * (2 * (n : ℝ) + 1) ^ d := mul_pow _ _ _
        _ ≤ (B ^ d + 1) * (2 * (n : ℝ) + 1) ^ d := by
          have hp : 0 ≤ (2 * (n : ℝ) + 1) ^ d := by positivity
          nlinarith
    have hlow : (B ^ d + 1)⁻¹ * (1 + r) ^ d ≤ (2 * (n : ℝ) + 1) ^ d := by
      exact (inv_mul_le_iff₀ (show 0 < B ^ d + 1 by linarith)).mpr hpow
    apply (ENNReal.ofReal_le_ofReal hlow).trans
    rw [hcast]
    exact cube_le_weightedLattice_volume hd x n hnr
  · have hf : (⌊r⌋₊ : ℝ) ≤ r := Nat.floor_le hr.le
    have hc : 2 * (⌊r⌋₊ : ℝ) + 1 ≤ B * (1 + r) := by
      nlinarith
    have hpow : (2 * (⌊r⌋₊ : ℝ) + 1) ^ d ≤ (B ^ d + 1) * (1 + r) ^ d := by
      calc
        (2 * (⌊r⌋₊ : ℝ) + 1) ^ d ≤ (B * (1 + r)) ^ d :=
          pow_le_pow_left₀ (by positivity) hc d
        _ = B ^ d * (1 + r) ^ d := mul_pow _ _ _
        _ ≤ (B ^ d + 1) * (1 + r) ^ d := by nlinarith
    apply (weightedLattice_volume_le_cube hd x hr.le).trans
    have h := ENNReal.ofReal_le_ofReal hpow
    rw [hcast] at h
    exact h

end

end LatticeProb.Graph.LongRangeKernel
