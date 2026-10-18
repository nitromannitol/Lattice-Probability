import LatticeProb.Walk.GreenTwoSided.UpperBound

/-!
# Diagonal of the killed Green function

For a finite set `B ⊆ ℤ^d` the killed Green function `Graph.killedGreenReal (lattice d) B x y`
is the total mass `∑' k, killedHeat k x y` divided by `2d`, by
`GreenTwoSided.killedGreenReal_eq_tsum_killedHeat_div`.

The diagonal is bounded by a dimension-dependent constant for `d ≥ 3` and by `C log (L + 2)`
for `d = 2` and `B ⊆ box 2 L`. For `d ≥ 2`, the row sum is bounded by `C_d (L + 1)^2`, uniformly
in `B ⊆ box d L` and the starting site. The proofs use the free heat bound and a geometric
survival bound. A positive-diagonal control records a genuine nonzero value of the kernel.
-/

namespace LatticeProb

namespace GreenTwoSided

variable {d : ℕ}

/-- For `d ≥ 3`, the diagonal of the killed Green function is bounded by a constant `C > 0`
depending only on `d`, uniformly over all finite `B`. -/
theorem killedGreen_diag_le_const_of_three_le (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ B : Finset (Site d),
      Graph.killedGreenReal (lattice d) (B : Set (Site d)) 0 0 ≤ C := by
  obtain ⟨C₂, hC₂pos, hC₂⟩ := srwHeat_le_mul_rpow_neg_half (d := d) (by omega)
  have hd3 : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hsum : Summable (fun k : ℕ =>
      C₂ * (k : ℝ) ^ (-(d : ℝ) / 2) + (if k = 0 then (1 : ℝ) else 0)) :=
    Summable.add ((Real.summable_nat_rpow.mpr (by linarith)).mul_left C₂)
      (hasSum_ite_eq 0 (1 : ℝ)).summable
  have hgnn : ∀ k : ℕ, 0 ≤ C₂ * (k : ℝ) ^ (-(d : ℝ) / 2) + (if k = 0 then (1 : ℝ) else 0) :=
    fun k => add_nonneg (mul_nonneg hC₂pos.le (Real.rpow_nonneg (Nat.cast_nonneg k) _))
      (by split_ifs <;> norm_num)
  have hpt : ∀ (B : Finset (Site d)) (k : ℕ),
      Graph.killedHeat (lattice d) (B : Set (Site d)) k 0 0
        ≤ C₂ * (k : ℝ) ^ (-(d : ℝ) / 2) + (if k = 0 then (1 : ℝ) else 0) := by
    intro B k
    have h := killedHeat_le_srwHeat_sub (B : Set (Site d)) k 0 0
    rw [sub_self] at h
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have hnn : (0 : ℝ) ≤ C₂ * ((0 : ℕ) : ℝ) ^ (-(d : ℝ) / 2) :=
        mul_nonneg hC₂pos.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      have h1 : srwHeat d 0 0 = 1 := by simp
      rw [if_pos rfl]
      linarith
    · have h2 := hC₂ k hk 0
      rw [if_neg hk.ne']
      linarith
  refine ⟨(∑' k : ℕ, (C₂ * (k : ℝ) ^ (-(d : ℝ) / 2) + (if k = 0 then (1 : ℝ) else 0)))
      / (2 * (d : ℝ)) + 1, ?_, ?_⟩
  · have h0 : (0 : ℝ) ≤ (∑' k : ℕ, (C₂ * (k : ℝ) ^ (-(d : ℝ) / 2)
        + (if k = 0 then (1 : ℝ) else 0))) / (2 * (d : ℝ)) :=
      div_nonneg (tsum_nonneg hgnn) (by positivity)
    linarith
  · intro B
    rw [killedGreenReal_eq_tsum_killedHeat_div (by omega : 1 ≤ d) B 0 0]
    have hle : ∑' k : ℕ, Graph.killedHeat (lattice d) (B : Set (Site d)) k 0 0
        ≤ ∑' k : ℕ, (C₂ * (k : ℝ) ^ (-(d : ℝ) / 2) + (if k = 0 then (1 : ℝ) else 0)) := by
      refine Real.tsum_le_of_sum_range_le (fun k => Network.killedHeat_nonneg (B : Set (Site d)) k 0 0)
        (fun n => ?_)
      exact le_trans (Finset.sum_le_sum fun k _ => hpt B k)
        (Summable.sum_le_tsum (Finset.range n) (fun k _ => hgnn k) hsum)
    have hdiv := div_le_div_of_nonneg_right hle (by positivity : (0 : ℝ) ≤ 2 * (d : ℝ))
    have h1 : (0 : ℝ) ≤ 1 := zero_le_one
    linarith

/-- Positive-diagonal control: for `d ≥ 1` the killed Green function at the origin of the
nonempty set `{0}` is strictly positive, so the diagonal is not a zero or default object. -/
theorem killedGreen_diag_pos_control (hd : 1 ≤ d) :
    0 < Graph.killedGreenReal (lattice d) (({0} : Finset (Site d)) : Set (Site d)) 0 0 := by
  rw [killedGreenReal_eq_tsum_killedHeat_div hd ({0} : Finset (Site d)) 0 0]
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨q, hq⟩ := Infinite.exists_notMem_finset ({0} : Finset (Site d))
  have hs := Network.summable_killedHeat (Graph.Zd.latticeConnected d) ({0} : Finset (Site d)) hq 0 0
  have h0 : Graph.killedHeat (lattice d) (({0} : Finset (Site d)) : Set (Site d)) 0 0 0 = 1 := by
    simp [Network.killedHeat_zero]
  have hle : Graph.killedHeat (lattice d) (({0} : Finset (Site d)) : Set (Site d)) 0 0 0
      ≤ ∑' k : ℕ, Graph.killedHeat (lattice d) (({0} : Finset (Site d)) : Set (Site d)) k 0 0 :=
    hs.le_tsum 0 (fun k _ => Network.killedHeat_nonneg (({0} : Finset (Site d)) : Set (Site d)) k 0 0)
  have hpos : (0 : ℝ) < ∑' k : ℕ, Graph.killedHeat (lattice d) (({0} : Finset (Site d)) : Set (Site d)) k 0 0 := by
    linarith
  have h2d : (0 : ℝ) < 2 * (d : ℝ) := by
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  exact div_pos hpos h2d

/-- Head of the `d = 2` killed heat series: the on-diagonal Gaussian bound gives
`killedHeat k 0 0 ≤ C₂ k⁻¹` for `k ≥ 1`, and the harmonic sum `∑_{k<N} k⁻¹` is at most
`1 + log N` (Mathlib's `harmonic_le_one_add_log`). -/
private theorem sum_range_killedHeat_two_le_harmonic (C₂ : ℝ) (hC₂ : 0 < C₂)
    (hC : ∀ (k : ℕ), 1 ≤ k → ∀ w : Site 2,
      srwHeat 2 k w ≤ C₂ * (k : ℝ) ^ (-((2 : ℕ) : ℝ) / 2))
    (B : Finset (Site 2)) (N : ℕ) (hN : 1 ≤ N) :
    ∑ k ∈ Finset.range N, Graph.killedHeat (lattice 2) (B : Set (Site 2)) k 0 0
      ≤ C₂ * (1 + Real.log (N : ℝ)) + 1 := by
  have hpt : ∀ k : ℕ, 1 ≤ k → Graph.killedHeat (lattice 2) (B : Set (Site 2)) k 0 0
      ≤ C₂ * (k : ℝ)⁻¹ := by
    intro k hk
    have h := killedHeat_le_srwHeat_sub (B : Set (Site 2)) k 0 0
    rw [sub_self] at h
    have h2 := hC k hk 0
    have hpow : (k : ℝ) ^ (-((2 : ℕ) : ℝ) / 2) = (k : ℝ)⁻¹ := by
      rw [show -((2 : ℕ) : ℝ) / 2 = -1 by norm_num, Real.rpow_neg_one]
    rw [hpow] at h2
    linarith
  have h0 : Graph.killedHeat (lattice 2) (B : Set (Site 2)) 0 0 0 ≤ 1 := by
    have h := killedHeat_le_srwHeat_sub (B : Set (Site 2)) 0 0 0
    rw [sub_self] at h
    have h1 : srwHeat 2 0 0 = 1 := by simp
    linarith
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  rw [Finset.sum_range_succ']
  have hs : ∑ i ∈ Finset.range n, Graph.killedHeat (lattice 2) (B : Set (Site 2)) (i + 1) 0 0
      ≤ ∑ i ∈ Finset.range n, C₂ * ((i + 1 : ℕ) : ℝ)⁻¹ :=
    Finset.sum_le_sum fun i _ => hpt (i + 1) (by omega)
  have hh : ∑ i ∈ Finset.range n, C₂ * ((i + 1 : ℕ) : ℝ)⁻¹ = C₂ * ((harmonic n : ℚ) : ℝ) := by
    rw [← Finset.mul_sum]
    congr 1
    simp [harmonic]
  have hH := harmonic_le_one_add_log n
  have hlog : Real.log (n : ℝ) ≤ Real.log ((n + 1 : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact Real.log_le_log (by exact_mod_cast hn) (by push_cast; linarith)
  have hmul : C₂ * ((harmonic n : ℚ) : ℝ) ≤ C₂ * (1 + Real.log ((n + 1 : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_left (by linarith) hC₂.le
  linarith

/-- For `d = 2` the diagonal of the killed Green function is bounded by `C log (L + 2)`, with `C`
independent of `L` and of the finite set `B ⊆ box 2 L`. The bound holds for every `L`, in
particular for `L ≥ 1`. -/
theorem killedGreen_diag_two_le_log :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) (B : Finset (Site 2)), (∀ z ∈ B, z ∈ box 2 L) →
      Graph.killedGreenReal (lattice 2) (B : Set (Site 2)) 0 0 ≤ C * Real.log ((L : ℝ) + 2) := by
  obtain ⟨C₂, hC₂, hC⟩ := srwHeat_le_mul_rpow_neg_half (d := 2) (by norm_num)
  obtain ⟨K, hK1, hK⟩ := exists_nat_survival_le_half (d := 2) (by norm_num)
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK1
  have hlogK : 0 ≤ Real.log (K : ℝ) := Real.log_nonneg (by exact_mod_cast hK1)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = C₂ + C₂ * Real.log (K : ℝ) + 1 + 2 * C₂ := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by
    have := mul_nonneg hC₂.le hlogK
    linarith
  refine ⟨(2 * C₂ + M / Real.log 2) / 4, ?_, ?_⟩
  · have hq : 0 ≤ M / Real.log 2 := div_nonneg hM0 hlog2.le
    exact div_pos (by linarith) (by norm_num)
  intro L B hB
  have hNpos : 0 < K * (L + 1) ^ 2 := Nat.mul_pos (by omega) (pow_pos (Nat.succ_pos L) 2)
  have hsurv : ∀ x : Site 2, Network.survival (lattice 2) B (K * (L + 1) ^ 2) x ≤ 1 / 2 :=
    fun x => hK L B hB x
  have hH := sum_range_killedHeat_two_le_harmonic C₂ hC₂ hC B (K * (L + 1) ^ 2) hNpos
  have hT : ∀ n, ∑ k ∈ Finset.range n,
      Graph.killedHeat (lattice 2) (B : Set (Site 2)) (k + K * (L + 1) ^ 2) 0 0
        ≤ 2 * ((K * (L + 1) ^ 2 : ℕ) : ℝ)
            * (C₂ * (((K * (L + 1) ^ 2 : ℕ) : ℝ)) ^ (-((2 : ℕ) : ℝ) / 2)) :=
    fun n => sum_range_killedHeat_add_le_two_mul_rpow_neg_half (by norm_num) C₂ hC B
      (K * (L + 1) ^ 2) hNpos hsurv 0 0 n
  have htsum := tsum_killedHeat_le_add_of_sum_range_le B (K * (L + 1) ^ 2) 0 0 _ _ hH hT
  have hNinv : ((K * (L + 1) ^ 2 : ℕ) : ℝ)
      * (((K * (L + 1) ^ 2 : ℕ) : ℝ)) ^ (-((2 : ℕ) : ℝ) / 2) = 1 := by
    rw [show -((2 : ℕ) : ℝ) / 2 = -1 by norm_num, Real.rpow_neg_one]
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hNpos.ne')
  have hT2 : 2 * ((K * (L + 1) ^ 2 : ℕ) : ℝ)
      * (C₂ * (((K * (L + 1) ^ 2 : ℕ) : ℝ)) ^ (-((2 : ℕ) : ℝ) / 2)) = 2 * C₂ := by
    calc _ = 2 * C₂ * (((K * (L + 1) ^ 2 : ℕ) : ℝ)
          * (((K * (L + 1) ^ 2 : ℕ) : ℝ)) ^ (-((2 : ℕ) : ℝ) / 2)) := by ring
      _ = 2 * C₂ := by rw [hNinv, mul_one]
  have hfin : ∑' k : ℕ, Graph.killedHeat (lattice 2) (B : Set (Site 2)) k 0 0
      ≤ C₂ * (1 + Real.log ((K * (L + 1) ^ 2 : ℕ) : ℝ)) + 1 + 2 * C₂ := by
    rw [hT2] at htsum
    linarith
  have hcast : ((K * (L + 1) ^ 2 : ℕ) : ℝ) = (K : ℝ) * ((L : ℝ) + 1) ^ 2 := by
    norm_num
  have hNle : Real.log ((K * (L + 1) ^ 2 : ℕ) : ℝ)
      ≤ Real.log (K : ℝ) + 2 * Real.log ((L : ℝ) + 2) := by
    have hle : ((K * (L + 1) ^ 2 : ℕ) : ℝ) ≤ (K : ℝ) * ((L : ℝ) + 2) ^ 2 := by
      rw [hcast]
      have h1 : ((L : ℝ) + 1) ^ 2 ≤ ((L : ℝ) + 2) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 2
      exact mul_le_mul_of_nonneg_left h1 hKpos.le
    have hpos : (0 : ℝ) < ((K * (L + 1) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hNpos
    calc Real.log ((K * (L + 1) ^ 2 : ℕ) : ℝ)
        ≤ Real.log ((K : ℝ) * ((L : ℝ) + 2) ^ 2) := Real.log_le_log hpos hle
      _ = Real.log (K : ℝ) + 2 * Real.log ((L : ℝ) + 2) := by
          rw [Real.log_mul hKpos.ne' (pow_pos (by positivity : (0 : ℝ) < (L : ℝ) + 2) 2).ne',
            Real.log_pow]
          norm_num
  have hlogL : Real.log 2 ≤ Real.log ((L : ℝ) + 2) :=
    Real.log_le_log (by norm_num) (by linarith [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)])
  have hMA : M ≤ M / Real.log 2 * Real.log ((L : ℝ) + 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    exact mul_le_mul_of_nonneg_left hlogL hM0
  have hlogsplit : C₂ * (1 + Real.log ((K * (L + 1) ^ 2 : ℕ) : ℝ))
      ≤ C₂ * (1 + (Real.log (K : ℝ) + 2 * Real.log ((L : ℝ) + 2))) :=
    mul_le_mul_of_nonneg_left (by linarith) hC₂.le
  have hkey : ∑' k : ℕ, Graph.killedHeat (lattice 2) (B : Set (Site 2)) k 0 0
      ≤ (2 * C₂ + M / Real.log 2) * Real.log ((L : ℝ) + 2) := by
    linarith [hfin, hlogsplit, hMA, hMdef]
  rw [killedGreenReal_eq_tsum_killedHeat_div (d := 2) (by norm_num) B 0 0]
  calc (∑' k : ℕ, Graph.killedHeat (lattice 2) (B : Set (Site 2)) k 0 0)
        / (2 * ((2 : ℕ) : ℝ))
      ≤ ((2 * C₂ + M / Real.log 2) * Real.log ((L : ℝ) + 2)) / (2 * ((2 : ℕ) : ℝ)) :=
        div_le_div_of_nonneg_right hkey (by norm_num)
    _ = (2 * C₂ + M / Real.log 2) / 4 * Real.log ((L : ℝ) + 2) := by
        push_cast
        ring

/-- Row sums of the killed Green function are bounded uniformly in the starting point: for
`d ≥ 2` there is `C > 0` depending only on `d` such that for every `L`, every finite `B ⊆ box d L`,
and every `x`, `∑_{y ∈ B} G_B(x,y) ≤ C (L+1)^2`. The row sum is the survival series divided by
`2d`, controlled by the geometric block bound at `N = K (L+1)^2`. -/
theorem killedGreen_row_sum_le_sq (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) (B : Finset (Site d)), (∀ z ∈ B, z ∈ box d L) →
      ∀ x : Site d,
        ∑ y ∈ B, Graph.killedGreenReal (lattice d) (B : Set (Site d)) x y
          ≤ C * ((L : ℝ) + 1) ^ 2 := by
  obtain ⟨K, hK1, hK⟩ := exists_nat_survival_le_half (d := d) (by omega)
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK1
  refine ⟨(K : ℝ), hKpos, ?_⟩
  intro L B hB x
  have hNpos : 0 < K * (L + 1) ^ 2 := Nat.mul_pos (by omega) (pow_pos (Nat.succ_pos L) 2)
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : 1 ≤ d)
  have hdpos : (0 : ℝ) < 2 * (d : ℝ) := by linarith
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨q, hq⟩ := Infinite.exists_notMem_finset B
  have hsum : ∑ y ∈ B, ∑' k : ℕ, Graph.killedHeat (lattice d) (B : Set (Site d)) k x y
      = ∑' k : ℕ, Network.survival (lattice d) B k x := by
    rw [← Summable.tsum_finsetSum (fun y _ =>
      Network.summable_killedHeat (Graph.Zd.latticeConnected d) B hq x y)]
    rfl
  have hrow : ∑ y ∈ B, Graph.killedGreenReal (lattice d) (B : Set (Site d)) x y
      = (∑' k : ℕ, Network.survival (lattice d) B k x) / (2 * (d : ℝ)) := by
    rw [Finset.sum_congr rfl fun y _ => killedGreenReal_eq_tsum_killedHeat_div (by omega : 1 ≤ d) B x y,
      ← Finset.sum_div, hsum]
  have hS : ∑' k : ℕ, Network.survival (lattice d) B k x ≤ 2 * ((K * (L + 1) ^ 2 : ℕ) : ℝ) :=
    Real.tsum_le_of_sum_range_le (fun k => Network.survival_nonneg (G := lattice d) B k x)
      (fun n => sum_range_survival_le_two_mul B (K * (L + 1) ^ 2) hNpos (hK L B hB) x n)
  have hcast : ((K * (L + 1) ^ 2 : ℕ) : ℝ) = (K : ℝ) * ((L : ℝ) + 1) ^ 2 := by
    norm_num
  have hNnn : (0 : ℝ) ≤ (K : ℝ) * ((L : ℝ) + 1) ^ 2 := by positivity
  rw [hcast] at hS
  rw [hrow, div_le_iff₀ hdpos]
  nlinarith [hS, mul_nonneg hNnn (sub_nonneg.mpr hd1)]

end GreenTwoSided

end LatticeProb
