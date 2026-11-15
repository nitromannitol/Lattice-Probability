import LatticeProb.Walk.HarmonicDifference.Midpoint

/-!
# Boundary geometry for the pair chain

Successors of an interior pair have both walkers in the graph closure of the
ball, and their separation stays between the absorbing levels. A quadratic
barrier dominates the paired difference on the boundary of the pair set.
-/

namespace LatticeProb.HarmonicDifference

variable {d : ℕ}

private theorem add_unit_mem_closure {n : ℕ} {x : Site d} (hx : x ∈ ball n) (i : Fin d) :
    x + unit i ∈ Graph.closureN (lattice d) (ball n) := by
  by_cases h : x + unit i ∈ ball n
  · exact Or.inl h
  · right
    refine ⟨h, x, hx, i, ?_⟩
    right
    rfl

private theorem sub_unit_mem_closure {n : ℕ} {x : Site d} (hx : x ∈ ball n) (i : Fin d) :
    x - unit i ∈ Graph.closureN (lattice d) (ball n) := by
  by_cases h : x - unit i ∈ ball n
  · exact Or.inl h
  · right
    refine ⟨h, x, hx, i, ?_⟩
    left
    abel

/-- Each successor of an interior pair has both walkers in the graph closure of
    the ball and separation between the absorbing levels. -/
theorem pairSucc_geometry (i : Fin d) (n L : ℕ) {s t : Site d × ℤ}
    (hs : s ∈ pairU i n L) (ht : t ∈ pairSucc i s) :
    0 ≤ t.2 ∧ t.2 ≤ L ∧
      t.1 ∈ Graph.closureN (lattice d) (ball n) ∧
      t.1 + t.2 • unit i ∈ Graph.closureN (lattice d) (ball n) := by
  obtain ⟨h1, hL, hx, hy⟩ := hs
  simp only [pairSucc, Finset.mem_union, Finset.mem_biUnion, Finset.mem_insert,
    Finset.mem_singleton] at ht
  rcases ht with ⟨j, hj, rfl | rfl⟩ | rfl | rfl | rfl | rfl | rfl
  · refine ⟨by omega, by omega, add_unit_mem_closure hx j, ?_⟩
    have heq : s.1 + unit j + s.2 • unit i = (s.1 + s.2 • unit i) + unit j := by abel
    rw [heq]
    exact add_unit_mem_closure hy j
  · refine ⟨by omega, by omega, sub_unit_mem_closure hx j, ?_⟩
    have heq : s.1 - unit j + s.2 • unit i = (s.1 + s.2 • unit i) - unit j := by abel
    rw [heq]
    exact sub_unit_mem_closure hy j
  · refine ⟨by omega, by omega, add_unit_mem_closure hx i, ?_⟩
    have heq : s.1 + unit i + (s.2 - 1) • unit i = s.1 + s.2 • unit i := by
      rw [sub_smul, one_smul]; abel
    rw [heq]
    exact Or.inl hy
  · refine ⟨by omega, by omega, sub_unit_mem_closure hx i, ?_⟩
    have heq : s.1 - unit i + (s.2 + 1) • unit i = s.1 + s.2 • unit i := by
      rw [add_smul, one_smul]; abel
    rw [heq]
    exact Or.inl hy
  · refine ⟨by omega, by omega, Or.inl hx, ?_⟩
    have heq : s.1 + (s.2 + 1) • unit i = (s.1 + s.2 • unit i) + unit i := by
      rw [add_smul, one_smul]; abel
    rw [heq]
    exact add_unit_mem_closure hy i
  · refine ⟨by omega, by omega, Or.inl hx, ?_⟩
    have heq : s.1 + (s.2 - 1) • unit i = (s.1 + s.2 • unit i) - unit i := by
      rw [sub_smul, one_smul]; abel
    rw [heq]
    exact sub_unit_mem_closure hy i
  · exact ⟨by omega, by omega, Or.inl hx, Or.inl hy⟩

/-- The real Euclidean representative of a lattice site. -/
noncomputable def siteEmbedding (x : Site d) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun k => (x k : ℝ))

/-- The distance from the midpoint to either walker is half the separation. -/
theorem midpoint_sub_first (i : Fin d) (s : Site d × ℤ) :
    midpoint i s - siteEmbedding s.1 = EuclideanSpace.single i ((s.2 : ℝ) / 2) := by
  ext k
  simp only [midpoint, siteEmbedding, PiLp.sub_apply, PiLp.single_apply]
  split_ifs <;> ring

/-- The distance from the midpoint to the second walker is half the separation. -/
theorem midpoint_sub_second (i : Fin d) (s : Site d × ℤ) :
    midpoint i s - siteEmbedding (s.1 + s.2 • unit i) =
      EuclideanSpace.single i (-(s.2 : ℝ) / 2) := by
  ext k
  simp only [midpoint, siteEmbedding, PiLp.sub_apply, PiLp.single_apply,
    Pi.add_apply, zsmul_eq_mul, Pi.mul_apply, Pi.intCast_apply, Int.cast_add, Int.cast_mul, unit,
    Pi.single_apply, Int.cast_ite, Int.cast_one, Int.cast_zero]
  split_ifs <;> simp
  ring

/-- If either walker is outside the ball, the midpoint is at least half the
    separation from its boundary. -/
theorem midpoint_lower_bound (i : Fin d) (n : ℕ) (s : Site d × ℤ)
    (hD : 0 ≤ s.2) (hout : s.1 ∉ ball n ∨ s.1 + s.2 • unit i ∉ ball n) :
    (n : ℝ) ≤ ‖midpoint i s‖ + (s.2 : ℝ) / 2 := by
  have hD' : (0 : ℝ) ≤ s.2 := by exact_mod_cast hD
  have hnorm (x : Site d) (h : x ∉ ball n) : (n : ℝ) ≤ ‖siteEmbedding x‖ := by
    have hz : (WithLp.toLp 2 (fun j => (((0 : Site d) j) : ℝ)) :
        EuclideanSpace ℝ (Fin d)) = 0 := by
      ext j
      simp
    change ¬ ‖siteEmbedding x - WithLp.toLp 2 (fun j => (((0 : Site d) j) : ℝ))‖ <
      (n : ℝ) at h
    rw [hz, sub_zero] at h
    exact le_of_not_gt h
  rcases hout with hx | hy
  · have htriangle := norm_le_norm_add_norm_sub' (siteEmbedding s.1) (midpoint i s)
    have hn : ‖siteEmbedding s.1 - midpoint i s‖ = (s.2 : ℝ) / 2 := by
      rw [norm_sub_rev, midpoint_sub_first, PiLp.norm_single, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    linarith [hnorm s.1 hx]
  · have htriangle := norm_le_norm_add_norm_sub' (siteEmbedding (s.1 + s.2 • unit i)) (midpoint i s)
    have hn : ‖siteEmbedding (s.1 + s.2 • unit i) - midpoint i s‖ = (s.2 : ℝ) / 2 := by
      rw [norm_sub_rev, midpoint_sub_second, PiLp.norm_single, Real.norm_eq_abs]
      rw [abs_div, abs_neg, abs_of_nonneg hD']
      norm_num
    linarith [hnorm (s.1 + s.2 • unit i) hy]

/-- The quadratic barrier controls the difference at every boundary successor. -/
theorem quadraticBarrier_boundary (i : Fin d) (n L : ℕ) (α M : ℝ)
    (hL : 0 < L) (hwidth : 2 * ((L : ℝ) - 1) ≤ n)
    (hα : 0 ≤ α) (hscale : 1 ≤ α * (3 * (n : ℝ) / 4) ^ 2)
    (hM : 0 ≤ M) (f : Site d → ℝ)
    (hf : ∀ x ∈ Graph.closureN (lattice d) (ball n), |f x| ≤ M)
    {s t : Site d × ℤ} (hs : s ∈ pairU i n L) (ht : t ∈ pairSucc i s)
    (hnot : t ∉ pairU i n L) :
    |f (t.1 + t.2 • unit i) - f t.1| ≤ quadraticBarrier i L α M t := by
  obtain ⟨hD0, hDL, hx, hy⟩ := pairSucc_geometry i n L hs ht
  have hD0' : (0 : ℝ) ≤ t.2 := by exact_mod_cast hD0
  have hDL' : (t.2 : ℝ) ≤ L := by exact_mod_cast hDL
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hsepFactor : 0 ≤ 2 * (L : ℝ) - t.2 := by linarith
  have hsep : 0 ≤ (t.2 : ℝ) * (2 * L - t.2) := mul_nonneg hD0' hsepFactor
  have hterm : 0 ≤ ‖midpoint i t‖ ^ 2 + ((d : ℝ) / 2) *
      ((t.2 : ℝ) * (2 * L - t.2)) := by positivity
  have hlin : 0 ≤ (1 / (L : ℝ)) * (t.2 : ℝ) := by positivity
  have hbar : 0 ≤ quadraticBarrier i L α M t := by
    unfold quadraticBarrier
    exact mul_nonneg (by positivity) (add_nonneg hlin (mul_nonneg hα hterm))
  by_cases hzero : t.2 = 0
  · simpa only [hzero, zero_smul, add_zero, sub_self, abs_zero] using hbar
  have hdiff : |f (t.1 + t.2 • unit i) - f t.1| ≤ 2 * M := by
    calc
      _ ≤ |f (t.1 + t.2 • unit i)| + |f t.1| := abs_sub _ _
      _ ≤ 2 * M := by linarith [hf _ hx, hf _ hy]
  by_cases htop : t.2 = (L : ℤ)
  · have heq : (t.2 : ℝ) = L := by exact_mod_cast htop
    have hlin' : (1 / (L : ℝ)) * (t.2 : ℝ) = 1 := by
      rw [heq]
      field_simp
    have : 2 * M ≤ quadraticBarrier i L α M t := by
      unfold quadraticBarrier
      rw [hlin']
      nlinarith [mul_nonneg hα hterm]
    exact hdiff.trans this
  · have hD1 : 1 ≤ t.2 := by omega
    have hDtop : t.2 ≤ (L : ℤ) - 1 := by omega
    have hout : t.1 ∉ ball n ∨ t.1 + t.2 • unit i ∉ ball n := by
      by_contra h
      push Not at h
      exact hnot ⟨hD1, hDtop, h.1, h.2⟩
    have hDtop' : (t.2 : ℝ) ≤ (L : ℝ) - 1 := by exact_mod_cast hDtop
    have hn : (3 * (n : ℝ) / 4) ≤ ‖midpoint i t‖ := by
      have hm := midpoint_lower_bound i n t hD0 hout
      linarith
    have hn0 : (0 : ℝ) ≤ 3 * (n : ℝ) / 4 := by positivity
    have hsq : (3 * (n : ℝ) / 4) ^ 2 ≤ ‖midpoint i t‖ ^ 2 := by nlinarith [norm_nonneg (midpoint i t)]
    have hαsq : 1 ≤ α * ‖midpoint i t‖ ^ 2 := by
      exact hscale.trans (mul_le_mul_of_nonneg_left hsq hα)
    have hrest : 0 ≤ ((d : ℝ) / 2) * ((t.2 : ℝ) * (2 * L - t.2)) := by positivity
    have hbig : 1 ≤ (1 / (L : ℝ)) * (t.2 : ℝ) + α *
        (‖midpoint i t‖ ^ 2 + ((d : ℝ) / 2) * ((t.2 : ℝ) * (2 * L - t.2))) := by
      nlinarith [mul_nonneg hα hrest]
    have : 2 * M ≤ quadraticBarrier i L α M t := by
      unfold quadraticBarrier
      nlinarith
    exact hdiff.trans this

end LatticeProb.HarmonicDifference
