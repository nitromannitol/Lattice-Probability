import LatticeProb.Walk.HarmonicDifference.Boundary
import LatticeProb.Walk.HarmonicDifference.Arithmetic

/-!
# Harmonic difference estimate

A pair-chain barrier bounds the difference of a harmonic function at the
origin and a neighbouring lattice point in terms of its boundary supremum.
-/

namespace LatticeProb.HarmonicDifference

variable {d : ℕ}

/-- The origin belongs to every lattice ball of positive radius. -/
theorem zero_mem_ball (n : ℕ) (hn : 0 < n) : (0 : Site d) ∈ ball n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [ball, Set.mem_ofPred_eq]
  have hz : (WithLp.toLp 2 (fun j => (((0 : Site d) j) : ℝ)) :
      EuclideanSpace ℝ (Fin d)) = 0 := by
    ext j
    simp
  rw [hz, sub_self, norm_zero]
  exact hn'

/-- A unit site belongs to every lattice ball of radius greater than one. -/
theorem unit_mem_ball (i : Fin d) (n : ℕ) (hn : 1 < n) : unit i ∈ ball n := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  simp only [ball, Set.mem_ofPred_eq]
  have hz : (WithLp.toLp 2 (fun j => (((0 : Site d) j) : ℝ)) :
      EuclideanSpace ℝ (Fin d)) = 0 := by
    ext j
    simp
  have hu : (WithLp.toLp 2 (fun j => ((unit i j) : ℝ)) : EuclideanSpace ℝ (Fin d)) =
      EuclideanSpace.single i 1 := by
    ext j
    simp [unit, PiLp.single_apply, Pi.single_apply]
  rw [hz, sub_zero, hu, PiLp.norm_single]
  simpa using hn'

/-- The initial pair lies inside the pair domain at radius at least two. -/
theorem initial_pair_mem (i : Fin d) (n L : ℕ) (hn : 1 < n) (hL : 2 ≤ L) :
    ((0 : Site d), (1 : ℤ)) ∈ pairU i n L := by
  refine ⟨by norm_num, by omega, zero_mem_ball n (by omega), ?_⟩
  simpa using unit_mem_ball i n hn

/-- The initial midpoint is half of the unit vector. -/
theorem midpoint_initial (i : Fin d) :
    midpoint i ((0 : Site d), (1 : ℤ)) = EuclideanSpace.single i (1 / 2) := by
  ext k
  simp only [midpoint, PiLp.single_apply, PiLp.toLp_apply, Pi.zero_apply, Int.cast_zero,
    Int.cast_one, zero_add]

/-- The squared norm of the initial midpoint is one quarter. -/
theorem midpoint_initial_norm_sq (i : Fin d) :
    ‖midpoint i ((0 : Site d), (1 : ℤ))‖ ^ 2 = 1 / 4 := by
  rw [midpoint_initial, PiLp.norm_single]
  norm_num

/-- The explicit value of the barrier at the initial pair. -/
theorem quadraticBarrier_initial (i : Fin d) (L α M : ℝ) :
    quadraticBarrier i L α M ((0 : Site d), (1 : ℤ)) =
      2 * M * (1 / L + α * (1 / 4 + (d : ℝ) / 2 * (2 * L - 1))) := by
  simp only [quadraticBarrier, midpoint_initial_norm_sq, Int.cast_one, mul_one, one_mul]

/-- The harmonic difference estimate for radii at least four. -/
theorem harmonic_difference_large (i : Fin d) (n : ℕ) (hn : 4 ≤ n)
    (f : Site d → ℝ) (M : ℝ)
    (hharm : ∀ z ∈ ball n, nbrSum f z - 2 * d * f z = 0)
    (hf : ∀ z ∈ Graph.closureN (lattice d) (ball n), |f z| ≤ M) :
    |f (unit i) - f 0| ≤ (2 * (d : ℝ) + 6) * M / n := by
  let L : ℕ := (n + 1) / 2
  let α : ℝ := 16 / (9 * (n : ℝ) ^ 2)
  have hnpos : 0 < n := by omega
  have hnreal : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hnrealpos : (0 : ℝ) < n := by linarith
  have hL2 : 2 ≤ L := by dsimp [L]; omega
  have hLpos : 0 < L := by omega
  have hLrealpos : (0 : ℝ) < L := by exact_mod_cast hLpos
  have hlo : n ≤ 2 * L := (half_radius_bounds n hn).2.1
  have hhi : 2 * L ≤ n + 1 := (half_radius_bounds n hn).2.2.2
  have hloreal : (n : ℝ) ≤ 2 * L := by exact_mod_cast hlo
  have hhireal : 2 * (L : ℝ) - 1 ≤ n := by
    have h : 2 * (L : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hhi
    linarith
  have hwidth : 2 * ((L : ℝ) - 1) ≤ n := by linarith
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hscale : 1 ≤ α * (3 * (n : ℝ) / 4) ^ 2 := by
    have h := barrier_scale_identity (n : ℝ) (ne_of_gt hnrealpos)
    dsimp [α]
    linarith
  have hM : 0 ≤ M := (abs_nonneg (f 0)).trans (hf 0 (Or.inl (zero_mem_ball n hnpos)))
  have hbd : ∀ s ∈ pairU i n L, ∀ t ∈ pairSucc i s, t ∉ pairU i n L →
      |f (t.1 + t.2 • unit i) - f t.1| ≤ quadraticBarrier i L α M t := by
    intro s hs t ht hnot
    exact quadraticBarrier_boundary i n L α M hLpos hwidth hα hscale hM f hf hs ht hnot
  have hs : ((0 : Site d), (1 : ℤ)) ∈ pairU i n L := initial_pair_mem i n L (by omega) hL2
  have h := pair_difference_le_barrier i n L f (quadraticBarrier i L α M) hharm
    (fun s _ => pairQ_quadraticBarrier_le i L α M s hα hM) hbd _ hs
  rw [quadraticBarrier_initial] at h
  have hnum := barrier_initial_numeric (n : ℝ) (L : ℝ) (d : ℝ) M hnreal hLrealpos
    hloreal hhireal (by positivity) hM
  dsimp [α] at h
  simpa using h.trans hnum

/-- The harmonic difference estimate for radii at most three. -/
theorem harmonic_difference_small (i : Fin d) (n : ℕ) (hn : 1 ≤ n) (hn3 : n ≤ 3)
    (f : Site d → ℝ) (M : ℝ)
    (hf : ∀ z ∈ Graph.closureN (lattice d) (ball n), |f z| ≤ M) :
    |f (unit i) - f 0| ≤ (2 * (d : ℝ) + 6) * M / n := by
  have hzero : (0 : Site d) ∈ ball n := zero_mem_ball n (by omega)
  have hu : unit i ∈ Graph.closureN (lattice d) (ball n) := by
    by_cases h : unit i ∈ ball n
    · exact Or.inl h
    · right
      refine ⟨h, 0, hzero, i, ?_⟩
      right
      simp
  have hM : 0 ≤ M := (abs_nonneg (f 0)).trans (hf 0 (Or.inl hzero))
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hnle : (n : ℝ) ≤ 3 := by exact_mod_cast hn3
  have hd : (0 : ℝ) ≤ d := by positivity
  have hbound : |f (unit i) - f 0| ≤ 2 * M := by
    calc
      _ ≤ |f (unit i)| + |f 0| := abs_sub _ _
      _ ≤ 2 * M := by linarith [hf (unit i) hu, hf 0 (Or.inl hzero)]
  apply hbound.trans
  apply (le_div_iff₀ hnpos).2
  nlinarith [mul_nonneg hM hd, mul_nonneg hM (show 0 ≤ (3 : ℝ) - n by linarith)]

/-- The harmonic difference estimate on a lattice ball and its graph closure. -/
theorem harmonic_difference (d : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ (f : Site d → ℝ) (M : ℝ),
      (∀ z ∈ ball n, nbrSum f z - 2 * d * f z = 0) →
      (∀ z ∈ Graph.closureN (lattice d) (ball n), |f z| ≤ M) →
      ∀ i : Fin d, |f (unit i) - f 0| ≤ C * M / n := by
  refine ⟨2 * d + 6, by positivity, ?_⟩
  intro n hn f M hharm hf i
  by_cases h : n ≤ 3
  · exact harmonic_difference_small i n hn h f M hf
  · exact harmonic_difference_large i n (by omega) f M hharm hf

end LatticeProb.HarmonicDifference
