import LatticeProb.Walk.HarmonicDifference.Barrier

/-!
# Midpoint drift for the coupled walk

The squared distance of the midpoint has constant drift under the pair operator.
-/

namespace LatticeProb.HarmonicDifference

variable {d : ℕ}

/-- The midpoint of the two walkers, in real coordinates. -/
noncomputable def midpoint (i : Fin d) (s : Site d × ℤ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun k => (s.1 k : ℝ) + if k = i then (s.2 : ℝ) / 2 else 0)

/-- The pair operator commutes with finite sums. -/
theorem pairQ_sum (i : Fin d) {α : Type*} (a : Finset α)
    (f : α → Site d × ℤ → ℝ) (s : Site d × ℤ) :
    pairQ i (fun t => ∑ k ∈ a, f k t) s = ∑ k ∈ a, pairQ i (f k) s := by
  classical
  induction a using Finset.induction_on with
  | empty => simp [pairQ]
  | @insert k a hk ih =>
    simp only [Finset.sum_insert hk, pairQ_add, ih]

/-- The drift of one squared midpoint coordinate. -/
theorem pairQ_midpoint_coord_sq (i k : Fin d) (s : Site d × ℤ) :
    pairQ i (fun t => (midpoint i t k) ^ 2) s =
      (midpoint i s k) ^ 2 + (if k = i then 1 / (4 * (d : ℝ)) else 1 / (2 * d)) := by
  classical
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast i.pos.ne'
  simp only [pairQ, midpoint, PiLp.toLp_apply, Pi.add_apply, Pi.sub_apply,
    Int.cast_add, Int.cast_sub, unit, Pi.single_apply, Int.cast_ite, Int.cast_one,
    Int.cast_zero]
  by_cases hki : k = i
  · subst k
    have hs : ∑ j ∈ Finset.univ.erase i,
        (((s.1 i : ℝ) + (if i = j then 1 else 0) + (s.2 : ℝ) / 2) ^ 2 +
         ((s.1 i : ℝ) - (if i = j then 1 else 0) + (s.2 : ℝ) / 2) ^ 2) =
        ((d : ℝ) - 1) * (2 * ((s.1 i : ℝ) + (s.2 : ℝ) / 2) ^ 2) := by
      calc
        _ = ∑ _j ∈ Finset.univ.erase i, (2 * ((s.1 i : ℝ) + (s.2 : ℝ) / 2) ^ 2) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hj' : i ≠ j := Ne.symm (Finset.mem_erase.mp hj).1
          simp only [hj', ite_false, add_zero, sub_zero]
          ring
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, card_erase_univ]
    simp only [ite_true]
    rw [hs]
    field_simp
    ring
  · simp only [hki, ite_false, add_zero]
    have hs : ∑ j ∈ Finset.univ.erase i,
        (((s.1 k : ℝ) + (if k = j then 1 else 0)) ^ 2 +
         ((s.1 k : ℝ) - (if k = j then 1 else 0)) ^ 2) =
        ((d : ℝ) - 1) * (2 * (s.1 k : ℝ) ^ 2) + 2 := by
      have hk : k ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hki, Finset.mem_univ _⟩
      rw [← Finset.add_sum_erase _ _ hk]
      simp only [ite_true]
      have hs' : ∑ j ∈ (Finset.univ.erase i).erase k,
          (((s.1 k : ℝ) + (if k = j then 1 else 0)) ^ 2 +
           ((s.1 k : ℝ) - (if k = j then 1 else 0)) ^ 2) =
           (((d : ℝ) - 1) - 1) * (2 * (s.1 k : ℝ) ^ 2) := by
        calc
          _ = ∑ _j ∈ (Finset.univ.erase i).erase k, (2 * (s.1 k : ℝ) ^ 2) := by
            apply Finset.sum_congr rfl
            intro j hj
            have hj' : k ≠ j := Ne.symm (Finset.mem_erase.mp hj).1
            simp only [hj', ite_false, add_zero, sub_zero]
            ring
          _ = _ := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem hk, Nat.cast_sub
              (Finset.card_pos.mpr ⟨k, hk⟩), card_erase_univ]
            norm_num
      rw [hs']
      ring
    rw [hs]
    field_simp
    ring

/-- The squared midpoint has constant drift under the pair operator. -/
theorem pairQ_midpoint_norm_sq (i : Fin d) (s : Site d × ℤ) :
    pairQ i (fun t => ‖midpoint i t‖ ^ 2) s =
      ‖midpoint i s‖ ^ 2 + (2 * (d : ℝ) - 1) / (4 * d) := by
  classical
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast i.pos.ne'
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  rw [pairQ_sum]
  simp_rw [pairQ_midpoint_coord_sq, Finset.sum_add_distrib]
  congr 1
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  simp only [ite_true]
  have hs : ∑ k ∈ Finset.univ.erase i,
      (if k = i then 1 / (4 * (d : ℝ)) else 1 / (2 * d)) =
      ((d : ℝ) - 1) * (1 / (2 * d)) := by
    calc
      _ = ∑ _k ∈ Finset.univ.erase i, (1 / (2 * (d : ℝ))) := by
        apply Finset.sum_congr rfl
        intro k hk
        simp only [(Finset.mem_erase.mp hk).1, ite_false]
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, card_erase_univ]
  rw [hs]
  field_simp
  ring

/-- The quadratic barrier used for the pair-chain estimate. -/
noncomputable def quadraticBarrier (i : Fin d) (L α M : ℝ) (s : Site d × ℤ) : ℝ :=
  (2 * M) * ((1 / L) * (s.2 : ℝ) + α *
    (‖midpoint i s‖ ^ 2 + ((d : ℝ) / 2) * ((s.2 : ℝ) * (2 * L - s.2))))

/-- The quadratic barrier decreases under the pair operator. -/
theorem pairQ_quadraticBarrier (i : Fin d) (L α M : ℝ) (s : Site d × ℤ) :
    pairQ i (quadraticBarrier i L α M) s =
      quadraticBarrier i L α M s - 2 * M * α / (4 * d) := by
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast i.pos.ne'
  change pairQ i (fun t => (2 * M) * ((1 / L) * (t.2 : ℝ) + α *
    (‖midpoint i t‖ ^ 2 + ((d : ℝ) / 2) * ((t.2 : ℝ) * (2 * L - t.2))))) s = _
  simp only [pairQ_const_mul, pairQ_add, pairQ_separation,
    pairQ_midpoint_norm_sq, pairQ_separation_quadratic, quadraticBarrier]
  field_simp
  ring

/-- Nonnegative parameters make the quadratic barrier superharmonic. -/
theorem pairQ_quadraticBarrier_le (i : Fin d) (L α M : ℝ) (s : Site d × ℤ)
    (hα : 0 ≤ α) (hM : 0 ≤ M) :
    pairQ i (quadraticBarrier i L α M) s ≤ quadraticBarrier i L α M s := by
  rw [pairQ_quadraticBarrier]
  have hd : (0 : ℝ) < d := by exact_mod_cast i.pos
  have h : 0 ≤ 2 * M * α / (4 * d) := by positivity
  linarith

end LatticeProb.HarmonicDifference
