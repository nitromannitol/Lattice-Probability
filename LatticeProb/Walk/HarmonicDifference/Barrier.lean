import LatticeProb.Walk.HarmonicDifference.PairChain

/-!
# Algebraic components of the pair-chain barrier

The separation of the two walkers has zero drift and a constant second moment
under the pair operator. These identities enter the quadratic barrier for the
harmonic difference estimate.
-/

namespace LatticeProb.HarmonicDifference

variable {d : ℕ}

/-- The separation of the walkers has zero drift under the pair operator. -/
theorem pairQ_separation (i : Fin d) (s : Site d × ℤ) :
    pairQ i (fun t => (t.2 : ℝ)) s = (s.2 : ℝ) := by
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast i.pos.ne'
  simp only [pairQ, Int.cast_sub, Int.cast_add, Int.cast_one]
  rw [Finset.sum_const, nsmul_eq_mul, card_erase_univ]
  field_simp
  ring

/-- The pair operator decreases the quadratic separation barrier by `1 / d`. -/
theorem pairQ_separation_quadratic (i : Fin d) (L : ℝ) (s : Site d × ℤ) :
    pairQ i (fun t => (t.2 : ℝ) * (2 * L - (t.2 : ℝ))) s =
      (s.2 : ℝ) * (2 * L - (s.2 : ℝ)) - 1 / d := by
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast i.pos.ne'
  simp only [pairQ, Int.cast_sub, Int.cast_add, Int.cast_one]
  rw [Finset.sum_const, nsmul_eq_mul, card_erase_univ]
  field_simp
  ring

/-- The pair operator preserves sums. -/
theorem pairQ_add (i : Fin d) (f g : Site d × ℤ → ℝ) (s : Site d × ℤ) :
    pairQ i (fun t => f t + g t) s = pairQ i f s + pairQ i g s := by
  simp only [pairQ]
  have hsum : ∑ j ∈ Finset.univ.erase i,
      ((f (s.1 + unit j, s.2) + g (s.1 + unit j, s.2)) +
        (f (s.1 - unit j, s.2) + g (s.1 - unit j, s.2))) =
      (∑ j ∈ Finset.univ.erase i, (f (s.1 + unit j, s.2) + f (s.1 - unit j, s.2))) +
      (∑ j ∈ Finset.univ.erase i, (g (s.1 + unit j, s.2) + g (s.1 - unit j, s.2))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hsum]
  ring

/-- The pair operator commutes with multiplication by a scalar. -/
theorem pairQ_const_mul (i : Fin d) (c : ℝ) (f : Site d × ℤ → ℝ) (s : Site d × ℤ) :
    pairQ i (fun t => c * f t) s = c * pairQ i f s := by
  simp only [pairQ]
  have hsum : ∑ j ∈ Finset.univ.erase i,
      (c * f (s.1 + unit j, s.2) + c * f (s.1 - unit j, s.2)) =
      c * ∑ j ∈ Finset.univ.erase i, (f (s.1 + unit j, s.2) + f (s.1 - unit j, s.2)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hsum]
  ring

/-- A superharmonic barrier dominating the paired difference on the one-step
boundary also dominates it on the pair set. -/
theorem pair_difference_le_barrier (i : Fin d) (n L : ℕ) (f : Site d → ℝ)
    (Φ : Site d × ℤ → ℝ)
    (hharm : ∀ z ∈ ball n, nbrSum f z - 2 * d * f z = 0)
    (hsup : ∀ s ∈ pairU i n L, pairQ i Φ s ≤ Φ s)
    (hbd : ∀ s ∈ pairU i n L, ∀ t ∈ pairSucc i s, t ∉ pairU i n L →
      |f (t.1 + t.2 • unit i) - f t.1| ≤ Φ t) :
    ∀ s ∈ pairU i n L, |f (s.1 + s.2 • unit i) - f s.1| ≤ Φ s := by
  let u : Site d × ℤ → ℝ := fun t => f (t.1 + t.2 • unit i) - f t.1
  have hsign (c : ℝ) (hc : c = 1 ∨ c = -1) :
      ∀ s ∈ pairU i n L, 0 ≤ Φ s + c * u s := by
    apply min_principle i n L
    · intro s hs
      rw [pairQ_add, pairQ_const_mul]
      have hu : pairQ i u s = u s := pairQ_u f i n L hharm hs
      rw [hu]
      linarith [hsup s hs]
    · intro s hs t ht hnot
      have hb := abs_le.mp (hbd s hs t ht hnot)
      change -Φ t ≤ u t ∧ u t ≤ Φ t at hb
      rcases hc with rfl | rfl <;> nlinarith
  intro s hs
  apply abs_le.mpr
  have hp := hsign 1 (Or.inl rfl) s hs
  have hm := hsign (-1) (Or.inr rfl) s hs
  change -Φ s ≤ u s ∧ u s ≤ Φ s
  constructor <;> linarith

end LatticeProb.HarmonicDifference
