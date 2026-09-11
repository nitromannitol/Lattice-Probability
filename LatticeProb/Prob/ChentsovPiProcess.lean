/-
Finite dyadic bad events for processes indexed by Euclidean boxes.
-/
import LatticeProb.Prob.ChentsovPi

noncomputable section
open MeasureTheory LatticeProb

variable {k : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

/-- The level-`n` grid indices inside the box `[-m, m]^k`. -/
def LatticeProb.boxIdx (m n : ℕ) : Finset (Fin k → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(m * 2 ^ n : ℕ) : ℤ) (m * 2 ^ n)

/-- The bad set at level `n`: some adjacent pair of level-`n` grid points of
the box has an increment of size at least `r n`. -/
def LatticeProb.badSetPi (X : (Fin k → ℝ) → Ω → ℝ) (r : ℕ → ℝ) (m n : ℕ) : Set Ω :=
  ⋃ i : Fin k, ⋃ j ∈ boxIdx m n,
    {ω | r n ≤ |X (gridPt n (j + Pi.single i 1)) ω - X (gridPt n j) ω|}

theorem LatticeProb.measurableSet_badSetPi {X : (Fin k → ℝ) → Ω → ℝ} {r : ℕ → ℝ} (_hr : ∀ n, 0 ≤ r n)
    (m n : ℕ)
    (hmeas : ∀ j : Fin k → ℤ, Measurable (fun ω => X (gridPt n j) ω)) :
    MeasurableSet (badSetPi X r m n) := by
  refine MeasurableSet.iUnion fun i => ?_
  refine Finset.measurableSet_biUnion _ fun j _ => ?_
  exact measurableSet_le measurable_const ((hmeas _).sub (hmeas _)).abs



theorem LatticeProb.mem_boxIdx_iff {k : ℕ} (m n : ℕ) (j : Fin k → ℤ) :
    j ∈ LatticeProb.boxIdx m n ↔ ∀ i, |j i| ≤ (m * 2 ^ n : ℕ) := by
  simp only [LatticeProb.boxIdx, Fintype.mem_piFinset, Finset.mem_Icc, abs_le, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]



theorem LatticeProb.card_boxIdx {k : ℕ} (m n : ℕ) :
    (LatticeProb.boxIdx (k := k) m n).card = (2 * (m * 2 ^ n) + 1) ^ k := by
  rw [LatticeProb.boxIdx, Fintype.card_piFinset_const]
  congr 1
  rw [Int.card_Icc]
  have heq : ((m : ℤ) * 2 ^ n + 1 - -(↑(m * 2 ^ n) : ℤ)) =
      ((2 * (m * 2 ^ n) + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [heq, Int.toNat_natCast]

end
