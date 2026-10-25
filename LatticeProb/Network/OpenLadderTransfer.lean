import LatticeProb.Network.OpenLadderKirchhoff

/-!
# Deterministic transfer across the open ladder

The derived top and interior Kirchhoff equations propagate rung differences downward.
The bottom equations then express the terminal gap through any real coefficient sequence
with initial values one and recurrence `a (k + 2) = 4 * a (k + 1) - a k`.
-/

namespace LatticeProb.Network.OpenLadder

/-- Backward elimination from the actual top rung determines every actual rung difference. -/
theorem rung_difference_transfer (a : ℕ → ℝ) (ha0 : a 0 = 1) (ha1 : a 1 = 1)
    (ha : ∀ k, a (k + 2) = 4 * a (k + 1) - a k)
    {n : ℕ} {u : Vertex (n : ℤ) → ℝ} (hu : Harmonic u)
    (k : ℕ) (hk : k < n) :
    rungDifference u ((n : ℤ) - (k : ℤ)) ⟨by omega, by omega⟩ =
      a (k + 1) * rungDifference u n ⟨by omega, by omega⟩ := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | k
    · simp only [Nat.cast_zero, sub_zero, ha1, one_mul]
    rcases k with _ | k
    · have ht := difference_top hu (by omega)
      have ha2 : a 2 = 3 := by rw [ha 0, ha0, ha1]; norm_num
      simpa only [Nat.zero_add, Nat.cast_one, ha2] using ht
    · have hp := ih (k + 1) (by omega) (by omega)
      have hq := ih k (by omega) (by omega)
      have hm := difference_middle (j := (n : ℤ) - ((k + 1 : ℕ) : ℤ)) hu
        (by omega) (by omega)
      have hlo : (n : ℤ) - ((k + 1 : ℕ) : ℤ) - 1 =
          (n : ℤ) - ((k + 2 : ℕ) : ℤ) := by omega
      have hhi : (n : ℤ) - ((k + 1 : ℕ) : ℤ) + 1 = (n : ℤ) - (k : ℤ) := by omega
      simp only [hlo, hhi] at hm
      rw [hp, hq] at hm
      rw [hm, ha (k + 1)]
      ring

/-- The actual harmonic ladder transfers its top difference to its terminal gap.
The coefficient hypotheses are literal scalar data, independent of the graph. -/
theorem terminal_gap_transfer (a : ℕ → ℝ) (ha0 : a 0 = 1) (ha1 : a 1 = 1)
    (ha : ∀ k, a (k + 2) = 4 * a (k + 1) - a k)
    {n : ℕ} (hn : 1 ≤ n) {u : Vertex (n : ℤ) → ℝ} (hu : Harmonic u) :
    u (target n) - u (source n) =
      a (n + 1) * rungDifference u n ⟨by omega, by omega⟩ := by
  by_cases hn1 : n = 1
  · subst n
    have ha2 : a 2 = 3 := by rw [ha 0, ha0, ha1]; norm_num
    change u (target 1) - u (source 1) =
      a 2 * rungDifference u 1 ⟨by omega, by omega⟩
    rw [ha2]
    exact terminal_gap_one hu
  have hb := difference_bottom hu (by omega)
  have h1 := rung_difference_transfer a ha0 ha1 ha hu (n - 1) (by omega)
  have h2 := rung_difference_transfer a ha0 ha1 ha hu (n - 2) (by omega)
  have hi1 : (n : ℤ) - ((n - 1 : ℕ) : ℤ) = 1 := by omega
  have hi2 : (n : ℤ) - ((n - 2 : ℕ) : ℤ) = 2 := by omega
  have hn1' : n - 1 + 1 = n := by omega
  have hn2' : n - 2 + 1 = n - 1 := by omega
  simp only [hi1, hn1'] at h1
  simp only [hi2, hn2'] at h2
  rw [hb, h1, h2]
  have hac := ha (n - 1)
  have hn2 : n - 1 + 2 = n + 1 := by omega
  rw [hn1', hn2] at hac
  rw [hac]
  ring

/-- Specializing the arbitrary-height transfer theorem at height two recovers eleven. -/
theorem terminal_gap_transfer_two (a : ℕ → ℝ) (ha0 : a 0 = 1) (ha1 : a 1 = 1)
    (ha : ∀ k, a (k + 2) = 4 * a (k + 1) - a k)
    {u : Vertex 2 → ℝ} (hu : Harmonic u) :
    u (target 2) - u (source 2) =
      11 * rungDifference u 2 ⟨by omega, by omega⟩ := by
  have h := terminal_gap_transfer a ha0 ha1 ha (n := 2) (by omega) hu
  have ha2 : a 2 = 3 := by rw [ha 0, ha0, ha1]; norm_num
  have ha3 : a 3 = 11 := by rw [ha 1, ha1, ha2]; norm_num
  simpa only [Nat.cast_ofNat, ha3] using h

/-- The existing explicit height-two voltage supplies a nonzero consumer of generic transfer. -/
theorem voltageTwo_transfer (a : ℕ → ℝ) (ha0 : a 0 = 1) (ha1 : a 1 = 1)
    (ha : ∀ k, a (k + 2) = 4 * a (k + 1) - a k) :
    voltageTwo (target 2) - voltageTwo (source 2) = a 3 ∧ a 3 = 11 := by
  have ht := terminal_gap_transfer a ha0 ha1 ha (n := 2) (by omega) voltageTwo_harmonic
  norm_num only [Nat.cast_ofNat] at ht
  rw [voltageTwo_gap.2, mul_one] at ht
  exact ⟨ht, ht.symm.trans voltageTwo_gap.1⟩

end LatticeProb.Network.OpenLadder
