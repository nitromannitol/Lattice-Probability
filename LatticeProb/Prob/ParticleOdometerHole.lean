/-
A positive particle odometer excludes an unfilled hole.

The paper's sentence "a site with a positive particle odometer carries no unfilled
hole" (`parking.tex:1820-1823`) is the induction that combines the one-step
identity `particleOdometer_succ` with the fact that no site carries an active
particle and an unfilled hole.
-/
import LatticeProb.ParticleHoleLemmas

noncomputable section

namespace LatticeProb

open MeasureTheory

/-- **A positive particle odometer excludes an unfilled hole.**  If the particle
odometer at `x` is positive at time `t`, then the hole count at `x` is zero. -/
theorem holeCount_eq_zero_of_particleOdometer_pos {d : ℕ}
    (D : Driver d) (t : ℕ) (x : Site d)
    (h : 0 < particleOdometer D t x) :
    holeCount D t x = 0 := by
  induction t with
  | zero =>
      simp only [particleOdometer, state, initial] at h
      exact absurd h (Nat.lt_irrefl 0)
  | succ t ih =>
      rw [holeCount_succ]
      rw [particleOdometer_succ] at h
      rcases Nat.eq_zero_or_pos (particleOdometer D t x) with h0 | hpos
      · rw [h0, Nat.zero_add] at h
        rw [holeCount_eq_zero_of_activeCount_pos t x h]
        exact Nat.zero_sub _
      · rw [ih hpos]
        exact Nat.zero_sub _

end LatticeProb
