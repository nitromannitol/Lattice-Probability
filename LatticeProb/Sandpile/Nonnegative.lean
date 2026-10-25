module

public import LatticeProb.Sandpile.Toppling

@[expose] public section

/-!
# Nonnegativity of the parallel toppling sandpile

For a nonnegative initial sandpile `s₀`, every parallel toppling sandpile
`s_t = s₀ + Δ v_t` of `LatticeProb.Sandpile.pconf` stays nonnegative at every site
and every time. A site loses `2d` chips only when it holds at least `2d`, and the
neighbour contribution never decreases in time because the odometer `v_t` is
nondecreasing (`podo_mono_step`).
-/

namespace LatticeProb.Sandpile

open LatticeProb

variable {d : ℕ}

/-- At time zero the parallel toppling sandpile is the initial sandpile. -/
theorem pconf_zero (s0 : Site d → ℤ) (x : Site d) : pconf s0 0 x = s0 x := by
  simp [pconf, lap, nbrSumZ]

/-- A nonnegative initial sandpile stays nonnegative at every site and every time. -/
theorem pconf_nonneg (s0 : Site d → ℤ) (hs0 : ∀ x, 0 ≤ s0 x) :
    ∀ t : ℕ, ∀ x : Site d, 0 ≤ pconf s0 t x := by
  intro t
  induction t with
  | zero =>
    intro x
    rw [pconf_zero]
    exact hs0 x
  | succ t ih =>
    intro x
    have hmono : nbrSumZ (podo s0 t) x ≤ nbrSumZ (podo s0 (t + 1)) x :=
      nbrSumZ_mono (fun y => podo_mono_step s0 t y) x
    have hpc : pconf s0 (t + 1) x = pconf s0 t x
        + (nbrSumZ (podo s0 (t + 1)) x - nbrSumZ (podo s0 t) x)
        - 2 * (d : ℤ) * (podo s0 (t + 1) x - podo s0 t x) := by
      simp only [pconf, lap]
      ring
    have hdiff : podo s0 (t + 1) x - podo s0 t x
        = if 2 * (d : ℤ) ≤ pconf s0 t x then 1 else 0 := by
      rw [podo_succ]
      ring
    rw [hpc, hdiff]
    have hx := ih x
    split_ifs with hc
    · linarith
    · linarith

end LatticeProb.Sandpile
