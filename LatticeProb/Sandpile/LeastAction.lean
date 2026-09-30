import LatticeProb.Sandpile.Toppling

/-!
# The least action principle for legal topplings

A *legal toppling procedure* in discrete time for the configuration `s₀` is a sequence of
odometers `u : ℕ → ℤ^d → ℤ` that starts at `0`, in which at each step every site topples
at most once, and only if it holds at least `2d` chips in the configuration `s₀ + Δ u_k`
reached so far (`IsLegalToppling`).

**The least action principle** (Fey, Meester and Redig, *Stabilizability and percolation in the
infinite volume sandpile model*, Ann. Probab. 37 (2009), Theorem 2.8): a legal procedure never
topples a site more often than a nonnegative odometer `w` whose final configuration `s₀ + Δ w`
is stable (`le_of_isLegalToppling`). In particular it never exceeds the final odometer of a
stabilizing legal procedure (`le_of_isLegalToppling_of_eventually_eq`).

The proof is by induction on the step. If `u_k ≤ w` and a site `x` with `u_k(x) = w(x)`
toppled at step `k`, then `Δ u_k(x) ≤ Δ w(x)`, so
`2d ≤ s₀(x) + Δ u_k(x) ≤ s₀(x) + Δ w(x) < 2d`.
-/

namespace LatticeProb.Sandpile

open LatticeProb

variable {d : ℕ}

/-- `u` is a legal toppling procedure in discrete time for the configuration `s0`: it starts at
`0`, and at each step every site topples at most once, and only if it holds at least `2d` chips
in the configuration `s0 + Δ u` reached so far. -/
def IsLegalToppling (s0 : Site d → ℤ) (u : ℕ → Site d → ℤ) : Prop :=
  u 0 = 0 ∧ ∀ (k : ℕ) (x : Site d),
    u (k + 1) x = u k x ∨ (u (k + 1) x = u k x + 1 ∧ 2 * (d : ℤ) ≤ s0 x + lap (u k) x)

/-- A legal toppling procedure is nondecreasing in time. -/
theorem IsLegalToppling.le_succ {s0 : Site d → ℤ} {u : ℕ → Site d → ℤ}
    (hu : IsLegalToppling s0 u) (k : ℕ) (x : Site d) : u k x ≤ u (k + 1) x := by
  rcases hu.2 k x with h | ⟨h, -⟩ <;> omega

/-- A legal toppling procedure is nonnegative. -/
theorem IsLegalToppling.nonneg {s0 : Site d → ℤ} {u : ℕ → Site d → ℤ}
    (hu : IsLegalToppling s0 u) (k : ℕ) (x : Site d) : 0 ≤ u k x := by
  induction k with
  | zero => simp [hu.1]
  | succ k ih => exact ih.trans (hu.le_succ k x)

/-- The Laplacian at `x` is monotone among functions that agree at `x`: if `u ≤ w` and
`u x = w x`, then `Δ u (x) ≤ Δ w (x)`. -/
theorem lap_le_lap_of_le {u w : Site d → ℤ} (h : ∀ y, u y ≤ w y) {x : Site d}
    (hx : u x = w x) : lap u x ≤ lap w x := by
  rw [lap, lap, hx]
  linarith [nbrSumZ_mono h x]

/-- **The least action principle** (Fey–Meester–Redig, Theorem 2.8): a legal toppling procedure
for `s0` stays below every nonnegative odometer `w` for which `s0 + Δ w` is stable. -/
theorem le_of_isLegalToppling {s0 : Site d → ℤ} {u : ℕ → Site d → ℤ}
    (hu : IsLegalToppling s0 u) {w : Site d → ℤ} (hw0 : ∀ x, 0 ≤ w x)
    (hw : ∀ x, s0 x + lap w x < 2 * (d : ℤ)) (k : ℕ) (x : Site d) : u k x ≤ w x := by
  induction k generalizing x with
  | zero => rw [hu.1]; exact hw0 x
  | succ k ih =>
    rcases hu.2 k x with h | ⟨h, htop⟩
    · rw [h]; exact ih x
    · rw [h]
      by_contra hlt
      have hx : u k x = w x := le_antisymm (ih x) (by omega)
      linarith [lap_le_lap_of_le ih hx, hw x]

/-- The least action principle against a stabilizing legal procedure: a legal toppling
procedure `u` for `s0` stays below the final odometer `w` of a legal procedure `v` that is
eventually `w` at every site, when `s0 + Δ w` is stable. -/
theorem le_of_isLegalToppling_of_eventually_eq {s0 : Site d → ℤ} {u v : ℕ → Site d → ℤ}
    (hu : IsLegalToppling s0 u) (hv : IsLegalToppling s0 v) {w : Site d → ℤ}
    (hvw : ∀ x, ∃ K : ℕ, ∀ k : ℕ, K ≤ k → v k x = w x)
    (hw : ∀ x, s0 x + lap w x < 2 * (d : ℤ)) (k : ℕ) (x : Site d) : u k x ≤ w x := by
  refine le_of_isLegalToppling hu (fun y => ?_) hw k x
  obtain ⟨K, hK⟩ := hvw y
  rw [← hK K le_rfl]
  exact hv.nonneg K y

end LatticeProb.Sandpile
