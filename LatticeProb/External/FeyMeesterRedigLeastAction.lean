import LatticeProb.Sandpile.LeastAction

/-!
# The least action principle of Fey, Meester and Redig

Theorem 2.8 of A. Fey, R. Meester and F. Redig, *Stabilizability and percolation in the infinite
volume sandpile model*, Ann. Probab. 37 (2009): legal toppling procedures that are finite for a
configuration never topple a site more often than a stabilizing one. Stated for procedures in
discrete time (`LatticeProb.Sandpile.IsLegalToppling`) and configurations with nonnegative
heights: if `v` is legal and eventually equal to `w` at every site, and `s0 + Δ w` is stable,
then every legal `u` satisfies `u k ≤ w` at every step `k`.

The statement is recorded here as a proposition so that a formalization citing the principle
can carry it as an explicit hypothesis; it is proved in
`LatticeProb.External.FeyMeesterRedigLeastActionProved`.
-/

namespace LatticeProb.External

open LatticeProb.Sandpile

/-- **The least action principle** (Fey–Meester–Redig, Theorem 2.8), for legal toppling
procedures in discrete time: if `v` is a legal procedure for `s0 ≥ 0` that is eventually `w` at
every site, and `s0 + Δ w` is stable, then every legal procedure `u` for `s0` has `u k ≤ w`. -/
def FeyMeesterRedigLeastAction : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∀ s0 : Site d → ℤ, (∀ x, 0 ≤ s0 x) →
    ∀ u v : ℕ → Site d → ℤ,
      IsLegalToppling s0 u → IsLegalToppling s0 v →
      ∀ w : Site d → ℤ, (∀ x, ∃ K : ℕ, ∀ k : ℕ, K ≤ k → v k x = w x) →
        (∀ x, s0 x + lap w x < 2 * (d : ℤ)) →
        ∀ (k : ℕ) (x : Site d), u k x ≤ w x

end LatticeProb.External
