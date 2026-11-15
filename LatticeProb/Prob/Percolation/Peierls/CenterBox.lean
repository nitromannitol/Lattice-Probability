/-
# Centered lattice boxes

Finite centered boxes and their cardinalities, together with the size threshold
used in the Peierls bound. Adapted from Ahmed Bou-Rabee's Exploding-Sandpiles,
`Exploding/Support/ExtMHProof8.lean` and `Exploding/Support/Vocab.lean`, commit
`dfcc6d2091673aacabe6aa1602c39aa0c37c8392` (Apache-2.0).
-/
import LatticeProb.Site

namespace LatticeProb.Percolation

variable {d : ℕ}

/-- The sup-norm box `[-n, n]^d`. -/
def xmh4_cent (d n : ℕ) : Set (Site d) := {x | ∀ i, |x i| ≤ (n : ℤ)}

/-- The box `[-n, n]^d` as a finset. -/
noncomputable def xmh4_centFinset (d n : ℕ) : Finset (Site d) :=
  Fintype.piFinset fun _ : Fin d => Finset.Icc (-(n : ℤ)) (n : ℤ)

theorem xmh4_mem_centFinset {n : ℕ} {x : Site d} :
    x ∈ xmh4_centFinset d n ↔ x ∈ xmh4_cent d n := by
  simp only [xmh4_centFinset, Fintype.mem_piFinset, Finset.mem_Icc, xmh4_cent,
    Set.mem_ofPred_eq]
  constructor
  · intro h i
    rw [abs_le]
    exact h i
  · intro h i
    have := h i
    rw [abs_le] at this
    exact this

theorem xmh4_centFinset_card (d n : ℕ) :
    (xmh4_centFinset d n).card = (2 * n + 1) ^ d := by
  rw [xmh4_centFinset, Fintype.card_piFinset]
  simp only [Int.card_Icc]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  omega

/-- The size threshold of the bad event at scale `n`. -/
def xmh4_m (n : ℕ) : ℕ := max 1 (Nat.log 2 n)

end LatticeProb.Percolation
