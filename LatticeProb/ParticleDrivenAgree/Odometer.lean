/- Adapted from Parking-Sharpness (https://github.com/nitromannitol/Parking-Sharpness),
   source module Parking.Support.Odometer at commit 66d817d. The module paths and the namespace `Parking`
   are renamed (to `LatticeProb.ParticleDrivenAgree`), and proofs are adapted to the Lean and Mathlib
   versions of this repository where needed. -/
import LatticeProb.ParticleDrivenAgree.Particle

/-!
# One round of the particle process: conservation and neighbour bounds

The two conservation facts of one round that `lem:parallel` rests on, and the
bridge from the neighbour hypothesis of that lemma to the step bound of
`LatticeProb.ParticleHoleLemmas`.

- `activeCount_zero`: at time zero the active particles at `x` are exactly the
  `η(x)⁺` particles that start there.
- `activeCount_succ`: the particles active at `x` after round `t + 1` are the
  arrivals of that round that did not settle.
- `stepsToNeighbour_of_mem`: an instruction that points at a neighbour of the
  site carrying it moves a particle by at most one in each coordinate, which is
  what makes the counts over `candidates` lossless.

The third ingredient of `lem:parallel`, that the instruction indices read at a
site in one round are exactly `[U_t(y), U_{t+1}(y))`, is
`LatticeProb.ParticleDrivenAgree.card_filter_nextPos` in `LatticeProb/ParticleDrivenAgree/Parallel.lean`.
-/

noncomputable section

namespace LatticeProb.ParticleDrivenAgree

open LatticeProb Finset

variable {d : ℕ}

/-! ### The neighbour hypothesis -/

/-- A site is a lattice neighbour of `y` iff it differs from `y` by a unit vector in
some coordinate. -/
theorem mem_nbrFinset_iff {y z : Site d} :
    z ∈ nbrFinset y ↔ ∃ i : Fin d, z = y + unit i ∨ z = y - unit i := by
  simp [nbrFinset]

/-- Neighbouring sites differ by at most one in every coordinate. -/
theorem abs_sub_le_one_of_mem_nbrFinset {y z : Site d} (h : z ∈ nbrFinset y) (i : Fin d) :
    |z i - y i| ≤ 1 := by
  obtain ⟨j, hj | hj⟩ := mem_nbrFinset_iff.mp h
  · subst hj
    by_cases hij : i = j
    · subst hij; simp [unit, Pi.single_eq_same]
    · simp [unit, Pi.single_eq_of_ne hij]
  · subst hj
    by_cases hij : i = j
    · subst hij; simp [unit, Pi.single_eq_same]
    · simp [unit, Pi.single_eq_of_ne hij]

/-- The neighbour relation is symmetric. -/
theorem nbrFinset_symm {y z : Site d} (h : z ∈ nbrFinset y) : y ∈ nbrFinset z := by
  obtain ⟨i, hi | hi⟩ := mem_nbrFinset_iff.mp h
  · exact mem_nbrFinset_iff.mpr ⟨i, Or.inr (by subst hi; abel)⟩
  · exact mem_nbrFinset_iff.mpr ⟨i, Or.inl (by subst hi; abel)⟩

/-- The hypothesis of `lem:parallel` gives the step bound of the library. -/
theorem stepsToNeighbour_of_mem {D : Driver d}
    (h : ∀ q : Site d × ℕ, D.stack q ∈ nbrFinset q.1) : StepsToNeighbour D :=
  fun q i => abs_sub_le_one_of_mem_nbrFinset (h q) i

/-! ### The active count at time zero -/

/-- The radius-zero box around `x` is the singleton `{x}`. -/
theorem boxFinset_zero (x : Site d) : boxFinset x 0 = {x} := by
  ext z
  simp [boxFinset]

/-- At time zero the candidate labels at `x` are exactly `(x, i)` for `i` below `η(x)⁺`,
matching the initial particle count there. -/
theorem candidates_zero (η : Site d → ℤ) (x : Site d) :
    candidates η x 0 = (Finset.range (η x).toNat).map ⟨fun i => (x, i), by
      intro a b h; simpa using h⟩ := by
  simp [candidates, boxFinset_zero]

/-- At time zero the active particle count at `x` equals `η(x)⁺`, the number of
particles initially placed there. -/
theorem activeCount_zero (D : Driver d) (x : Site d) :
    activeCount D 0 x = (D.eta x).toNat := by
  classical
  unfold activeCount activeAt
  rw [show state D 0 = initial D.eta from rfl, candidates_zero]
  rw [Finset.filter_map, Finset.card_map,
    Finset.filter_true_of_mem (fun i hi =>
      ⟨decide_eq_true (Finset.mem_range.mp hi), rfl⟩),
    Finset.card_range]

/-! ### The active count after a round -/

/-- A particle is active after round `t + 1` iff it was active at `t` and did not
settle in that round. -/
theorem active_succ_iff (D : Driver d) (t : ℕ) (p : Label d) :
    (state D (t + 1)).active p = true
      ↔ ((state D t).active p = true ∧ settles D (state D t) t p = false) := by
  simp [state, step]

/-- The particles that settle at `x` in round `t` are among that round's arrivals at `x`. -/
theorem settledAt_subset (D : Driver d) (t : ℕ) (x : Site d) :
    settledAt D t x ⊆ arrivalsAt D (state D t) t x := Finset.filter_subset _ _

/-- Under `StepsToNeighbour`, the particles active at `x` after round `t + 1` are exactly
the round's arrivals at `x` that did not settle there. -/
theorem activeAt_succ_eq {D : Driver d} (h : StepsToNeighbour D) (t : ℕ) (x : Site d) :
    activeAt D (state D (t + 1)) (t + 1) x
      = arrivalsAt D (state D t) t x \ settledAt D t x := by
  classical
  ext p
  rw [mem_activeAt_iff h, Finset.mem_sdiff, mem_arrivalsAt_iff h, settledAt,
    Finset.mem_filter, active_succ_iff]
  constructor
  · rintro ⟨⟨hact, hset⟩, hpos⟩
    refine ⟨⟨hact, ?_⟩, ?_⟩
    · rw [show (state D (t + 1)).pos p = nextPos D (state D t) t p from rfl] at hpos
      exact hpos
    · rintro ⟨-, hs⟩
      rw [hs] at hset
      exact Bool.noConfusion hset
  · rintro ⟨⟨hact, hpos⟩, hno⟩
    refine ⟨⟨hact, ?_⟩, ?_⟩
    · by_contra hs
      exact hno ⟨Finset.mem_filter.mpr ⟨arrivalsAt_subset_candidates _ _ _ _
        (by rw [mem_arrivalsAt_iff h]; exact ⟨hact, hpos⟩), hact, hpos⟩,
        by simpa using Bool.not_eq_false _ |>.mp hs⟩
    · rw [show (state D (t + 1)).pos p = nextPos D (state D t) t p from rfl]
      exact hpos

/-- The particles active at `x` after round `t + 1` are the arrivals of that
round that did not settle. -/
theorem activeCount_succ {D : Driver d} (h : StepsToNeighbour D) (t : ℕ) (x : Site d) :
    activeCount D (t + 1) x
      = (arrivalsAt D (state D t) t x).card - (settledAt D t x).card := by
  unfold activeCount
  rw [activeAt_succ_eq h, Finset.card_sdiff_of_subset (settledAt_subset D t x)]

end LatticeProb.ParticleDrivenAgree

end
