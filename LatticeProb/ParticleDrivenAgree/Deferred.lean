/- Adapted from Parking-Sharpness (https://github.com/nitromannitol/Parking-Sharpness),
   source module Parking.Support.Deferred at commit 66d817d; only the module paths and the namespace `Parking` are renamed
   (to `LatticeProb.ParticleDrivenAgree`). -/
import LatticeProb.ParticleDrivenAgree.Parallel

/-!
# Lemma 3.2, first clause

Lemma 3.2 of `parking.tex`, first clause: the event that the odometer at `y`
has reached `j + 1` does not depend on the instruction of index `j` at `y`.

The whole content is `state_congr`: the state after `t` rounds reads only the
instructions the odometer has reached, so two drivers agreeing on those, on the
configuration and on the uniform variables have the same state.  The bound
`instructionIndex_lt` is what makes that true: a particle active at `y` reads
an index between the departures from `y` before and after the round, because
its own label is one of the labels at `y` that the round counts.  That in turn
needs the instructions to move a particle to a neighbour, without which a
particle can stand at a site it is not a candidate for and read an index the
round does not count.

The clause follows: if the odometer at `y` never reaches `j + 1`, then no
instruction of index `j` at `y` is ever read, the two states agree, and the
odometers agree.
-/

noncomputable section

namespace LatticeProb.ParticleDrivenAgree

open LatticeProb Finset

variable {d : ℕ}

/-- `activeAt` depends on the driver only through its configuration `D.eta`. -/
theorem activeAt_congr {D D' : Driver d} (heta : D.eta = D'.eta) (S : State d) (t : ℕ)
    (z : Site d) : activeAt D S t z = activeAt D' S t z := by
  unfold activeAt; rw [heta]

/-- `instructionIndex` depends on the driver only through its configuration
`D.eta`, via `activeAt_congr`. -/
theorem instructionIndex_congr {D D' : Driver d} (heta : D.eta = D'.eta) (S : State d)
    (t : ℕ) (p : Label d) :
    instructionIndex D S t p = instructionIndex D' S t p := by
  unfold instructionIndex; rw [activeAt_congr heta]

/-- An active label reads an instruction index below the odometer at its site
after the round, because its own label is one of the labels the round counts
there. -/
theorem instructionIndex_lt {D : Driver d} (hs : StepsToNeighbour D) (t : ℕ) (p : Label d)
    (hact : (state D t).active p = true) :
    instructionIndex D (state D t) t p
      < particleOdometer D (t + 1) ((state D t).pos p) := by
  have hmem : p ∈ activeAt D (state D t) t ((state D t).pos p) :=
    (mem_activeAt_iff hs t _ p).mpr ⟨hact, rfl⟩
  have hlt := countLT_lt_card (r := labelLT (d := d)) labelLT_irrefl hmem
  rw [instructionIndex_of_mem hmem, particleOdometer_succ]
  exact Nat.add_lt_add_left hlt _

/-- The state after `t` rounds reads only the instructions the odometer has
reached, so two drivers that agree on those, on the configuration and on the
uniform variables have the same state. -/
theorem state_congr {D D' : Driver d} (hs : StepsToNeighbour D)
    (heta : D.eta = D'.eta) (hrank : D.rank = D'.rank) :
    ∀ t : ℕ, (∀ z i, i < particleOdometer D t z → D.stack (z, i) = D'.stack (z, i)) →
      state D t = state D' t := by
  intro t
  induction t with
  | zero => intro _; show initial D.eta = initial D'.eta; rw [heta]
  | succ t ih =>
      intro hst
      have hst' : ∀ z i, i < particleOdometer D t z → D.stack (z, i) = D'.stack (z, i) :=
        fun z i hi => hst z i (lt_of_lt_of_le hi (particleOdometer_le_succ D t z))
      have hS : state D t = state D' t := ih hst'
      have hnext : ∀ p, nextPos D (state D t) t p = nextPos D' (state D t) t p := by
        intro p
        unfold nextPos
        by_cases hact : (state D t).active p = true
        · rw [if_pos hact, if_pos hact, instructionIndex_congr heta]
          exact hst _ _ (by
            rw [← instructionIndex_congr heta]
            exact instructionIndex_lt hs t p hact)
        · rw [if_neg hact, if_neg hact]
      have harr : ∀ x, arrivalsAt D (state D t) t x = arrivalsAt D' (state D t) t x := by
        intro x
        unfold arrivalsAt
        rw [heta]
        exact Finset.filter_congr fun p _ => by rw [hnext p]
      have hsettle : ∀ p, settles D (state D t) t p = settles D' (state D t) t p := by
        intro p
        unfold settles
        rw [hnext p, harr, hrank]
      show step D (state D t) t = step D' (state D' t) t
      rw [← hS]
      unfold step
      congr 1
      · funext p; rw [hsettle p]
      · funext p; exact hnext p
      · funext x; rw [harr x]
      · funext z; rw [activeAt_congr heta]

/-- If two drivers agree on the configuration, the priorities, and every
instruction except possibly the one at `(y, j)`, and the odometer at `y` under
`D` never reaches `j + 1`, then it agrees with the odometer under `D'`, by
`state_congr`. -/
theorem odometer_transfer {D D' : Driver d} (hs : StepsToNeighbour D)
    (heta : D.eta = D'.eta) (hrank : D.rank = D'.rank) (y : Site d) (j n : ℕ)
    (hne : ∀ q : Site d × ℕ, q ≠ (y, j) → D.stack q = D'.stack q)
    (h : particleOdometer D n y ≤ j) :
    particleOdometer D' n y = particleOdometer D n y := by
  have hstate : state D n = state D' n := by
    refine state_congr hs heta hrank n fun z i hi => hne (z, i) ?_
    rintro heq
    rw [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    omega
  show (state D' n).departures y = (state D n).departures y
  rw [hstate]

/-- Lemma 3.2 of the paper, first clause: whether the odometer at `y` has
reached `j + 1` does not depend on the instruction of index `j` at `y`. -/
theorem odometer_ge_congr {D D' : Driver d} (hs : StepsToNeighbour D)
    (hs' : StepsToNeighbour D') (heta : D.eta = D'.eta) (hrank : D.rank = D'.rank)
    (y : Site d) (j n : ℕ)
    (hne : ∀ q : Site d × ℕ, q ≠ (y, j) → D.stack q = D'.stack q) :
    (j + 1 ≤ particleOdometer D n y ↔ j + 1 ≤ particleOdometer D' n y) := by
  constructor
  · intro h
    by_contra hc
    have hle : particleOdometer D' n y ≤ j := by omega
    have := odometer_transfer hs' heta.symm hrank.symm y j n
      (fun q hq => (hne q hq).symm) hle
    omega
  · intro h
    by_contra hc
    have hle : particleOdometer D n y ≤ j := by omega
    have := odometer_transfer hs heta hrank y j n hne hle
    omega

end LatticeProb.ParticleDrivenAgree

end
