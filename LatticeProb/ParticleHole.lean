/-
The particle–hole process on `ℤ^d`, as `parking.tex` describes it in Section 3:
a configuration `η` places `η(x)⁺` particles or `η(x)⁻` holes at each site;
a round has three stages.  Every active particle takes one step, each arrival
receives an independent uniform variable, and at each site the arrivals fill
the unfilled holes there in increasing order of these variables until either
the arrivals or the holes run out.  A particle which fills a hole never moves
again.

How the paper's objects are modelled here:

- A particle is labelled by its starting site and an index, `(x, i)` with
  `i < η(x)⁺`.  The label is what makes "the particles which start at the
  origin" and the tagged-particle couplings expressible.
- The randomness sits at the sites, as in the paper's stack construction: the
  `j`-th departure from `y` follows the instruction `stack (y, j)`.  When
  several particles leave `y` in the same round they read consecutive
  instructions in the order of their labels.  The paper does not fix this
  order; it does not affect the odometer, and it fixes which particle carries
  which instruction so that every quantity below is a function of the data.
- The uniform variable of a particle in round `t + 1` is `rank (p, t)`.  Ties
  are broken by the label; they have probability zero.
- The state after round `t` is the set of active particles with their
  positions, the number of unfilled holes at each site, and the number of
  departures from each site so far, which is the particle odometer `U_t`.
- The particles that can be at `y` after round `t` started within sup-distance
  `t` of `y`, so every count below is over an explicit finite set.
-/
import LatticeProb.IID

noncomputable section

namespace LatticeProb

/-- A particle label: its starting site and its index there. -/
abbrev Label (d : ℕ) : Type := Site d × ℕ

/-- The data driving one realization of the process. -/
structure Driver (d : ℕ) where
  /-- The initial configuration, particles minus holes. -/
  eta : Site d → ℤ
  /-- The instruction stacks: the `j`-th departure from `y` goes to `stack (y, j)`. -/
  stack : Site d × ℕ → Site d
  /-- The uniform variable of particle `p` in round `t + 1`. -/
  rank : Label d × ℕ → ℝ

/-- The state after a round. -/
structure State (d : ℕ) where
  active : Label d → Bool
  pos : Label d → Site d
  holes : Site d → ℕ
  departures : Site d → ℕ

/-- The sup-norm box of radius `r` about `y`, as a finset. -/
def boxFinset {d : ℕ} (y : Site d) (r : ℕ) : Finset (Site d) :=
  Fintype.piFinset fun i => (Finset.Icc (y i - r) (y i + r))

/-- The labels of every particle that started within sup-distance `r` of `y`. -/
def candidates {d : ℕ} (η : Site d → ℤ) (y : Site d) (r : ℕ) : Finset (Label d) :=
  (boxFinset y r).biUnion fun x => (Finset.range (η x).toNat).map ⟨fun i => (x, i), by
    intro a b h; simpa using h⟩

/-- The initial state: `η(x)⁺` active particles at `x`, `η(x)⁻` holes there. -/
def initial {d : ℕ} (η : Site d → ℤ) : State d where
  active := fun p => decide (p.2 < (η p.1).toNat)
  pos := fun p => p.1
  holes := fun x => (-η x).toNat
  departures := fun _ => 0

/-- Labels are ordered lexicographically; this fixes the reading order of the
instructions and breaks ties among ranks. -/
def labelLT {d : ℕ} (p q : Label d) : Prop :=
  toLex (p.1, p.2) < toLex (q.1, q.2)

instance {d : ℕ} : DecidableRel (labelLT (d := d)) := Classical.decRel _

/-- The particles active at `y` after round `t`, among the candidates. -/
def activeAt {d : ℕ} (D : Driver d) (S : State d) (t : ℕ) (y : Site d) : Finset (Label d) :=
  (candidates D.eta y t).filter fun p => S.active p ∧ S.pos p = y

/-- The instruction index read by `p` when it leaves `y` in round `t + 1`: the
departures so far plus the number of co-departing particles with smaller labels. -/
def instructionIndex {d : ℕ} (D : Driver d) (S : State d) (t : ℕ) (p : Label d) : ℕ :=
  S.departures (S.pos p) + ((activeAt D S t (S.pos p)).filter fun q => labelLT q p).card

/-- Where `p` stands after the step of round `t + 1`. -/
def nextPos {d : ℕ} (D : Driver d) (S : State d) (t : ℕ) (p : Label d) : Site d :=
  if S.active p then D.stack (S.pos p, instructionIndex D S t p) else S.pos p

/-- The particles arriving at `x` in round `t + 1`. -/
def arrivalsAt {d : ℕ} (D : Driver d) (S : State d) (t : ℕ) (x : Site d) : Finset (Label d) :=
  (candidates D.eta x (t + 1)).filter fun p => S.active p ∧ nextPos D S t p = x

/-- `p` settles in round `t + 1` when fewer arrivals of smaller rank than it
reach its new site than there are holes there. -/
def settles {d : ℕ} (D : Driver d) (S : State d) (t : ℕ) (p : Label d) : Bool :=
  S.active p ∧
    ((arrivalsAt D S t (nextPos D S t p)).filter fun q =>
        D.rank (q, t) < D.rank (p, t) ∨ (D.rank (q, t) = D.rank (p, t) ∧ labelLT q p)).card
      < S.holes (nextPos D S t p)

/-- One round. -/
def step {d : ℕ} (D : Driver d) (S : State d) (t : ℕ) : State d where
  active := fun p => S.active p ∧ !settles D S t p
  pos := nextPos D S t
  holes := fun x => S.holes x - (arrivalsAt D S t x).card
  departures := fun y => S.departures y + (activeAt D S t y).card

/-- The state after `t` rounds. -/
def state {d : ℕ} (D : Driver d) : ℕ → State d
  | 0 => initial D.eta
  | t + 1 => step D (state D t) t

/-- The particle odometer `U_t(x)`: the departures from `x` in the first `t` rounds. -/
def particleOdometer {d : ℕ} (D : Driver d) (t : ℕ) (x : Site d) : ℕ :=
  (state D t).departures x

/-- `A_t(x)`: the number of active particles at `x` after round `t`. -/
def activeCount {d : ℕ} (D : Driver d) (t : ℕ) (x : Site d) : ℕ :=
  (activeAt D (state D t) t x).card

/-- `H_t(x)`: the unfilled holes at `x` after round `t`. -/
def holeCount {d : ℕ} (D : Driver d) (t : ℕ) (x : Site d) : ℕ :=
  (state D t).holes x

/-- The particles which started at `y` and are still active after round `t`. -/
def survivorsFrom {d : ℕ} (D : Driver d) (t : ℕ) (y : Site d) : ℕ :=
  ((Finset.range (D.eta y).toNat).filter fun i => (state D t).active (y, i)).card

/-- The law of the uniform variables: independent uniforms on `[0, 1]`. -/
noncomputable def rankLaw (d : ℕ) : MeasureTheory.Measure (Label d × ℕ → ℝ) :=
  MeasureTheory.Measure.infinitePi fun _ : Label d × ℕ =>
    MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)

/-- The law of the instruction stacks for the oriented walk: each step goes to
`y + e_i` with probability `1/d`. -/
noncomputable def orientedInstructionLaw {d : ℕ} (y : Site d) : MeasureTheory.Measure (Site d) :=
  ((d : ENNReal)⁻¹) • Finset.univ.sum fun i : Fin d => MeasureTheory.Measure.dirac (y + unit i)

noncomputable def orientedStackLaw (d : ℕ) : MeasureTheory.Measure (Site d × ℕ → Site d) :=
  MeasureTheory.Measure.infinitePi fun p : Site d × ℕ => orientedInstructionLaw p.1

end LatticeProb

end
