/- Adapted from Parking-Sharpness (https://github.com/nitromannitol/Parking-Sharpness),
   source module Parking.Support.Particle at commit 66d817d; only the module paths and the namespace `Parking` are renamed
   (to `LatticeProb.ParticleDrivenAgree`). -/
import LatticeProb.ParticleDrivenAgree.Walk

/-!
# The particle-driven construction

The particle-driven construction of the process, in which every particle
carries its own walk and its own uniform variables.  This is the construction
`parking.tex` couples in `lem:one-particle` and `lem:tagged-monotonicity`,
where "every particle they share" gets "the same walk and the same uniform
variables"; the stack construction of `LatticeProb.ParticleHole` cannot express
that coupling, because adding a particle at a site changes which instruction
each later departure from that site reads.

The two constructions differ only in where a departing particle goes: here the
particle labelled `p` moves by the direction `move (p, t)` in round `t + 1`,
whereas in the stack construction it reads the next unread instruction at its
site.  Rounds, settling, holes and the odometer are defined exactly as there,
so the two processes share the state type and every derived count.

Raising the configuration by one at a single site is `addParticle`: it adds the
label `(x₀, η(x₀)⁺)` when `η(x₀) ≥ 0`, and removes one hole at `x₀` otherwise.
Either way the labels of the particles already present, and their moves and
uniform variables, are untouched, which is the coupling of `lem:one-particle`.
-/

noncomputable section

namespace LatticeProb.ParticleDrivenAgree

open LatticeProb

/-- The data driving one realization of the particle-driven construction. -/
structure PDriver (d : ℕ) where
  /-- The initial configuration, particles minus holes. -/
  eta : Site d → ℤ
  /-- The direction particle `p` takes in round `t + 1`. -/
  move : Label d × ℕ → Fin d × Bool
  /-- The uniform variable of particle `p` in round `t + 1`. -/
  rank : Label d × ℕ → ℝ

/-- The particles active at `y` after round `t`, among the candidates. -/
def pActiveAt {d : ℕ} (D : PDriver d) (S : State d) (t : ℕ) (y : Site d) :
    Finset (Label d) :=
  (candidates D.eta y t).filter fun p => S.active p ∧ S.pos p = y

/-- Where `p` stands after the step of round `t + 1`. -/
def pNextPos {d : ℕ} (D : PDriver d) (S : State d) (t : ℕ) (p : Label d) : Site d :=
  if S.active p then S.pos p + stepVec (D.move (p, t)) else S.pos p

/-- The particles arriving at `x` in round `t + 1`. -/
def pArrivalsAt {d : ℕ} (D : PDriver d) (S : State d) (t : ℕ) (x : Site d) :
    Finset (Label d) :=
  (candidates D.eta x (t + 1)).filter fun p => S.active p ∧ pNextPos D S t p = x

/-- `p` settles in round `t + 1` when fewer arrivals of smaller rank than it
reach its new site than there are holes there. -/
def pSettles {d : ℕ} (D : PDriver d) (S : State d) (t : ℕ) (p : Label d) : Bool :=
  S.active p ∧
    ((pArrivalsAt D S t (pNextPos D S t p)).filter fun q =>
        D.rank (q, t) < D.rank (p, t) ∨ (D.rank (q, t) = D.rank (p, t) ∧ labelLT q p)).card
      < S.holes (pNextPos D S t p)

/-- One round. -/
def pStep {d : ℕ} (D : PDriver d) (S : State d) (t : ℕ) : State d where
  active := fun p => S.active p ∧ !pSettles D S t p
  pos := pNextPos D S t
  holes := fun x => S.holes x - (pArrivalsAt D S t x).card
  departures := fun y => S.departures y + (pActiveAt D S t y).card

/-- The state after `t` rounds. -/
def pState {d : ℕ} (D : PDriver d) : ℕ → State d
  | 0 => initial D.eta
  | t + 1 => pStep D (pState D t) t

/-- `U_t(x)`, the departures from `x` in the first `t` rounds. -/
def pOdometer {d : ℕ} (D : PDriver d) (t : ℕ) (x : Site d) : ℕ :=
  (pState D t).departures x

/-- `A_t(x)`, the active particles at `x` after round `t`. -/
def pActiveCount {d : ℕ} (D : PDriver d) (t : ℕ) (x : Site d) : ℕ :=
  (pActiveAt D (pState D t) t x).card

/-- `H_t(x)`, the unfilled holes at `x` after round `t`. -/
def pHoleCount {d : ℕ} (D : PDriver d) (t : ℕ) (x : Site d) : ℕ :=
  (pState D t).holes x

/-- Raising the configuration by one at `x₀`. -/
def addParticle {d : ℕ} (x₀ : Site d) (η : Site d → ℤ) : Site d → ℤ :=
  fun x => if x = x₀ then η x + 1 else η x

/-- The driver with one particle added at `x₀`, every other particle keeping
its walk and its uniform variables. -/
def addParticleDriver {d : ℕ} (x₀ : Site d) (D : PDriver d) : PDriver d where
  eta := addParticle x₀ D.eta
  move := D.move
  rank := D.rank

/-- The law of the per-particle directions. -/
def moveLaw (d : ℕ) : MeasureTheory.Measure (Label d × ℕ → Fin d × Bool) :=
  MeasureTheory.Measure.infinitePi fun _ : Label d × ℕ => stepLaw d

/-- The driving data of the particle-driven construction, as a plain triple. -/
abbrev PData (d : ℕ) : Type :=
  (Site d → ℤ) × (Label d × ℕ → Fin d × Bool) × (Label d × ℕ → ℝ)

/-- The driver built from a triple. -/
def toPDriver {d : ℕ} (ω : PData d) : PDriver d := ⟨ω.1, ω.2.1, ω.2.2⟩

/-- The law of the particle-driven data. -/
def pDataLaw (d : ℕ) (ν : MeasureTheory.Measure ℤ) : MeasureTheory.Measure (PData d) :=
  (LatticeProb.iidLaw d ν).prod ((moveLaw d).prod (LatticeProb.rankLaw d))

/-- The statement of `parking.tex:645-646` that the stack construction and the
particle-driven construction have the same law, as a proposition; it is proved
as `LatticeProb.ParticleDrivenAgree.constructionsAgree'`.  It is what carries the pathwise
couplings of `lem:one-particle` and `lem:tagged-monotonicity` over to the
odometer, the activity and the hole counts of the stack process, in terms of
which `S_t` and `E U_n(0)` are defined. -/
def ConstructionsAgree : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (ν : MeasureTheory.Measure ℤ),
    MeasureTheory.IsProbabilityMeasure ν →
    (law d ν).map (fun ω =>
        (fun tx : ℕ × Site d => U ω tx.1 tx.2,
         fun tx : ℕ × Site d => A ω tx.1 tx.2,
         fun tx : ℕ × Site d => H ω tx.1 tx.2,
         fun ti : ℕ × Label d => (LatticeProb.state (toDriver ω) ti.1).active ti.2))
      = (pDataLaw d ν).map (fun ω =>
        (fun tx : ℕ × Site d => pOdometer (toPDriver ω) tx.1 tx.2,
         fun tx : ℕ × Site d => pActiveCount (toPDriver ω) tx.1 tx.2,
         fun tx : ℕ × Site d => pHoleCount (toPDriver ω) tx.1 tx.2,
         fun ti : ℕ × Label d => (pState (toPDriver ω) ti.1).active ti.2))

end LatticeProb.ParticleDrivenAgree

end
