/-
The particle-driven construction of the particle-hole process, and the
statement that it has the same law as the stack construction.

In `LatticeProb.ParticleHole` the randomness sits at the SITES: the `j`-th
departure from `y` follows `stack (y, j)`, so adding a particle at a site
shifts which instruction every later departure from that site reads and no
pathwise coupling in the configuration survives.  The construction here puts
the randomness on the PARTICLES: the particle labelled `p` moves by the
displacement `move (p, t)` in round `t + 1`, whatever else is happening.  The
tagged-particle couplings of the papers are pathwise in this construction and
in no other.

Rounds, settling, holes and the odometer are defined exactly as in the stack
construction, so the two processes share `LatticeProb.State` and every count
derived from it.  What has to be proved is that the two have the same LAW,
which is `ConstructionsAgree`.  The engine for it is
`LatticeProb.map_revealed_dag`: the pairs `(p, t)` at which a particle departs
read pairwise distinct entries of `stack` (`LatticeProb.readIndex_injective`),
each read looks only at the finitely many reads that precede it in the
dependency order once the configuration is fixed, and every instruction law
pushes forward to the SAME displacement law (`instructionLaw_map_sub`).
-/
import LatticeProb.ReadIndex
import LatticeProb.Invariance
import LatticeProb.Prob.DagExploration
import LatticeProb.Prob.PiSum

noncomputable section

namespace LatticeProb

open MeasureTheory

variable {d : ℕ}

/-! ### The construction -/

/-- The data driving one realization of the particle-driven construction: the
configuration, the displacement each particle takes in each round, and the
uniform variables. -/
structure PDriver (d : ℕ) where
  /-- The initial configuration, particles minus holes. -/
  eta : Site d → ℤ
  /-- The displacement particle `p` takes in round `t + 1`. -/
  move : Label d × ℕ → Site d
  /-- The uniform variable of particle `p` in round `t + 1`. -/
  rank : Label d × ℕ → ℝ

/-- The particles active at `y` after round `t`, among the candidates. -/
def pActiveAt (D : PDriver d) (S : State d) (t : ℕ) (y : Site d) : Finset (Label d) :=
  (candidates D.eta y t).filter fun p => S.active p ∧ S.pos p = y

/-- Where `p` stands after the step of round `t + 1`. -/
def pNextPos (D : PDriver d) (S : State d) (t : ℕ) (p : Label d) : Site d :=
  if S.active p then S.pos p + D.move (p, t) else S.pos p

/-- The particles arriving at `x` in round `t + 1`. -/
def pArrivalsAt (D : PDriver d) (S : State d) (t : ℕ) (x : Site d) : Finset (Label d) :=
  (candidates D.eta x (t + 1)).filter fun p => S.active p ∧ pNextPos D S t p = x

/-- `p` settles in round `t + 1` when fewer arrivals of smaller rank than it
reach its new site than there are holes there. -/
def pSettles (D : PDriver d) (S : State d) (t : ℕ) (p : Label d) : Bool :=
  S.active p ∧
    ((pArrivalsAt D S t (pNextPos D S t p)).filter fun q =>
        D.rank (q, t) < D.rank (p, t) ∨ (D.rank (q, t) = D.rank (p, t) ∧ labelLT q p)).card
      < S.holes (pNextPos D S t p)

/-- One round. -/
def pStep (D : PDriver d) (S : State d) (t : ℕ) : State d where
  active := fun p => S.active p ∧ !pSettles D S t p
  pos := pNextPos D S t
  holes := fun x => S.holes x - (pArrivalsAt D S t x).card
  departures := fun y => S.departures y + (pActiveAt D S t y).card

/-- The state after `t` rounds. -/
def pState (D : PDriver d) : ℕ → State d
  | 0 => initial D.eta
  | t + 1 => pStep D (pState D t) t

/-- `U_t(x)`, the departures from `x` in the first `t` rounds. -/
def pOdometer (D : PDriver d) (t : ℕ) (x : Site d) : ℕ :=
  (pState D t).departures x

/-- `A_t(x)`, the active particles at `x` after round `t`. -/
def pActiveCount (D : PDriver d) (t : ℕ) (x : Site d) : ℕ :=
  (pActiveAt D (pState D t) t x).card

/-- `H_t(x)`, the unfilled holes at `x` after round `t`. -/
def pHoleCount (D : PDriver d) (t : ℕ) (x : Site d) : ℕ :=
  (pState D t).holes x

/-- Raising the configuration by one at `x₀`: a particle is added when the site
carries particles, and a hole is removed when it carries holes. -/
def addParticle (x₀ : Site d) (η : Site d → ℤ) : Site d → ℤ :=
  fun x => if x = x₀ then η x + 1 else η x

/-- The driver with one particle added at `x₀`, every other particle keeping its
displacements and its uniform variables. -/
def addParticleDriver (x₀ : Site d) (D : PDriver d) : PDriver d where
  eta := addParticle x₀ D.eta
  move := D.move
  rank := D.rank

/-! ### The two laws -/

/-- The law of one displacement: the instruction law at the origin, which is
what every instruction law pushes forward to. -/
abbrev displacementLaw (d : ℕ) : Measure (Site d) := instructionLaw (0 : Site d)

/-- Every instruction law is the displacement law recentred. -/
theorem instructionLaw_map_sub_self (y : Site d) :
    (instructionLaw y).map (fun z : Site d => z - y) = displacementLaw d := by
  have := instructionLaw_map_sub (d := d) y 0
  rwa [zero_add] at this

/-- The law of the per-particle displacements. -/
def moveLaw (d : ℕ) : Measure (Label d × ℕ → Site d) :=
  Measure.infinitePi fun _ : Label d × ℕ => displacementLaw d

/-- The driving data of the stack construction, as a plain triple. -/
abbrev StackData (d : ℕ) : Type :=
  (Site d → ℤ) × (Site d × ℕ → Site d) × (Label d × ℕ → ℝ)

/-- The driver of the stack construction built from a triple. -/
def toStackDriver (ω : StackData d) : Driver d := ⟨ω.1, ω.2.1, ω.2.2⟩

/-- The law of the stack data: i.i.d. configuration, independent stacks,
independent uniforms. -/
def stackDataLaw (d : ℕ) (ν : Measure ℤ) : Measure (StackData d) :=
  (iidLaw d ν).prod ((stackLaw d).prod (rankLaw d))

/-- The driving data of the particle-driven construction, as a plain triple. -/
abbrev PData (d : ℕ) : Type :=
  (Site d → ℤ) × (Label d × ℕ → Site d) × (Label d × ℕ → ℝ)

/-- The driver of the particle-driven construction built from a triple. -/
def toPDriver (ω : PData d) : PDriver d := ⟨ω.1, ω.2.1, ω.2.2⟩

/-- The law of the particle-driven data. -/
def pDataLaw (d : ℕ) (ν : Measure ℤ) : Measure (PData d) :=
  (iidLaw d ν).prod ((moveLaw d).prod (rankLaw d))

/-- The observables both constructions carry: the odometer, the active count,
the hole count, and which particles are still active. -/
def stackObservables (ω : StackData d) :
    (ℕ × Site d → ℕ) × (ℕ × Site d → ℕ) × (ℕ × Site d → ℕ) × (ℕ × Label d → Bool) :=
  (fun tx => particleOdometer (toStackDriver ω) tx.1 tx.2,
   fun tx => activeCount (toStackDriver ω) tx.1 tx.2,
   fun tx => holeCount (toStackDriver ω) tx.1 tx.2,
   fun ti => (state (toStackDriver ω) ti.1).active ti.2)

/-- The same observables of the particle-driven construction. -/
def pObservables (ω : PData d) :
    (ℕ × Site d → ℕ) × (ℕ × Site d → ℕ) × (ℕ × Site d → ℕ) × (ℕ × Label d → Bool) :=
  (fun tx => pOdometer (toPDriver ω) tx.1 tx.2,
   fun tx => pActiveCount (toPDriver ω) tx.1 tx.2,
   fun tx => pHoleCount (toPDriver ω) tx.1 tx.2,
   fun ti => (pState (toPDriver ω) ti.1).active ti.2)

/-- **The two constructions have the same law.**  `parking.tex:630` asserts it
without proof, and the divisible-sandpile papers use the same passage between
the two constructions.  It is what carries the pathwise couplings of the
particle-driven construction over to the odometer, the activity and the hole
counts of the stack process, in terms of which the papers' quantities are
defined. -/
def ConstructionsAgree : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ ν : Measure ℤ, IsProbabilityMeasure ν →
    (stackDataLaw d ν).map stackObservables = (pDataLaw d ν).map pObservables

/-! ### Transporting a differently coded displacement family

A repository whose particle-driven construction codes the displacement as a
signed coordinate, or in any other way, uses the law above through this: any
family of displacements whose one-step law pushes forward to
`displacementLaw d` gives `pDataLaw d ν` after the pushforward. -/

/-- Recoding the displacements through a map that carries the one-step law to
the displacement law carries the whole law of the particle data. -/
theorem map_pDataLaw_of_map {M : Type*} [MeasurableSpace M] (θ : Measure M)
    [IsProbabilityMeasure θ] (f : M → Site d) (hf : Measurable f)
    (hθ : θ.map f = displacementLaw d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hd : 1 ≤ d) :
    ((iidLaw d ν).prod
        ((Measure.infinitePi fun _ : Label d × ℕ => θ).prod (rankLaw d))).map
        (fun ω => (ω.1, (fun q => f (ω.2.1 q), ω.2.2)))
      = pDataLaw d ν := by
  have hprob : IsProbabilityMeasure (displacementLaw d) := instructionLaw_isProbability hd 0
  haveI := hprob
  haveI : IsProbabilityMeasure (rankLaw d) := rankLaw_isProbability d
  haveI : IsProbabilityMeasure (iidLaw d ν) := by
    unfold iidLaw; infer_instance
  have hmove : (Measure.infinitePi fun _ : Label d × ℕ => θ).map
      (fun ω q => f (ω q)) = moveLaw d := by
    rw [Measure.infinitePi_map_pi _ fun _ : Label d × ℕ => hf]
    simp only [moveLaw, hθ]
  have hmeasf : Measurable fun ω : Label d × ℕ → M => fun q => f (ω q) :=
    measurable_pi_lambda _ fun q => hf.comp (measurable_pi_apply q)
  have hpair : ((Measure.infinitePi fun _ : Label d × ℕ => θ).prod (rankLaw d)).map
      (Prod.map (fun ω q => f (ω q)) id) = (moveLaw d).prod (rankLaw d) := by
    rw [← Measure.map_prod_map _ _ hmeasf measurable_id, hmove, Measure.map_id]
  have hfull : ((iidLaw d ν).prod
        ((Measure.infinitePi fun _ : Label d × ℕ => θ).prod (rankLaw d))).map
        (Prod.map id (Prod.map (fun ω q => f (ω q)) id))
      = (iidLaw d ν).prod ((moveLaw d).prod (rankLaw d)) := by
    rw [← Measure.map_prod_map _ _ measurable_id (hmeasf.prodMap measurable_id),
      Measure.map_id, hpair]
  rw [pDataLaw, ← hfull]
  rfl

end LatticeProb

end
