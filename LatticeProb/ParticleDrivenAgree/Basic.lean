/- Adapted from Parking-Sharpness (https://github.com/nitromannitol/Parking-Sharpness),
   source module Parking.Basic at commit 66d817d; only the module paths and the namespace `Parking` are renamed
   (to `LatticeProb.ParticleDrivenAgree`). -/
import LatticeProb.Site
import LatticeProb.IID
import LatticeProb.ParticleHole
import LatticeProb.Rank
import LatticeProb.ParticleHoleLemmas
import LatticeProb.Walk.SRW
import LatticeProb.Walk.Shells

/-!
# The parking model

The parking model of `parking.tex` and its divisible-sandpile analogue, modelled here as
follows (`parking.tex`, Sections 1 and 3).

- The particle-hole process, its labelled particles, the instruction stacks and the uniform
  variables are `LatticeProb.ParticleHole`. A realization is driven by the triple
  `(η, stack, rank)`; the law of the triple is the product of the i.i.d. law of `η`, the stack
  law of the walk, and independent uniforms.
- `U_n(x)` is the number of departures from `x` in the first `n` rounds, `A_t(x)` the active
  particles at `x` after round `t`, and `S_t` the expected number of particles started at the
  origin still active after round `t`.
- The divisible sandpile odometer is `u_{n+1} = (η + P u_n)⁺` with `u_0 = 0`, for the simple
  random walk operator `P`; the oriented version uses the transpose kernel
  `P⃗(x, x - e_i) = 1/d`, as Remark 3.1 of the paper requires.
- `U_∞(x)` is the supremum of `U_n(x)` in `ℕ∞`, so that a site which never stops receiving
  particles has the value `⊤` and not a junk one.
-/

open MeasureTheory
open scoped ENNReal

namespace LatticeProb.ParticleDrivenAgree

export LatticeProb (Site unit walkOp Driver Label graphNorm)

/-- The driving data as a plain triple, so that its law is a product measure. -/
abbrev Data (d : ℕ) : Type :=
  (Site d → ℤ) × (Site d × ℕ → Site d) × (Label d × ℕ → ℝ)

/-- The driver built from a triple. -/
def toDriver {d : ℕ} (ω : Data d) : Driver d := ⟨ω.1, ω.2.1, ω.2.2⟩

/-- The law of the data for the simple random walk: i.i.d. `η` with one-site
law `ν`, independent instruction stacks, independent uniforms. -/
noncomputable def law (d : ℕ) (ν : Measure ℤ) : Measure (Data d) :=
  (LatticeProb.iidLaw d ν).prod ((LatticeProb.stackLaw d).prod (LatticeProb.rankLaw d))

/-- The law of the data for the oriented walk. -/
noncomputable def orientedLaw (d : ℕ) (ν : Measure ℤ) : Measure (Data d) :=
  (LatticeProb.iidLaw d ν).prod ((LatticeProb.orientedStackLaw d).prod (LatticeProb.rankLaw d))

/-- The particle odometer `U_n(x)` of a realization. -/
noncomputable def U {d : ℕ} (ω : Data d) (n : ℕ) (x : Site d) : ℕ :=
  LatticeProb.particleOdometer (toDriver ω) n x

/-- `A_t(x)`, the active particles at `x` after round `t`. -/
noncomputable def A {d : ℕ} (ω : Data d) (t : ℕ) (x : Site d) : ℕ :=
  LatticeProb.activeCount (toDriver ω) t x

/-- `H_t(x)`, the unfilled holes at `x` after round `t`. -/
noncomputable def H {d : ℕ} (ω : Data d) (t : ℕ) (x : Site d) : ℕ :=
  LatticeProb.holeCount (toDriver ω) t x

/-- The limiting odometer `U_∞(x)`, in `ℕ∞`. -/
noncomputable def Ulimit {d : ℕ} (ω : Data d) (x : Site d) : ℕ∞ :=
  ⨆ n : ℕ, (U ω n x : ℕ∞)

/-- `E U_n(0)` under a law `P` on the data. -/
noncomputable def meanU {d : ℕ} (P : Measure (Data d)) (n : ℕ) : ℝ :=
  ∫ ω, (U ω n 0 : ℝ) ∂P

/-- `E U_∞(0)`, in `ℝ≥0∞`. -/
noncomputable def meanUlimit {d : ℕ} (P : Measure (Data d)) : ℝ≥0∞ :=
  ∫⁻ ω, (Ulimit ω 0 : ℝ≥0∞) ∂P

/-- `S_t`: the expected number of particles started at the origin and still
active after round `t`. -/
noncomputable def S {d : ℕ} (P : Measure (Data d)) (t : ℕ) : ℝ :=
  ∫ ω, (LatticeProb.survivorsFrom (toDriver ω) t 0 : ℝ) ∂P

/-- The divisible sandpile odometer `u_{n+1} = (η + P u_n)⁺`, `u_0 = 0`. -/
noncomputable def u {d : ℕ} (η : Site d → ℝ) : ℕ → Site d → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun x => max 0 (η x + walkOp (u η n) x)

/-- The oriented operator `(P⃗ f)(x) = (1/d) ∑_i f(x - e_i)`. -/
noncomputable def orientedOp {d : ℕ} (f : Site d → ℝ) (x : Site d) : ℝ :=
  (∑ i : Fin d, f (x - unit i)) / d

/-- The oriented divisible sandpile odometer `u⃗_{n+1} = (η + P⃗ u⃗_n)⁺`. -/
noncomputable def uOriented {d : ℕ} (η : Site d → ℝ) : ℕ → Site d → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun x => max 0 (η x + orientedOp (uOriented η n) x)

/-- The sandpile odometer of a realization, from its integer configuration. -/
noncomputable def uOf {d : ℕ} (ω : Data d) (n : ℕ) (x : Site d) : ℝ :=
  u (fun y => (ω.1 y : ℝ)) n x

/-- `E u_n(0)` under a law `P` on the data. -/
noncomputable def meanu {d : ℕ} (P : Measure (Data d)) (n : ℕ) : ℝ :=
  ∫ ω, uOf ω n 0 ∂P

/-- `E u⃗_n(0)` under a law `P` on the data. -/
noncomputable def meanuOriented {d : ℕ} (P : Measure (Data d)) (n : ℕ) : ℝ :=
  ∫ ω, uOriented (fun y => (ω.1 y : ℝ)) n 0 ∂P

/-- The standing hypotheses on the one-site law at the critical density:
integer valued, nonconstant, mean zero, with an exponential moment. -/
structure CriticalLaw (ν : Measure ℤ) : Prop where
  prob : IsProbabilityMeasure ν
  nonconst : ∀ k : ℤ, ν {k} ≠ 1
  mean : ∫ k, (k : ℝ) ∂ν = 0
  expMoment : ∃ θ : ℝ, 0 < θ ∧ Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν

end LatticeProb.ParticleDrivenAgree

namespace LatticeProb.ParticleDrivenAgree

/-- The graph distance from the origin to the nearest unfilled hole after round
`t`, in `ℕ∞`, so that "no hole anywhere" is `⊤` and not a junk value. -/
noncomputable def holeDistance {d : ℕ} (ω : Data d) (t : ℕ) : ℕ∞ :=
  ⨅ x ∈ {x : Site d | 0 < H ω t x}, (graphNorm x : ℕ∞)

/-- The graph distance from the origin to the nearest active particle after
round `t`. -/
noncomputable def activeDistance {d : ℕ} (ω : Data d) (t : ℕ) : ℕ∞ :=
  ⨅ x ∈ {x : Site d | 0 < A ω t x}, (graphNorm x : ℕ∞)

/-- The event that the origin is closer to an unfilled hole than to an active
particle after round `t`. -/
def HoleCloser {d : ℕ} (ω : Data d) (t : ℕ) : Prop :=
  holeDistance ω t < activeDistance ω t

end LatticeProb.ParticleDrivenAgree
