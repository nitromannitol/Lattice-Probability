/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Probability.Williams.Defs at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
Definitions for nodes W0–W7 of `blueprint/EXT_PP_BLUEPRINT.md` (§A.0), which prove
`WilliamsDriftDecomposition` (L14, `Proofs/LQG/WedgeTranslation.lean`). The statement is due to
D. Williams, *Path decomposition and continuity of local time for one-dimensional diffusions I*,
Proc. LMS 28 (1974), and L. C. G. Rogers, J. W. Pitman, *Markov functions*, Ann. Probab. 9 (1981);
see also Revuz–Yor, *Continuous Martingales and Brownian Motion*, VII.4 and XI.

All paths are indexed by `ℝ≥0`. Hitting and passage times use `sInf`/`sSup` in `ℝ≥0`, with the
junk value `0` when the set is empty (or unbounded, for `sSup`); every use is on the almost sure
event where they are genuine.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace QuantumZipper.Williams

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A version of Brownian motion that is measurable at each time, and continuous and started at
`0` for every `ω` (not just almost every). -/
structure GoodBM (b : ℝ≥0 → Ω → ℝ) (P : Measure Ω) : Prop where
  pre : IsPreBrownianReal b P
  meas : ∀ t, Measurable (b t)
  cont : ∀ ω, Continuous (b · ω)
  zero : ∀ ω, b 0 ω = 0

/-- Brownian motion with diffusion coefficient `σ` and drift `μ`: `t ↦ σ b_t + μ t`. -/
def dpath (σ μ : ℝ) (b : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ≥0 → ℝ := fun t => σ * b t ω + μ * t

/-- First hitting time of the level `a`. -/
def hitLevel (w : ℝ≥0 → ℝ) (a : ℝ) : ℝ≥0 := sInf {t | w t = a}

/-- Last passage time at the level `a`. -/
def lastPass (w : ℝ≥0 → ℝ) (a : ℝ) : ℝ≥0 := sSup {t | w t = a}

/-- The path after its last passage at `a`, re-centred at `0`; `Ŷ = postLast Y 0`. -/
def postLast (w : ℝ≥0 → ℝ) (a : ℝ) : ℝ≥0 → ℝ := fun u => w (lastPass w a + u) - a

/-- The reversal of `x` from its hitting time of `-c`, shifted up by `c`, as (lifetime, path).
Truncated subtraction stops the path at the value `c` after the lifetime. -/
def revHit (x : ℝ≥0 → ℝ) (c : ℝ) : ℝ≥0 × (ℝ≥0 → ℝ) :=
  (hitLevel x (-c), fun u => x (hitLevel x (-c) - u) + c)

/-- Concatenation of two (lifetime, path) pieces; the second is shifted up by `c`. -/
def concatPre (c : ℝ) (p q : ℝ≥0 × (ℝ≥0 → ℝ)) : ℝ≥0 × (ℝ≥0 → ℝ) :=
  (p.1 + q.1, fun u => if u ≤ p.1 then p.2 u else c + q.2 (u - p.1))

/-- Expected occupation measure of `t ↦ σ b_t + μ t`: `A ↦ ∫_0^∞ P(σ b_m + μ m ∈ A) dm`
(Lebesgue measure on `(0, ∞) ⊆ ℝ`, since `ℝ≥0` carries no `volume`). -/
def occ (σ μ : ℝ) : Measure ℝ :=
  ((volume : Measure ℝ).restrict (Set.Ioi 0)).bind fun m =>
    gaussianReal (μ * m) (⟨σ ^ 2, sq_nonneg σ⟩ * m.toNNReal)

end QuantumZipper.Williams
