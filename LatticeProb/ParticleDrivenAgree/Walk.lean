/- Adapted from Parking-Sharpness (https://github.com/nitromannitol/Parking-Sharpness),
   source module Parking.Support.Walk at commit 66d817d; only the module paths and the namespace `Parking` are renamed
   (to `LatticeProb.ParticleDrivenAgree`). -/
import LatticeProb.ParticleDrivenAgree.Basic

/-!
# The simple random walk and its stopping problem

The simple random walk that Sections 3 to 5 of `parking.tex` run beside the
particle system, its bounded optimal stopping problem, and the truncated
Green function.

How the paper's objects are modelled here:

- A trajectory is driven by a sequence of signed directions in
  `Fin d × Bool`; `walkPath x p j` is `X_j` under `P_x`.  The law of the
  directions is the uniform product measure `walkLaw d`, so that `E_x f` is
  `∫ p, f (walkPath x p) ∂(walkLaw d)`.  For `d = 0` the one-step law is the
  zero measure, which is why every statement below fixes `1 ≤ d`.
- A stopping time bounded by `n` for the natural filtration of the walk is a
  function of the direction sequence which is bounded by `n` and depends only
  on the directions read before it stops; that is the content of
  `IsStoppingTimeLE`.
- `stopReward η x σ p` is `∑_{j<σ} η(X_j)` along one trajectory, so the
  quantity the paper's supremum ranges over is `stopValue η x σ`.
- `heat d j x` is `P^j(0, x)` and `green d m x` is
  `g_m(x) = ∑_{j<m} P^j(0,x)`; `gamma d m y` is the paper's `Γ_m(y)`.
- `kappa d n` is `κ_d(n)`.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace LatticeProb.ParticleDrivenAgree

/-- The displacement of one signed direction. -/
def stepVec {d : ℕ} (b : Fin d × Bool) : Site d :=
  if b.2 then LatticeProb.unit b.1 else -LatticeProb.unit b.1

/-- The position of the walk from `x` after `j` steps of the direction
sequence `p`. -/
def walkPath {d : ℕ} (x : Site d) (p : ℕ → Fin d × Bool) : ℕ → Site d
  | 0 => x
  | j + 1 => walkPath x p j + stepVec (p j)

/-- The uniform law of one signed direction. -/
def stepLaw (d : ℕ) : Measure (Fin d × Bool) :=
  ((2 * (d : ℝ≥0∞))⁻¹) • Finset.univ.sum fun b : Fin d × Bool => Measure.dirac b

/-- The law of the direction sequence of a simple random walk. -/
def walkLaw (d : ℕ) : Measure (ℕ → Fin d × Bool) :=
  Measure.infinitePi fun _ : ℕ => stepLaw d

/-- The transition probability `P(y, x) = 1{y ∼ x}/(2d)`. -/
def kern (d : ℕ) (y x : Site d) : ℝ :=
  if x ∈ LatticeProb.nbrFinset y then (2 * (d : ℝ))⁻¹ else 0

/-- `σ` is a stopping time for the natural filtration of the walk, bounded by
`n`: it never exceeds `n`, and it is decided by the directions it has read. -/
def IsStoppingTimeLE {d : ℕ} (n : ℕ) (σ : (ℕ → Fin d × Bool) → ℕ) : Prop :=
  (∀ p, σ p ≤ n) ∧ ∀ p q : ℕ → Fin d × Bool, (∀ j < σ p, p j = q j) → σ q = σ p

/-- The reward `∑_{j<σ} η(X_j)` collected along one trajectory. -/
def stopReward {d : ℕ} (η : Site d → ℝ) (x : Site d)
    (σ : (ℕ → Fin d × Bool) → ℕ) (p : ℕ → Fin d × Bool) : ℝ :=
  ∑ j ∈ Finset.range (σ p), η (walkPath x p j)

/-- `E_x ∑_{j<σ} η(X_j)`, the expected reward of the stopping rule `σ`. -/
def stopValue {d : ℕ} (η : Site d → ℝ) (x : Site d)
    (σ : (ℕ → Fin d × Bool) → ℕ) : ℝ :=
  ∫ p, stopReward η x σ p ∂(walkLaw d)

/-- The set of expected rewards of the stopping rules bounded by `n`, over
which `eq:stopping` takes its supremum. -/
def stopValues (d : ℕ) (η : Site d → ℝ) (n : ℕ) (x : Site d) : Set ℝ :=
  {v | ∃ σ, IsStoppingTimeLE n σ ∧ v = stopValue η x σ}

/-- `P^j(0, x)`, the `j`-step transition probability of the walk. -/
def heat (d : ℕ) : ℕ → Site d → ℝ
  | 0 => fun x => if x = 0 then 1 else 0
  | j + 1 => fun x => LatticeProb.walkOp (heat d j) x

/-- The truncated Green function `g_m(x) = ∑_{j<m} P^j(0, x)`. -/
def green (d : ℕ) (m : ℕ) (x : Site d) : ℝ :=
  ∑ j ∈ Finset.range m, heat d j x

/-- `Γ_m(y) = ∑_z P(y,z)(g_m(z) - (P g_m)(y))^2`, the variance of `g_m` at a
uniform neighbour of `y`. -/
def gamma (d : ℕ) (m : ℕ) (y : Site d) : ℝ :=
  ∑ z ∈ LatticeProb.nbrFinset y,
    kern d y z * (green d m z - LatticeProb.walkOp (green d m) y) ^ 2

/-- `κ_d(n)`, the Green-function factor of Section 4. -/
def kappa (d : ℕ) (n : ℕ) : ℝ :=
  if d = 1 then (n : ℝ) ^ ((1 : ℝ) / 2)
  else if d = 2 then Real.log (n + 2)
  else 1

/-- The increment bound `max_{m<n} max_y max_{z ∼ y} |g_m(z) - (P g_m)(y)|`
of `lem:w-martingale`. -/
def greenIncrement (d : ℕ) (n : ℕ) : ℝ :=
  ⨆ m ∈ Set.Iio n, ⨆ y : Site d, ⨆ z ∈ LatticeProb.nbrFinset y,
    |green d m z - LatticeProb.walkOp (green d m) y|

end LatticeProb.ParticleDrivenAgree

end
