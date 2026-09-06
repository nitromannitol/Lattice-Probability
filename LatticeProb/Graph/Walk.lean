/-
The simple random walk on a general graph, the walk payoff
`S_n`, bounded stopping times, and the optimal stopping value `v_n`.

How the paper's objects are modelled here:

- Two expectations appear, and they are the same object read at two horizons.
  `walkExp G n x F` is `E_x[F(X)]` for a functional `F` of the trajectory that
  is determined by the first `n+1` positions; it is defined by the first-step
  recursion of the walk, so it is a finite average over the trajectories of
  length `n` and needs no measure.  Every statement of the paper about a
  stopping time bounded by a deterministic `n`, in particular `thm:RW`, is
  written with it.  `walkLaw G x` is the law of the whole trajectory on path
  space, needed for the statements whose functional has no finite horizon
  (`E_x[(\sup_n S_n)^q]`, and the value `v_K` of `prop:finite-vol`, whose
  stopping times are bounded only by the exit time of a finite set).  The walk
  is driven by an i.i.d. sequence of uniform instructions on `[0,1)`, one per
  step, and `stepTo` reads the instruction as the index of a neighbour.
- A stopping time for the natural filtration of `(X_k)` is a function of the
  trajectory whose value at `k` is decided by the first `k+1` positions; that
  is `IsStopping`, the convention of the companion formalizations.
- `payoff G ξ n X = S_n = ∑_{k<n} ξ(X_k)/deg(X_k)` and `S_τ` is `payoff` at
  `τ X`.  `stopValues G ξ n x` is the set of values `E_x[S_τ]` over stopping times
  bounded by `n`, over which `v_n(x)` is the supremum.
- `optimalStop` is `τ_n^* = min{0 ≤ k ≤ n : v_{n-k}(X_k) = 0}`.  The set it
  minimizes over always contains `n`, since `v_0 = 0`, so the `sInf` is the
  paper's minimum and never the junk value of an empty infimum.
- `localTime n v X = L_n(v)`, `drift` is `D_n` and `fluctuation` is `W_n` of
  `eq:dn-wn-stuff`.
-/
import LatticeProb.Graph.Basic
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory
open scoped ENNReal

namespace LatticeProb.Graph

variable {V : Type*}

/-! ### Trajectories -/

/-- `cons x X` prepends the position `x` to the trajectory `X`. -/
def cons (x : V) (X : ℕ → V) : ℕ → V
  | 0 => x
  | k + 1 => X k

/-- `walkExp G n x F = E_x[F(X)]`, for a functional `F` of the trajectory that
is determined by the first `n+1` positions.  It is the first-step average of
the walk, iterated `n` times. -/
noncomputable def walkExp (G : SimpleGraph V) [G.LocallyFinite] :
    ℕ → V → ((ℕ → V) → ℝ) → ℝ
  | 0, x, F => F (fun _ => x)
  | n + 1, x, F =>
      (∑ y ∈ G.neighborFinset x, walkExp G n y (fun X => F (cons x X))) / G.degree x

/-- `τ` is a stopping time for the natural filtration of the walk: whether it
takes the value `k` is decided by the positions up to time `k`. -/
def IsStopping (τ : (ℕ → V) → ℕ) : Prop :=
  ∀ (k : ℕ) (X Y : ℕ → V), (∀ j ≤ k, X j = Y j) → τ X = k → τ Y = k

/-- The walk payoff `S_n = ∑_{k<n} ξ(X_k)/deg(X_k)` of `thm:OS`, written in the
excess mass `ξ`.  For the sandpile, `ξ = σ - 1` and this is `∑_{k<n} ζ(X_k)`. -/
noncomputable def payoff (G : SimpleGraph V) [G.LocallyFinite] (ξ : V → ℝ) (n : ℕ)
    (X : ℕ → V) : ℝ :=
  ∑ k ∈ Finset.range n, ξ (X k) / G.degree (X k)

/-- The set of expected payoffs `E_x[S_τ]` over stopping times bounded by `n`. -/
noncomputable def stopValues (G : SimpleGraph V) [G.LocallyFinite] (ξ : V → ℝ) (n : ℕ)
    (x : V) : Set ℝ :=
  {a | ∃ τ : (ℕ → V) → ℕ, IsStopping τ ∧ (∀ X, τ X ≤ n) ∧
    a = walkExp G n x (fun X => payoff G ξ (τ X) X)}

/-- The optimal stopping value `v_n(x) = sup_{τ ≤ n} E_x[S_τ]`. -/
noncomputable def value (G : SimpleGraph V) [G.LocallyFinite] (ξ : V → ℝ) (n : ℕ) (x : V) : ℝ :=
  sSup (stopValues G ξ n x)

/-- The optimal stopping time `τ_n^* = min{0 ≤ k ≤ n : v_{n-k}(X_k) = 0}`. -/
noncomputable def optimalStop (G : SimpleGraph V) [G.LocallyFinite] (ξ : V → ℝ) (n : ℕ)
    (X : ℕ → V) : ℕ :=
  sInf {k : ℕ | k ≤ n ∧ value G ξ (n - k) (X k) = 0}

open scoped Classical in
/-- The local time `L_n(v) = #{k < n : X_k = v}`. -/
noncomputable def localTime (n : ℕ) (v : V) (X : ℕ → V) : ℕ :=
  ((Finset.range n).filter (fun k => X k = v)).card

/-- The drift `D_n = (μ-1)∑_{k<n} 1/deg(X_k)` of `eq:dn-wn-stuff`. -/
noncomputable def drift (G : SimpleGraph V) [G.LocallyFinite] (μ : ℝ) (n : ℕ) (X : ℕ → V) : ℝ :=
  (μ - 1) * ∑ k ∈ Finset.range n, invDeg G (X k)

/-- The fluctuation `W_n = ∑_v (L_n(v)/deg(v))(σ(v) - μ)` of `eq:dn-wn-stuff`. -/
noncomputable def fluctuation (G : SimpleGraph V) [G.LocallyFinite] (ξ : V → ℝ) (μ : ℝ) (n : ℕ)
    (X : ℕ → V) : ℝ :=
  ∑' v : V, (localTime n v X / G.degree v) * (ξ v - μ)

/-! ### The walk on path space -/

/-- The uniform law on `[0,1)`, the law of one instruction. -/
noncomputable def stepLaw : Measure ℝ := volume.restrict (Set.Ico (0 : ℝ) 1)

/-- The law of the instruction sequence that drives the walk. -/
noncomputable def driverLaw : Measure (ℕ → ℝ) := Measure.infinitePi fun _ : ℕ => stepLaw

/-- The neighbour of `x` selected by the instruction `u ∈ [0,1)`. -/
noncomputable def stepTo (G : SimpleGraph V) [G.LocallyFinite] (x : V) (u : ℝ) : V :=
  ((G.neighborFinset x).toList).getD ⌊(G.degree x : ℝ) * u⌋₊ x

/-- The trajectory started at `x` and driven by the instructions `ω`. -/
noncomputable def walkPath (G : SimpleGraph V) [G.LocallyFinite] (x : V) (ω : ℕ → ℝ) : ℕ → V
  | 0 => x
  | k + 1 => stepTo G (walkPath G x ω k) (ω k)

/-- The law `P_x` of the simple random walk started at `x`, on path space. -/
noncomputable def walkLaw (G : SimpleGraph V) [G.LocallyFinite] [MeasurableSpace V] (x : V) :
    Measure (ℕ → V) :=
  driverLaw.map (walkPath G x)

/-- The exit time `τ_C = inf{k ≥ 0 : X_k ∉ C}`, in `ℕ∞`, so that a trajectory
which never leaves `C` has the value `⊤` and not a junk finite value. -/
noncomputable def exitTime (C : Set V) (X : ℕ → V) : ℕ∞ :=
  sInf {k : ℕ∞ | ∃ n : ℕ, (k : ℕ∞) = n ∧ X n ∉ C}

/-- `S_{τ_C}` along one trajectory.  A trajectory that never leaves `C` is
given the value `0` through `ENat.toNat ⊤ = 0`; for a finite proper `C` in a
connected graph those trajectories form a `P_x`-null set. -/
noncomputable def payoffAtExit (G : SimpleGraph V) [G.LocallyFinite] (ξ : V → ℝ) (C : Set V)
    (X : ℕ → V) : ℝ :=
  payoff G ξ (exitTime C X).toNat X

/-- The set of expected payoffs `E_x[S_τ]` over stopping times bounded by the
exit time of `C`, over which `v_C(x)` is the supremum. -/
noncomputable def stopValuesExit (G : SimpleGraph V) [G.LocallyFinite] [MeasurableSpace V]
    (ξ : V → ℝ) (C : Set V) (x : V) : Set ℝ :=
  {a | ∃ τ : (ℕ → V) → ℕ, IsStopping τ ∧ (∀ X, (τ X : ℕ∞) ≤ exitTime C X) ∧
    a = ∫ X, payoff G ξ (τ X) X ∂(walkLaw G x)}

/-- The value `v_K(x) = sup_{τ ≤ τ_K} E_x[S_τ]` of Section 3. -/
noncomputable def valueExit (G : SimpleGraph V) [G.LocallyFinite] [MeasurableSpace V]
    (ξ : V → ℝ) (C : Set V) (x : V) : ℝ :=
  sSup (stopValuesExit G ξ C x)

/-- `sup_n S_n`, in `[0,∞]`; the supremum is at least `S_0 = 0`. -/
noncomputable def supPayoff (G : SimpleGraph V) [G.LocallyFinite] (ξ : V → ℝ) (X : ℕ → V) : ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal (payoff G ξ n X)

end LatticeProb.Graph
