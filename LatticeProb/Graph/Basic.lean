/-
The divisible sandpile on a general graph, and the walk objects,
Sections 1 and 3.

How the paper's objects are modelled here:

- The graph is a `SimpleGraph V` together with `SimpleGraph.LocallyFinite`, so
  that `G.degree v` and `G.neighborFinset v` are available.  Infiniteness,
  connectedness, and a degree bound are hypotheses of the statements that use
  them, exactly as in the paper.
- `walkOp G f x = deg(x)⁻¹ ∑_{y ∼ x} f(y)` is the one-step averaging operator
  `P`, and `laplacian G f x = ∑_{y ∼ x} (f(y) - f(x))` is `Δ`.
- The parallel toppling procedure `eq:u-update`, `eq:sigma-update` is `topple`,
  whose `n`-fold iterate is `config G σ n = σ_n`; the odometer `u_n` is the
  partial sum of the emissions `(σ_k - 1)⁺/deg`, which is the paper's recursion
  in closed form.  `odometerLimit` is `u_∞` valued in `ℝ≥0∞`, so that an
  exploding vertex has the value `⊤` and not a junk real number, and
  `Stabilizes` is `u_∞ < ∞` at every vertex.
- `heat G k x y` is `P_x(X_k = y)`, defined by the averaging recursion.  From
  it come `meanLocalTime G n x v = E_x[L_n(v)]`, the finite-time Green function
  `greenTime = g_n` of `eq:gn-def`, the Green function `green = g` of
  `eq:green-def` valued in `ℝ≥0∞`, the inverse-degree clock `clock = A_n`, and
  the fluctuation scale `fluct = Σ_n`, again in `ℝ≥0∞`.
- `killedHeat`/`killedGreen` are the same objects for the walk killed on
  leaving a set, so `killedGreen G C y v` is `g_C(y,v)` of `eq:gC-PDE`.
- `closedBall G x r` is `B(x,r) = {v : dist(v,x) ≤ r}`, written with `edist` so
  that vertices in another component are not accidentally included.

Degrees enter as denominators.  A vertex of degree zero would give the junk
value `a / 0 = 0`; on an infinite connected graph there is no such vertex, and
the statements below all carry connectedness or a positive degree bound.
-/
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped ENNReal

namespace LatticeProb.Graph

variable {V : Type*}

/-! ### The graph operators -/

/-- The one-step averaging operator `(P f)(x) = deg(x)⁻¹ ∑_{y ∼ x} f(y)`. -/
noncomputable def walkOp (G : SimpleGraph V) [G.LocallyFinite] (f : V → ℝ) (x : V) : ℝ :=
  (∑ y ∈ G.neighborFinset x, f y) / G.degree x

/-- The discrete Laplacian `Δf(x) = ∑_{y ∼ x} (f(y) - f(x))`. -/
noncomputable def laplacian (G : SimpleGraph V) [G.LocallyFinite] (f : V → ℝ) (x : V) : ℝ :=
  ∑ y ∈ G.neighborFinset x, (f y - f x)

/-- The closed ball `B(x,r) = {v : dist(v,x) ≤ r}`. -/
def closedBall (G : SimpleGraph V) (x : V) (r : ℕ) : Set V := {v | G.edist v x ≤ r}

/-! ### The divisible sandpile -/

/-- The excess mass `ξ(v) = σ(v) - 1`. -/
def excess (σ : V → ℝ) (v : V) : ℝ := σ v - 1

/-- The per-neighbour excess `ζ(v) = (σ(v) - 1)/deg(v)`. -/
noncomputable def scenery (G : SimpleGraph V) [G.LocallyFinite] (σ : V → ℝ) (v : V) : ℝ :=
  (σ v - 1) / G.degree v

/-- The mass emitted by `v` in one round of parallel toppling,
`(σ(v) - 1)⁺ / deg(v)`. -/
noncomputable def emission (G : SimpleGraph V) [G.LocallyFinite] (σ : V → ℝ) (v : V) : ℝ :=
  max (σ v - 1) 0 / G.degree v

/-- One round of parallel toppling, `eq:sigma-update`. -/
noncomputable def topple (G : SimpleGraph V) [G.LocallyFinite] (σ : V → ℝ) (v : V) : ℝ :=
  min (σ v) 1 + ∑ w ∈ G.neighborFinset v, emission G σ w

/-- The configuration `σ_n` after `n` rounds of parallel toppling. -/
noncomputable def config (G : SimpleGraph V) [G.LocallyFinite] (σ : V → ℝ) (n : ℕ) : V → ℝ :=
  (topple G)^[n] σ

/-- The odometer `u_n(v) = ∑_{k<n} (σ_k(v) - 1)⁺/deg(v)` of `eq:u-update`. -/
noncomputable def odometer (G : SimpleGraph V) [G.LocallyFinite] (σ : V → ℝ) (n : ℕ) (v : V) : ℝ :=
  ∑ k ∈ Finset.range n, emission G (config G σ k) v

/-- The limiting odometer `u_∞(v) ∈ [0,∞]`. -/
noncomputable def odometerLimit (G : SimpleGraph V) [G.LocallyFinite] (σ : V → ℝ) (v : V) : ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal (odometer G σ n v)

/-- The configuration `σ` stabilizes: `u_∞(v) < ∞` for every vertex. -/
def Stabilizes (G : SimpleGraph V) [G.LocallyFinite] (σ : V → ℝ) : Prop :=
  ∀ v : V, odometerLimit G σ v ≠ ⊤

/-! ### The heat kernel and the Green functions -/

open scoped Classical in
/-- The `k`-step transition probability `p_k(x,y) = P_x(X_k = y)`. -/
noncomputable def heat (G : SimpleGraph V) [G.LocallyFinite] : ℕ → V → V → ℝ
  | 0 => fun x y => if x = y then 1 else 0
  | k + 1 => fun x y => walkOp G (fun z => heat G k z y) x

/-- The expected local time `E_x[L_n(v)] = ∑_{k<n} p_k(x,v)`. -/
noncomputable def meanLocalTime (G : SimpleGraph V) [G.LocallyFinite] (n : ℕ) (x v : V) : ℝ :=
  ∑ k ∈ Finset.range n, heat G k x v

/-- The finite-time Green function `g_n(x,v) = E_x[L_n(v)]/deg(v)` of `eq:gn-def`. -/
noncomputable def greenTime (G : SimpleGraph V) [G.LocallyFinite] (n : ℕ) (x v : V) : ℝ :=
  meanLocalTime G n x v / G.degree v

/-- The Green function `g(x,v)` of `eq:green-def`, valued in `[0,∞]`. -/
noncomputable def green (G : SimpleGraph V) [G.LocallyFinite] (x v : V) : ℝ≥0∞ :=
  (∑' k : ℕ, ENNReal.ofReal (heat G k x v)) / (G.degree v : ℝ≥0∞)

/-- The inverse degree `1/deg(v)`. -/
noncomputable def invDeg (G : SimpleGraph V) [G.LocallyFinite] (v : V) : ℝ := 1 / G.degree v

/-- The inverse-degree clock `A_n(x) = E_x[∑_{k<n} 1/deg(X_k)]` of `eq:gn-def`. -/
noncomputable def clock (G : SimpleGraph V) [G.LocallyFinite] (n : ℕ) (x : V) : ℝ :=
  ∑ k ∈ Finset.range n, (walkOp G)^[k] (invDeg G) x

/-- The fluctuation scale `Σ_n(x) = ∑_v g_n(x,v)^2` of `eq:gn-def`, in `[0,∞]`. -/
noncomputable def fluct (G : SimpleGraph V) [G.LocallyFinite] (n : ℕ) (x : V) : ℝ≥0∞ :=
  ∑' v : V, ENNReal.ofReal (greenTime G n x v ^ 2)

open scoped Classical in
/-- The `k`-step transition probability of the walk killed on leaving `C`. -/
noncomputable def killedHeat (G : SimpleGraph V) [G.LocallyFinite] (C : Set V) :
    ℕ → V → V → ℝ
  | 0 => fun x y => if x ∈ C then (if x = y then 1 else 0) else 0
  | k + 1 => fun x y => if x ∈ C then walkOp G (fun z => killedHeat G C k z y) x else 0

/-- The killed Green function `g_C(y,v) = E_y[L_{τ_C}(v)]/deg(v)` of `eq:gC-PDE`,
valued in `[0,∞]`. -/
noncomputable def killedGreen (G : SimpleGraph V) [G.LocallyFinite] (C : Set V) (y v : V) : ℝ≥0∞ :=
  (∑' k : ℕ, ENNReal.ofReal (killedHeat G C k y v)) / (G.degree v : ℝ≥0∞)

/-- The killed Green function as a real number.  On a finite proper `C` in a
connected graph the walk leaves `C` in finite expected time, so this is the
value of `g_C(y,v)`; the `toReal` never meets the value `⊤` there. -/
noncomputable def killedGreenReal (G : SimpleGraph V) [G.LocallyFinite] (C : Set V) (y v : V) : ℝ :=
  (killedGreen G C y v).toReal

end LatticeProb.Graph
