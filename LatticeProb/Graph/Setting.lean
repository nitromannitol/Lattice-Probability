/-
The vocabulary shared by the statements: the walk-averaged
payoff, the two suprema of the optimal stopping problem, the joint law of the
scenery and the walk, double transience, a degree bound, and the connected
component of a vertex in a set.

`meanPayoff G ξ n x` is `E_x[S_n | ξ]`, the payoff at the deterministic time
`n`, which is a function of the scenery alone.  `supMeanPayoff` is `sup_n` of
it and `supStopValue` is `sup_τ E_x[S_τ | ξ]` over bounded stopping times, both
in `[0,∞]`, so that the paper's `= ∞` is a value and not a junk real.
-/
import LatticeProb.Graph.Walk
import LatticeProb.Graph.Scenery

open MeasureTheory
open scoped ENNReal

namespace LatticeProb.Graph

variable {V : Type*}

/-- `E_x[S_n | ξ]`, the expected payoff at the deterministic time `n`. -/
noncomputable def meanPayoff (G : SimpleGraph V) [G.LocallyFinite] (ξ : V → ℝ) (n : ℕ) (x : V) :
    ℝ :=
  walkExp G n x (payoff G ξ n)

/-- `sup_n E_x[S_n | ξ]`, in `[0,∞]`. -/
noncomputable def supMeanPayoff (G : SimpleGraph V) [G.LocallyFinite] (ξ : V → ℝ) (x : V) :
    ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal (meanPayoff G ξ n x)

/-- `sup_τ E_x[S_τ | ξ]` over bounded stopping times, in `[0,∞]`. -/
noncomputable def supStopValue (G : SimpleGraph V) [G.LocallyFinite] (ξ : V → ℝ) (x : V) : ℝ≥0∞ :=
  ⨆ (n : ℕ) (a : ℝ) (_ : a ∈ stopValues G ξ n x), ENNReal.ofReal a

/-- The joint law of the i.i.d. scenery with marginal `ν` and of the walk
started at `x`; the product records that the walk is independent of the
scenery. -/
noncomputable def jointLaw (G : SimpleGraph V) [G.LocallyFinite] [MeasurableSpace V]
    (ν : Measure ℝ) (x : V) : Measure ((V → ℝ) × (ℕ → V)) :=
  (iidLaw V ν).prod (walkLaw G x)

/-- `G` is doubly transient: `∑_v g(o,v)^2 < ∞` for every `o`. -/
def DoublyTransient (G : SimpleGraph V) [G.LocallyFinite] : Prop :=
  ∀ o : V, (∑' v : V, green G o v ^ 2) ≠ ⊤

/-- The degree of `G` is bounded by `d`. -/
def BoundedDegree (G : SimpleGraph V) [G.LocallyFinite] (d : ℕ) : Prop :=
  ∀ v : V, G.degree v ≤ d

/-- The connected component of `o` in `D`, empty when `o ∉ D`. -/
def compIn (G : SimpleGraph V) (D : Set V) (o : V) : Set V :=
  {x | ∃ h : o ∈ D, ∃ hx : x ∈ D, (G.induce D).Reachable ⟨o, h⟩ ⟨x, hx⟩}

/-- `Θ_C(y) = ∑_{v ∈ C} g_C(y,v)`, the inverse-degree exit time from `C`
started at `y` of `def:trap-family`.  The killed Green function vanishes off
`C`, so the sum over `V` is the paper's sum over `C`. -/
noncomputable def thetaExit (G : SimpleGraph V) [G.LocallyFinite] (C : Set V) (y : V) : ℝ≥0∞ :=
  ∑' v : V, killedGreen G C y v

/-- The uniform local trap condition . -/
def UniformLocalTrap (G : SimpleGraph V) [G.LocallyFinite] : Prop :=
  ∀ L : ℝ, 0 < L → ∃ rL ML : ℕ, ∀ y : V, ∃ C : Finset V,
    y ∈ C ∧ (C : Set V) ⊆ closedBall G y rL ∧ C.card ≤ ML ∧
      (G.induce (C : Set V)).Connected ∧ ENNReal.ofReal L ≤ thetaExit G (C : Set V) y

/-- The spectral dimension bound `eq:return-bound`,
`sup_x P_x(X_n = x) ≤ A n^{-d_s/2}` for all `n ≥ 1`. -/
def SpectralDimensionBound (G : SimpleGraph V) [G.LocallyFinite] (d_s A : ℝ) : Prop :=
  ∀ (x : V) (n : ℕ), 1 ≤ n → heat G n x x ≤ A * (n : ℝ) ^ (-d_s / 2)

/-- The volume growth hypothesis `|B(o,r)| ≤ C r^{d_f}` for all `r ≥ 1`. -/
def VolumeGrowthUpper (G : SimpleGraph V) (o : V) (C d_f : ℝ) : Prop :=
  ∀ r : ℕ, 1 ≤ r → (closedBall G o r).encard ≤ ENNReal.ofReal (C * (r : ℝ) ^ d_f)

/-- The volume lower bound `|B(o,r)| ≥ c r^{d_f}` for all `r ≥ 1`. -/
def VolumeGrowthLower (G : SimpleGraph V) (o : V) (c d_f : ℝ) : Prop :=
  ∀ r : ℕ, 1 ≤ r → ENNReal.ofReal (c * (r : ℝ) ^ d_f) ≤ (closedBall G o r).encard

/-- The walk dimension hypothesis `H3` of `prop:poly-growth`. -/
def WalkDimensionBound (G : SimpleGraph V) [G.LocallyFinite] [MeasurableSpace V]
    (d_w C_disp c_disp : ℝ) : Prop :=
  ∀ (x : V) (n r : ℕ), 1 ≤ n → 1 ≤ r →
    walkLaw G x {X | exitTime (closedBall G x r) X ≤ (n : ℕ∞)} ≤
      ENNReal.ofReal (C_disp * Real.exp (-c_disp * ((r : ℝ) ^ d_w / n) ^ (1 / (d_w - 1))))

open scoped Classical in
/-- The configuration `σ(v) = 1 + m·1_{v = o}` of `ex:finite-perturbation`. -/
noncomputable def spikeConfig (o : V) (m : ℝ) : V → ℝ := fun v => if v = o then 1 + m else 1

open scoped Classical in
/-- The scenery `ξ^{(v)}` with the value at `v` replaced by `t`, of
`lem:sensitivity`. -/
noncomputable def resample (ξ : V → ℝ) (v : V) (t : ℝ) : V → ℝ :=
  fun w => if w = v then t else ξ w

/-- `D_K = {x ∈ K : v_K(x) > 0}` of `prop:finite-vol`. -/
def activeSet (G : SimpleGraph V) [G.LocallyFinite] [MeasurableSpace V] (ξ : V → ℝ)
    (K : Set V) : Set V :=
  {x ∈ K | 0 < valueExit G ξ K x}

/-- `sup_v g_n(x,v)`, in `[0,∞]`. -/
noncomputable def supGreenTime (G : SimpleGraph V) [G.LocallyFinite] (n : ℕ) (x : V) : ℝ≥0∞ :=
  ⨆ v : V, ENNReal.ofReal (greenTime G n x v)

/-- `Y_k = (max_{2^k ≤ n < 2^{k+1}} W_n - |E[ξ]| 2^k / d)⁺` of `lem:dyadic`, for a
scenery `ξ` of mean `m` on a graph of degree bounded by `d`. -/
noncomputable def dyadicY (G : SimpleGraph V) [G.LocallyFinite] (ξ : V → ℝ) (m : ℝ) (d k : ℕ)
    (X : ℕ → V) : ℝ :=
  max ((⨆ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), fluctuation G ξ m n X)
    - |m| / d * 2 ^ k) 0

/-- The good-walk event `A_k = {max_v L_N(v) ≤ N^{α+δ}}` with `N = 2^{k+1}`, of
`lem:good-walk`. -/
def goodWalk (α δ : ℝ) (k : ℕ) : Set (ℕ → V) :=
  {X | ∀ v : V, (localTime (2 ^ (k + 1)) v X : ℝ) ≤ (2 ^ (k + 1) : ℝ) ^ (α + δ)}

/-- The simple random walk on `G` is recurrent at `o`: it returns to `o` with
probability one, equivalently `g(o,o) = ∞`. -/
def Recurrent (G : SimpleGraph V) [G.LocallyFinite] (o : V) : Prop := green G o o = ⊤

end LatticeProb.Graph
