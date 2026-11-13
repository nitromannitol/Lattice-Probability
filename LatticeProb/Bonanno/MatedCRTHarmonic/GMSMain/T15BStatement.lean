/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSMain.T15BStatement at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS3.Energy
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.CellularEmbedding
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.VerticesMeeting

/-!
# [18] Theorem 1.5 and Theorem 3.9′: the predicates

Source: Gwynne–Miller–Sheffield, *Harmonic functions on mated-CRT maps* [18]: the boundary data (1.6) and "the discrete harmonic function `f_ε`", Theorem 1.5 ((1.9), `[18]`) and the boundary estimate of Theorem 3.9 in form (3.31′).

* `IsHarmonicExtension G J D f g`: `g` is discrete harmonic (`GMS3.lap G g x = 0`) at every vertex of
  `V(D) \ V(∂D)` and equals the (1.6) value `sup_{z ∈ J_x ∩ ∂D} f(z)` at every vertex of `V(D) ∩ V(∂D)` (the
  function `f_ε : V(D) → ℝ` of [18]; values off `V(D)` are irrelevant). It is T16D's
  `IsCellDirichletSolution H D (bdryVal H D f) g` read on sets (for bounded `D`: `T16D.coe_vFin`, `T16D.coe_vBd`).
* `BoundaryEstimate G J pt D s C ξ` — **(3.31′) on one environment**, the named input produced by
  for every `u` discrete harmonic on `V(D) \ V(∂D)` with `|u| ≤ M` on `V(D)`, every interior vertex `x`,
  every `t > δ_x := dist(pt x, ∂D)` and every upper bound `c` of `u` on the vertices of `V(D)` whose cells meet
  `∂D ∩ B_t(pt x)` with `c ≥ −M`: `u(x) ≤ c + C · M · ((δ_x ∨ s)/t)^ξ` (the lower bound follows for `−u`). This is the
  `f_ε(x) ≤ max_{V(∂D∩B_t(η(x)))} f_ε + C‖f_ε‖(t/(δ_x ∨ ε^β))^{−ξ₀}` with `pt x = η(x)`, `s = ε^β`; the guard
  `t > δ_x` is the range where `∂D ∩ B_t(η(x)) ≠ ∅`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric

namespace MatedCRTHarmonic.GMSMain.T15B

variable {V E : Type*}

/-- **The discrete harmonic function `f_ε` of [18] (1.6)**: `g` equals the boundary value
`sup_{z ∈ J_x ∩ ∂D} f(z)` at every vertex `x ∈ V(D)` whose cell meets `∂D`, and is discrete harmonic at every vertex
of `V(D) \ V(∂D)`. -/
def IsHarmonicExtension (G : LFMultigraph V E) (J : V → Set ℂ) (D : Set ℂ) (f : ℂ → ℝ) (g : V → ℝ) : Prop :=
  (∀ x ∈ verticesMeeting J D, x ∈ verticesMeeting J (frontier D) → g x = sSup (f '' (J x ∩ frontier D))) ∧
    ∀ x ∈ verticesMeeting J D, x ∉ verticesMeeting J (frontier D) → GMS3.lap G g x = 0

/-- **[18] (3.31′), the boundary continuity estimate on one environment** (the
named input, produced ): for every function `u` discrete harmonic on `V(D) \ V(∂D)` with
`|u| ≤ M` on `V(D)`, every vertex `x` of `V(D) \ V(∂D)`, every `t > dist(pt x, ∂D)` and every bound `c ≥ u` on the
vertices of `V(D)` whose cells meet `∂D ∩ B_t(pt x)` with `c ≥ −M` (automatic when that vertex set is nonempty):
`u(x) ≤ c + C · M · ((dist(pt x, ∂D) ∨ s)/t)^ξ`. 's `T15CBoundaryEstimate` (all `x ∈ V(D)`, all points of
`H_x`, error `A M (t/(dist ∨ ε^β))^{−ξ}`, uniform in `D`) specializes to it (`boundaryEstimate_of_t15c`). -/
def BoundaryEstimate (G : LFMultigraph V E) (J : V → Set ℂ) (pt : V → ℂ) (D : Set ℂ) (s C ξ : ℝ) : Prop :=
  ∀ (u : V → ℝ) (M : ℝ),
    (∀ v ∈ verticesMeeting J D, v ∉ verticesMeeting J (frontier D) → GMS3.lap G u v = 0) →
    (∀ v ∈ verticesMeeting J D, |u v| ≤ M) →
    ∀ x ∈ verticesMeeting J D, x ∉ verticesMeeting J (frontier D) →
    ∀ t : ℝ, infDist (pt x) (frontier D) < t →
    ∀ c : ℝ, (∀ a ∈ verticesMeeting J D, a ∈ verticesMeeting J (frontier D ∩ ball (pt x) t) → u a ≤ c) →
      -M ≤ c → u x ≤ c + C * M * (max (infDist (pt x) (frontier D)) s / t) ^ ξ

end MatedCRTHarmonic.GMSMain.T15B
