/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_10 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.10 (`lem-square-bdy-dist`, T:943–950): statement

"For `r > 0`, let `S_r(0)` be the closed square of side length `r` centered at zero. Let `h` be a
whole-plane GFF plus a bounded continuous function. For each `p ∈ (0,1)` and each `C > 0`, there
exists `R = R(p,C) > 1` (depending on `p, C` and the law of `h`) such that for each fixed `r > 0`,
`liminf_{ε→0} P[sup_{u,v∈S_r(0)} D_h^ε(u,v) < C⁻¹ D_h^ε(S_r(0), ∂S_{Rr}(0))] ≥ p`."

Readings: distances in `[0,∞]` (`lfppDistE`), sup/inf as `⨆`/`⨅`; `liminf_{ε→0}` along
`𝓝[>] 0`; `R` is chosen after the probability space and `h` (the paper: after the law of `h`;
consumers fix `h`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS

open Blueprint

/-- the closed square `S_s(z)` of side length `s` centred at `z` -/
def sqC (s : ℝ) (z : ℂ) : Set ℂ := closedSq (z - ((s / 2 : ℝ) : ℂ) * (1 + Complex.I)) s

/-- the event of DFGPS (2.10) (`eqn-square-bdy-dist`): `sup_{u,v∈S_r(0)} D^ε_h(u,v) <
C⁻¹ D^ε_h(S_r(0), ∂S_{Rr}(0))` -/
def sqBdyEvent (ξ ε C r R : ℝ) (g : DistC) : Prop :=
  (⨆ u ∈ sqC r 0, ⨆ v ∈ sqC r 0, lfppDistE ξ ε g u v) <
    ENNReal.ofReal C⁻¹ * ⨅ u ∈ sqC r 0, ⨅ v ∈ frontier (sqC (R * r) 0), lfppDistE ξ ε g u v

/-- **DFGPS Lemma 2.10** (`lem-square-bdy-dist`, T:943–950), exact statement. -/
def Lem2_10 : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
      IsGFFPlusBddCont h P → ∀ p ∈ Ioo (0 : ℝ) 1, ∀ C : ℝ, 0 < C → ∃ R : ℝ, 1 < R ∧
        ∀ r : ℝ, 0 < r → ENNReal.ofReal p ≤
          liminf (fun ε => P {ω | sqBdyEvent (xiGamma γ) ε C r R (h ω)}) (𝓝[>] 0)

end LQGMetric.DFGPS
