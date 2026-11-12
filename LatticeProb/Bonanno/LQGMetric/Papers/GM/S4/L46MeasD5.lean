/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.L46MeasD5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasD3
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasD4
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasC1

/-!
# GM Lemma 4.6 (c) (task P2-E3c)

Source: GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
Lemma 4.6, last claim, proof l. 1709–1716.

* `gmStabEv`, `gmHitBall`: the events `Stab_{k,r}(z)` and `{P ∩ B_r(z) ≠ ∅}` (`P|_{[0, D(𝕫,𝕨)]}`
  the unit-speed form of the geodesic `η` from `𝕫` to `𝕨`);
* `gm_arcHit_ae_eq_hitU`: on `Stab ∩ Hit`, a.s., the hit events of the arc of `𝓘_k` containing
  `P(t_k)` are the metric events `gmHitUSet` (GM l. 1709–1712, `gm_arcHit_iff_hitU`);
* `gm_L4_6_hArc`: the second input `hArc` of `gm_L4_6c_of` (GM l. 1712–1714: "the arc … is
  determined by `h|_{ℂ∖B_r(z)}`" on `Stab ∩ Hit`), via the glue `gm_aeEventIn_of_local`;
* `gm_L4_6c`: GM Lemma 4.6 (c) in the `hL46` form of `gm_L4_7_pair`, from Lemma 4.5 (E2b) and the
  remaining input `hA` (traces of `σ(𝓑^•_{t_k}, h|_{𝓑^•_{t_k}})`, P2-E2R's random-set locality).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric MeasurableSpace
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM
open LocalEvent

variable {Ω : Type} [MeasurableSpace Ω]

/-- the event `Stab_{k,r}(z)` (GM (4.10), (4.11)) -/
def gmStabEv (D : DistC → ContMetric) (h : Ω → DistC) (𝕫 : ℂ) (ℓ 𝕣 ε β : ℝ) (k : ℕ)
    (lam1 lam4 ν : ℝ) (Rads : Set ℝ) (z : ℂ) (r : ℝ) : Set Ω :=
  {ω | (z, r) ∈ candSet (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β k ω)) lam1 lam4 ε ν 𝕣
        Rads ∧ stabCond (D (h ω)) 𝕫 (s4S D h 𝕫 ℓ 𝕣 ε β k ω) (s4T D h 𝕫 ℓ 𝕣 ε β k ω) z r}

/-- the event `{P ∩ B_r(z) ≠ ∅}` -/
def gmHitBall (D : DistC → ContMetric) (h : Ω → DistC) (𝕫 𝕨 : ℂ) (η : Ω → C(unitInterval, ℂ))
    (z : ℂ) (r : ℝ) : Set Ω :=
  {ω | ∃ u ∈ Icc 0 ((D (h ω)).1 (𝕫, 𝕨)), geodL (D (h ω)) 𝕫 𝕨 (η ω) u ∈ ball z r}

end LQGMetric.GM
