/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39J3e at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39J3d
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39H3
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.JordanJ1bFinal
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412fHit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The arcs of `∂𝓑^•_τ` (DEC-120 §4, packet J3: adapter for J5/J6)

`t39jA c D h z₀ τ m i ω := c.arcs m i (∂𝓑^•_τ(ω))` for an arc choice `c : T39JArcChoice`
(e.g. `t39jArcChoice`, S3T39J3d). CONF C:1514, 1740–1744 ("chosen in a manner depending only on
`𝓑^•_τ`"), DV-D120-1.

* `t39jA_subset` (the `hI₀` field of `T39JRestData`): `A m i ω ⊆ ∂𝓑^•_τ`, surely;
* `t39jA_sep`: the separation hypothesis of `CONFThm3_9RestC`, a.s. on
  `{0 < τ, D_h length metric, 𝓑_τ bounded}` (`GM.gm_filledBall_frontier_isJordanCurve'`);
* `t39jA_conn`, `t39jA_disj`: connected, disjoint arcs on the same event;
* `t39j_frontier_measurable`: `ω ↦ ∂A(ω)` is `setSigma A`/`effrosSigma`-measurable
  (`GM.p412f_frontier_hit_meas`), so **every Effros-measurable functional of the arcs is
  `σ(𝓑^•_τ)`-measurable**; `t39jA_hit_meas`, `t39jA_hit_meas0` (hit events of the arcs in
  `setSigma 𝓑^•_τ` and in `filledBallSigmaAt0 D h z₀ (ofReal ∘ τ)`).
-/

noncomputable section

open MeasureTheory Set Filter
open LQGMetric.Blueprint

namespace LQGMetric.CONF

variable {Ω : Type}

/-- **the arcs of `∂𝓑^•_τ`** -/
def t39jA (c : T39JArcChoice) (D : DistC → ContMetric) (h : Ω → DistC) (z₀ : ℂ) (τ : Ω → ℝ)
    (m : ℕ) (i : Fin m) (ω : Ω) : Set ℂ :=
  c.arcs m i (frontier (filledBall (D (h ω)) z₀ (τ ω)))

theorem t39jA_subset (c : T39JArcChoice) (D : DistC → ContMetric) (h : Ω → DistC) (z₀ : ℂ)
    (τ : Ω → ℝ) (m : ℕ) (i : Fin m) (ω : Ω) :
    t39jA c D h z₀ τ m i ω ⊆ frontier (filledBall (D (h ω)) z₀ (τ ω)) := by
  have := c.subset m i (frontier (filledBall (D (h ω)) z₀ (τ ω)))
  rwa [isClosed_frontier.closure_eq] at this

/-- `∂𝓑^•_τ` is a Jordan curve on the good event -/
theorem t39jA_jordan {D : DistC → ContMetric} {h : Ω → DistC} {z₀ : ℂ} {τ : Ω → ℝ} {ω : Ω}
    (hω : 0 < τ ω ∧ (D (h ω)).IsLength ∧ Bornology.IsBounded (ballM (D (h ω)) z₀ (τ ω))) :
    JordanMap.IsJordanCurve (frontier (filledBall (D (h ω)) z₀ (τ ω))) :=
  GM.gm_filledBall_frontier_isJordanCurve' hω.1 hω.2.1 hω.2.2

theorem t39jA_conn (c : T39JArcChoice) {D : DistC → ContMetric} {h : Ω → DistC} {z₀ : ℂ}
    {τ : Ω → ℝ} {ω : Ω}
    (hω : 0 < τ ω ∧ (D (h ω)).IsLength ∧ Bornology.IsBounded (ballM (D (h ω)) z₀ (τ ω)))
    (m : ℕ) (i : Fin m) (hne : (t39jA c D h z₀ τ m i ω).Nonempty) :
    IsPreconnected (t39jA c D h z₀ τ m i ω) :=
  c.conn m i _ (t39jA_jordan hω) hne

theorem t39jA_disj (c : T39JArcChoice) {D : DistC → ContMetric} {h : Ω → DistC} {z₀ : ℂ}
    {τ : Ω → ℝ} {ω : Ω}
    (hω : 0 < τ ω ∧ (D (h ω)).IsLength ∧ Bornology.IsBounded (ballM (D (h ω)) z₀ (τ ω)))
    (m : ℕ) : Pairwise (Function.onFun Disjoint fun i => t39jA c D h z₀ τ m i ω) :=
  c.disj m _ (t39jA_jordan hω)

/-- **the separation hypothesis of `CONFThm3_9RestC`** -/
theorem t39jA_sep [MeasurableSpace Ω] {P : Measure Ω} (c : T39JArcChoice)
    (D : DistC → ContMetric) (h : Ω → DistC) (z₀ : ℂ) (τ : Ω → ℝ)
    (hgood : ∀ᵐ ω ∂P, 0 < τ ω ∧ (D (h ω)).IsLength ∧
      Bornology.IsBounded (ballM (D (h ω)) z₀ (τ ω))) :
    ∀ᵐ ω ∂P, ∀ F : Finset ℂ, (F : Set ℂ) ⊆ frontier (filledBall (D (h ω)) z₀ (τ ω)) →
      ∀ᶠ m in atTop, (∀ x ∈ F, ∃ i, x ∈ t39jA c D h z₀ τ m i ω) ∧
        ∀ i, ∀ x ∈ F, ∀ y ∈ F, x ∈ t39jA c D h z₀ τ m i ω → y ∈ t39jA c D h z₀ τ m i ω →
          x = y :=
  hgood.mono fun _ hω F hF => c.sep _ (t39jA_jordan hω) F hF

end LQGMetric.CONF
