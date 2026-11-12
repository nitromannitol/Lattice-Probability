/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.L3_1N2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Blueprint.LMResults

/-!
# LM Lemma 3.1 (1) with `N = 2` metrics (statement only; task P2-LM42)

Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), Lemma 3.1 (`lem-annulus-iterate`, l. 573–585), standing assumptions
l. 568: `h` a whole-plane GFF with `h_1(0) = 0`, `ξ ∈ ℝ`, and `D_1, …, D_N` jointly local and
`ξ`-additive for `h`; here `N = 2` (used in the proof of LM Lemma 4.1, l. 812–815).

The events `E_{r_k}` are measurable w.r.t.
`σ((h − h_{r_k}(0))|_{A_{s₁r_k,s₂r_k}(0)}, {e^{−ξh_{r_k}(0)} D_n(·,·; A_{s₁r_k,s₂r_k}(0))}_{n ≤ 2})`
(LM l. 574–575). This is an LM-internal node (orchestrator decision for P2-LM42, D21), proved
elsewhere; the `N = 0` case is `Blueprint.LMLem3_1a`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace LQGMetric.LM

open Blueprint

/-- the scaled internal metrics `e^{−ξ h_r(0)} D(·,·;V)` (LM l. 575) -/
def normIntFam {Ω : Type} (ξ : ℝ) (h : Ω → DistC) (D : Ω → ContMetric) (r : ℝ) :
    Ω → Set ℂ → ℂ → ℂ → ℝ≥0∞ :=
  fun ω V u v => ENNReal.ofReal (Real.exp (-ξ * circleAvg (h ω) r 0)) * (D ω).internal V u v

/-- the hypotheses of LM Lemma 3.1 with `N = 2` (LM l. 574–575): `(r_k)` decreasing positive with
`r_{k+1}/r_k ≤ s₁`, and each `E_{r_k}` measurable w.r.t.
`σ((h − h_{r_k}(0))|_{A_k}, e^{−ξh_{r_k}(0)} D₁(·,·;A_k), e^{−ξh_{r_k}(0)} D₂(·,·;A_k))`,
`A_k = A_{s₁r_k, s₂r_k}(0)`. -/
def AnnulusIterHypN2 {Ω : Type} (ξ : ℝ) (h : Ω → DistC) (D₁ D₂ : Ω → ContMetric) (s₁ s₂ : ℝ)
    (r : ℕ → ℝ) (E : ℕ → Set Ω) : Prop :=
  (∀ k, 0 < r k) ∧ Antitone r ∧ (∀ k, r (k + 1) / r k ≤ s₁) ∧
    ∀ k, MeasurableSet[fieldSigma (fun ω => addConst (h ω) (-circleAvg (h ω) (r k) 0))
        (annulus 0 (s₁ * r k) (s₂ * r k)) ⊔
      famSigma (normIntFam ξ h D₁ (r k)) (annulus 0 (s₁ * r k) (s₂ * r k)) ⊔
      famSigma (normIntFam ξ h D₂ (r k)) (annulus 0 (s₁ * r k) (s₂ * r k))] (E k)

/-- **LM Lemma 3.1 (1)** (`lem-annulus-iterate`, l. 573–585) with `N = 2`: "For each `a > 0` and
each `b ∈ (0,1)`, there exists `p = p(a,b,s₁,s₂) ∈ (0,1)` and `c = c(a,b,s₁,s₂) > 0` such that if
`P[E_{r_k}] ≥ p` for all `k`, then `P[𝒩(K) < bK] ≤ c e^{−aK}` for all `K ∈ ℕ`." -/
def LMLem3_1aN2 : Prop :=
  ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ → s₂ < 1 → ∀ a : ℝ, 0 < a → ∀ b : ℝ, 0 < b → b < 1 →
    ∃ p c : ℝ, 0 < p ∧ p < 1 ∧ 0 < c ∧
      ∀ (ξ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC) (D₁ D₂ : Ω → ContMetric),
        IsNormalizedWPGFF h P → IsXiAdditive2 ξ P h D₁ D₂ →
        ∀ (r : ℕ → ℝ) (E : ℕ → Set Ω), AnnulusIterHypN2 ξ h D₁ D₂ s₁ s₂ r E →
        (∀ k, ENNReal.ofReal p ≤ P (E k)) →
        ∀ K : ℕ, P {ω | (countOcc E K ω : ℝ) < b * K} ≤ ENNReal.ofReal (c * Real.exp (-a * K))

end LQGMetric.LM
