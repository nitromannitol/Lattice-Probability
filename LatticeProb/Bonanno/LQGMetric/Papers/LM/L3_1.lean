/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.L3_1 at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_1Core

/-!
# LM Lemma 3.1 (`N = 0`) from its inputs (3.8), (3.9), (3.10)

Source: LM = Gwynne–Miller, *Local metrics of the Gaussian free field*, arXiv:1905.00379,
`literature/src/1905.00379/local-metrics-final.tex`, Lemma 3.1 (`lem-annulus-iterate`,
l. 573–590) and its proof (l. 723–764).

LM's proof uses three facts about the field, all stated for the filtration
`𝓕_{r_k} = σ((h − h_{r_k}(0))|_{ℂ∖B_{r_k}(0)})` (eq. (3.4), here `lmF h (r k)`):
* (3.9), l. 731–734: `E_{r_k} ∈ 𝓕_{s₁r_k} ⊂ 𝓕_{r_{k+1}}` (from Lemma 3.2);
* (3.8), l. 725–730: on the `𝓕_{r_k}`-measurable good event `{𝔐^{r_k}_{s'r_k} ≤ M}`,
  `P[E | 𝓕_{r_k}]` is bounded below in terms of `P[E]` (Lemma 3.3 + Hölder). We record the two
  Hölder consequences of the moment bounds of Lemma 3.3 (`α = 2` for `H`, `α = 1` for `H^{-1}`):
  `P[E | 𝓕] ≥ 1 − C √(1 − P[E])` and `P[E | 𝓕] ≥ P[E]² / C`
  (`blueprint/LocalMetrics.md`, note to LM.L3.1);
* (3.10), l. 736–740: Lemma 3.4, the number of good scales among the first `K` is `≥ bK` except
  on an event of probability `≤ c₀ e^{−aK}`.
These are bundled in `LMAnnulusIterInput` (the filtration and good events are those of LM, but
only their properties are used here, so they are existentially quantified; in
`LQGMetric.Papers.LM.L3_1Main` the filtration is fixed to LM's `𝓕_{r_k}`, null-augmented). From it, `lmLem3_1a_of_input` and
`lmLem3_1b_of_input` prove `Blueprint.LMLem3_1a` and `Blueprint.LMLem3_1b` following l. 744–763
(via `prob_countOcc_lt_le`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory

namespace LQGMetric.LM

open Blueprint

/-- `h − h_r(0)`. -/
def recentre {Ω : Type} (h : Ω → DistC) (r : ℝ) : Ω → DistC :=
  fun ω => addConst (h ω) (-circleAvg (h ω) r 0)

/-- `𝓕_r = σ((h − h_r(0))|_{ℂ∖B_r(0)})` (LM eq. (3.4), `N = 0`). -/
def lmF {Ω : Type} (h : Ω → DistC) (r : ℝ) : MeasurableSpace Ω :=
  fieldSigmaClosed (recentre h r) (Metric.ball (0 : ℂ) r)ᶜ

/-- `σ((h − h_r(0))|_{A_{s₁r, s₂r}(0)})` (LM eq. (3.1), `N = 0`). -/
def annSigma {Ω : Type} (h : Ω → DistC) (s₁ s₂ r : ℝ) : MeasurableSpace Ω :=
  fieldSigma (recentre h r) (annulus 0 (s₁ * r) (s₂ * r))

lemma measure_le_ofReal_of_real {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {s : Set Ω} {x : ℝ} (h : P.real s ≤ x) : P s ≤ ENNReal.ofReal x := by
  rw [← ofReal_measureReal]; exact ENNReal.ofReal_le_ofReal h

lemma real_ge_of_ofReal_le {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {s : Set Ω} {p : ℝ} (h : ENNReal.ofReal p ≤ P s) : p ≤ P.real s := by
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top P s)).1 h

end LQGMetric.LM
