/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L11In2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L11Scale

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Pathwise step `E_S(ĥ^tr) ⟹ E_S(ĥ)` of DG Lemma 3.11 (P2-DG105l)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, proof of Lemma 3.11 (DG:1226):
(eqn-rectangle-perc-truncated) for `ĥ^tr` is "combined with (eqn-gff-compare) (applied with
`A = c n^{1/2}`)", i.e. DG Lemma 3.2's deterministic step (DG:1005–1007): on the event
`max_K |ĥ − ĥ^tr| ≤ A`, `dμ_ĥ = e^{γ(ĥ − ĥ^tr)} dμ_{ĥ^tr}` gives
`D^{e^{γA} ε'}_{ĥ}(·,·;U) ≤ D^{ε'}_{ĥ^tr}(·,·;U)`, and `D^ε` decreases in `ε` (DG:1260).

* `dgLGD_anti_eps`: `D^ε` is antitone in `ε` (DG:1260);
* **`goodSq_muHat_of_muTr`**: the event `E_S` of DG:1240 transfers from `μ_{ĥ^tr}` at level `ε'`
  to `μ_ĥ` at level `ε ≥ e^{γA} ε'`, for one white noise `W'`, on `{max_K |hatMod'| ≤ A/2,
  max_K |trMod'| ≤ A/2}` (the event whose probability is bounded uniformly in `W'` by
  `hatTr_tail_uniform`, S3L11In1).
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DG

open WhiteNoise SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- `D^ε` is antitone in `ε` (DG:1260) -/
lemma dgLGD_anti_eps (μ : Measure ℂ) {ε₁ ε₂ : ℝ} (h : ε₂ ≤ ε₁) (U : Set ℂ) (z w : ℂ) :
    dgLGD μ ε₁ U z w ≤ dgLGD μ ε₂ U z w :=
  dgLGD_le_of_ball (fun _ _ _ hB => hB.trans (ENNReal.ofReal_le_ofReal h)) z w

/-- **`E_S(ĥ^tr) ⟹ E_S(ĥ)`** (DG:1226 with DG:1005–1007), pathwise for one white noise. -/
theorem goodSq_muHat_of_muTr {W' : WNSpace → Ω → ℝ} (hW' : IsWhiteNoise P W') {γ : ℝ}
    (hγ : 0 ≤ γ) {y : ℂ} {b : ℝ} (hb : 0 < b)
    (hK : ∀ z ∈ ferniqueBox y b, Metric.ball z (1 / 10) ⊆ openSquare) {s : ℝ} {c : ℂ}
    {x : ℤ × ℤ} (hsq : sqOne s c x ⊆ ferniqueBox y b) {A ε ε' M : ℝ} {ω : Ω}
    (hω : ∀ z ∈ ferniqueBox y b, |hatMod hW' hb hK z ω| ≤ A / 2 ∧ |trMod hW' hb hK z ω| ≤ A / 2)
    (hε : Real.exp (γ * A) * ε' ≤ ε) (h : goodSq (muTr hW' γ hb hK ω) ε' s c M x) :
    goodSq (muHat hW' γ hb hK ω) ε s c M x := by
  obtain ⟨hc₁, -, -, -⟩ := hatMod_spec hW' hb hK
  obtain ⟨hc₂, -, -, -⟩ := trMod_spec hW' hb hK
  have e : muHat hW' γ hb hK ω = (muTr hW' γ hb hK ω).withDensity
      fun z => ENNReal.ofReal (Real.exp (γ * (trMod hW' hb hK z ω - hatMod hW' hb hK z ω))) :=
    muOfMod_eq_withDensity W' γ _ hc₁ hc₂ ω
  have hg : ∀ z ∈ closure (sqOne s c x),
      |γ * (trMod hW' hb hK z ω - hatMod hW' hb hK z ω)| ≤ Real.log (Real.exp (γ * A)) := by
    intro z hz
    rw [(isClosed_sqOne s c x).closure_eq] at hz
    obtain ⟨h1, h2⟩ := hω z (hsq hz)
    rw [Real.log_exp, abs_mul, abs_of_nonneg hγ]
    refine mul_le_mul_of_nonneg_left ?_ hγ
    calc |trMod hW' hb hK z ω - hatMod hW' hb hK z ω|
        ≤ |trMod hW' hb hK z ω| + |hatMod hW' hb hK z ω| := abs_sub _ _
      _ ≤ A / 2 + A / 2 := add_le_add h2 h1
      _ = A := by ring
  intro u hu v hv
  refine le_trans ?_ (h u hu v hv)
  rw [e]
  refine ENat.toENNReal_le.2 ((dgLGD_anti_eps _ hε _ u v).trans ?_)
  exact (dgLGD_compare_of_withDensity (Real.exp_pos _) hg u v).1

end DG
end LQGMetric
