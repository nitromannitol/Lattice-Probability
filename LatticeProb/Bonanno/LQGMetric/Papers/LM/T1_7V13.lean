/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.T1_7V13 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_7V10
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_7L2
import LatticeProb.Bonanno.LQGMetric.Papers.LM.C1_8Len

/-!
# LM Theorem 1.7: the variance node reduced to one probability measure `ν = κ_g`

Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), proof of Theorem 1.7 (l. 1000–1089) with decision D107 / D111.
`LMT17VarNodeK` (Papers/LM/T1_7L2.lean) is reduced to the statement `T17VarG` about a single
probability measure `ν` on metrics, which isolates exactly what the proof uses about `ν = κ_g`
(the conditional law of `D` given `h = g`):

* `ν`-a.e. metric is a length metric (`t17KernelLength`);
* the copy bound `d' ≤ C d` for `ν ⊗ ν`-a.e. pairs (`t17e_copy_kernel`, LM Lemma 5.1 input);
* for each mesh `ε_j = 1/(j+1)` and Lebesgue-a.e. grid shift `θ`, the internal metrics on the squares
  `t17Box ε (n+1)` are independent under `ν` (LM Lemma 5.4, `t17v_lem5_4_ae`).

`T17VarG` is the per-field Steps 1–3 of the repaired proof (D107 §3(i)–(v)).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric.LM

open Blueprint

/-- **N-VAR for one measure** (D107 §3(i)–(v), per field `g`, `ν = κ_g`) -/
def T17VarG : Prop :=
  ∀ (ν : Measure ContMetric) [IsProbabilityMeasure ν], (∀ᵐ d ∂ν, d.IsLength) →
    ∀ C : ℝ, 1 < C → (∀ᵐ p ∂ν.prod ν, ∀ z w : ℂ, p.2.1 (z, w) ≤ C * p.1.1 (z, w)) →
    ∀ (z w : ℂ) (n : ℕ), ‖z‖ < n → ‖w‖ < n →
    (∀ j : ℕ, ∀ᵐ θ ∂(volume : Measure (ℝ × ℝ)),
      ν.map (t17Y (1 / ((j : ℝ) + 1)) θ (t17Box (1 / ((j : ℝ) + 1)) ((n : ℝ) + 1))) =
        Measure.pi fun k : t17Box (1 / ((j : ℝ) + 1)) ((n : ℝ) + 1) =>
          ν.map (t17eEnc (t17Square (1 / ((j : ℝ) + 1)) θ k))) →
    ∫ d, ((t17F (n + 1) z w d).toReal - ∫ d', (t17F (n + 1) z w d').toReal ∂ν) ^ 2 ∂ν ≤
      C ^ 4 * ∫ d, ((t17F n z w d).toReal - (t17F (n + 1) z w d).toReal) *
        (t17F (n + 1) z w d).toReal ∂ν

/-- `LMT17VarNodeK` from the per-measure node -/
theorem t17_varNodeK_of_varG (H : T17VarG) : LMT17VarNodeK := by
  intro Ω _ P _ h D hh hloc C hCm hC1 hcopy z w n hz hw
  have hK := t17KernelLength P h D hh.measurable hloc.1 hloc.2.1
  have hB := t17e_copy_kernel hh.measurable hloc.1 hCm hcopy
  have hI := ae_all_iff.2 fun j : ℕ => t17v_lem5_4_ae hh hloc
    (ε := 1 / ((j : ℝ) + 1)) (by positivity) (t17Box (1 / ((j : ℝ) + 1)) ((n : ℝ) + 1))
  filter_upwards [hK, hB, hI] with g hKg hBg hIg
  exact H (condDistrib D h P g) hKg (C g) (hC1 g) hBg z w n hz hw hIg

/-- **LM Theorem 1.7** from the per-measure node -/
theorem lmThm1_7_of_varG (H : T17VarG) : LMThm1_7 :=
  lmThm1_7_of_varNodeK (t17_varNodeK_of_varG H)

/-- **LM Corollary 1.8** from the per-measure node -/
theorem lmCor1_8_of_varG (H : T17VarG) : Blueprint.LMCor1_8 :=
  lmCor1_8_of_thm1_7' (lmThm1_7_of_varG H)

end LQGMetric.LM
