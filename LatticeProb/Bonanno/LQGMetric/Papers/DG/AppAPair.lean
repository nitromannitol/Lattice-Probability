/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.AppAPair at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.AppA1Main

/-!
DG (`metric-comparison-final.tex`, proof of Lemma 3.1, DG:2243–2244): "Combine Lemmas 2.2, A.1
and A.2." For the pair `(h^U, ĥ)` with all fields built from one white noise `W`:
`h^U − ĥ = (h^U − ĥ^tr) − (ĥ − ĥ^tr)`, with kernel `dgA1Kernel U z − hatDiffKernel0 z`; its
`L²` increments are bounded by those of A.1 (`dg_A1_var_box`) and A.2 (`dg_A2_var0`), and
`exists_box_modification_tail` gives the continuous modification and (3.5).

* `dg_lemma31_hU_hat_wn` — DG (3.5) for `(h^1, h^2) = (h^U, ĥ)` on a box `K` with
  `B(z, 1/10) ⊆ U` for `z ∈ K` (DEVIATIONS DG3C-1).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace LQGMetric
namespace DG

open KilledHeat WhiteNoise DZZ SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- The kernel of `(h^U − ĥ)(z)`. -/
def dgUHatKernel (U : Set ℂ) (z : ℂ) : WNSpace := dgA1Kernel U z - hatDiffKernel0 z

/-- **DG Lemma 3.1, pair `(h^U, ĥ)`** (white-noise form, `K` a box). -/
theorem dg_lemma31_hU_hat_wn (hW : IsWhiteNoise P W) {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {y : ℂ} {b : ℝ} (hb : 0 < b)
    (hK : ∀ z ∈ ferniqueBox y b, Metric.ball z (1 / 10) ⊆ U) :
    ∃ Y : ℂ → Ω → ℝ, (∀ ω, Continuous fun z => Y z ω) ∧ (∀ z, Measurable (Y z)) ∧
      (∀ z ∈ ferniqueBox y b, Y z =ᵐ[P] fun ω => Real.sqrt Real.pi * W (dgUHatKernel U z) ω) ∧
      ∃ c₀ c₁ : ℝ, 0 < c₁ ∧ ∀ A : ℝ, 0 ≤ A →
        P {ω | ¬ ∀ z ∈ ferniqueBox y b, |Y z ω| ≤ A} ≤
          ENNReal.ofReal (c₀ * Real.exp (-c₁ * A ^ 2)) := by
  have hpi := Real.pi_pos
  obtain ⟨L, hL0, hL⟩ := dg_A1_var_box hU hUb hb hK
  obtain ⟨C, hC⟩ := dg_A2_var0
  refine exists_box_modification_tail hW _ hb (L := 2 * L + 2 * (max C 0 / Real.pi))
    (by positivity) fun x hx c hc => ?_
  have h1 := hL x hx c hc
  have h2 : ‖hatDiffKernel0 x - hatDiffKernel0 c‖ ^ 2 ≤ max C 0 / Real.pi * ‖x - c‖ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hpi]
    nlinarith [hC x c, mul_le_mul_of_nonneg_right (le_max_left C 0) (norm_nonneg (x - c))]
  have e : dgUHatKernel U x - dgUHatKernel U c =
      (dgA1Kernel U x - dgA1Kernel U c) - (hatDiffKernel0 x - hatDiffKernel0 c) := by
    unfold dgUHatKernel; abel
  rw [e]
  have hsq : ∀ u v : WNSpace, ‖u - v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := fun u v => by
    have := norm_sub_le u v
    nlinarith [norm_nonneg (u - v), norm_nonneg u, norm_nonneg v, sq_nonneg (‖u‖ - ‖v‖)]
  refine (hsq _ _).trans ?_
  nlinarith

end DG
end LQGMetric
