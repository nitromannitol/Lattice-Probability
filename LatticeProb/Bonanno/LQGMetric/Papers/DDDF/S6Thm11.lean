/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6Thm11 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6T20Done
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffSq
import LatticeProb.Bonanno.LQGMetric.LFPP.Tight
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# DDDF Theorem 1 (1) from the uniform Hölder bounds (task P2-DDDF6e, packet O7)

DDDF = arXiv:1904.08021, `tightness.tex` l. 155–160 (Theorem 1 (1)), l. 1385–1490 (Prop 28:
"(UpperHolder)" l. 1398–1401 and "(LowerHolder)" l. 1450–1453) and l. 1648 (the family
`δ ∈ (0,1)`, "the same argument"). Prop 28's proof ends with: the upper bound on the modulus of
continuity gives tightness in `C([0,1]² × [0,1]², ℝ⁺)` (Part 1, l. 1441–1443), and the two
Hölder bounds give the bi-Hölder property of subsequential limits.

This file proves `Blueprint.DDDFThm1_1` from (UpperHolder) and (LowerHolder) for the family
`(λ_δ^{-1} e^{ξ φ_δ} ds)_{δ ∈ (0,1)}` (`S6UpperHolderD`, `S6LowerHolderD`):
* continuity of `(x,y) ↦ λ_δ^{-1} d_δ(x,y)` for every `ω` (`continuous_lfppDOn_toReal`);
* tightness by the modulus criterion `LFPP.isTightMeasureSet_of_modulus` (Arzelà–Ascoli,
  Billingsley Thm 7.3);
* bi-Hölder limits by the Portmanteau theorem on the closed sets
  `{d | ∀ x y, c|x−y|^α ≤ d(x,y) ≤ C|x−y|^β}` (`ProbabilityMeasure.limsup_measure_closed_le_of_tendsto`).
`λ_δ > 0` comes from (6.98) (`s6_eq6_98_of_554`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace LQGMetric
namespace DDDF
namespace S6Thm

open WhiteNoise Blueprint DFGPS

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **DDDF (UpperHolder)** (l. 1398–1401) for the family `δ ∈ (0,1)` (l. 1648): for every
`ε > 0` there is `C` with `P(∃ x, x' : d_δ(x,x') > C |x − x'|^β) ≤ ε` uniformly in `δ`. -/
def S6UpperHolderD (ξ : ℝ) (W : WNSpace → Ω → ℝ) (P : Measure Ω) (β : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ δ ∈ Ioo (0 : ℝ) 1,
    P {ω | ∃ x y : closedUnitSquare, C * ‖(x : ℂ) - y‖ ^ β <
      (lambdaDelta ξ W P δ)⁻¹ * lenMetricOn ξ (fun z => phiVer W P δ 1 z ω) closedUnitSquare x y}
      ≤ ENNReal.ofReal ε

/-- **DDDF (LowerHolder)** (l. 1450–1453) for the family `δ ∈ (0,1)` (l. 1648): for every
`ε > 0` there is `c > 0` with `P(∃ x, x' : d_δ(x,x') < c |x − x'|^α) ≤ ε` uniformly in `δ`. -/
def S6LowerHolderD (ξ : ℝ) (W : WNSpace → Ω → ℝ) (P : Measure Ω) (α : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∀ δ ∈ Ioo (0 : ℝ) 1,
    P {ω | ∃ x y : closedUnitSquare, (lambdaDelta ξ W P δ)⁻¹ *
      lenMetricOn ξ (fun z => phiVer W P δ 1 z ω) closedUnitSquare x y < c * ‖(x : ℂ) - y‖ ^ α}
      ≤ ENNReal.ofReal ε

lemma cont_sqLen {ξ : ℝ} {f : ℂ → ℝ} (hf : Continuous f) (a : ℝ) :
    Continuous fun p : closedUnitSquare × closedUnitSquare =>
      a⁻¹ * lenMetricOn ξ f closedUnitSquare p.1 p.2 := by
  simp only [lenMetricOn, crossLenIn_singleton]
  exact continuous_lfppDOn_toReal hf DFGPS.convex_closedUnitSquare
    closedUnitSquare_subset_closedBall _

lemma sqMetricC_apply' {ξ a : ℝ} {f : ℂ → ℝ} (hf : Continuous f)
    (p : closedUnitSquare × closedUnitSquare) :
    sqMetricC ξ a f p = a⁻¹ * lenMetricOn ξ f closedUnitSquare p.1 p.2 :=
  toCMap_apply_of_continuous (cont_sqLen hf a) p

/-- `λ_δ > 0` for `δ ∈ (0,1)`, from (6.98) and `λ_n > 0` -/
lemma lambdaDelta_pos_of_698 {ξ : ℝ} (hW : IsWhiteNoise P W) (h698 : S6Eq6_98 ξ W P) {δ : ℝ}
    (hδ : δ ∈ Ioo (0 : ℝ) 1) : 0 < lambdaDelta ξ W P δ := by
  obtain ⟨C, hC⟩ := h698
  obtain ⟨n, r, hr0, hr1, rfl⟩ := S6.exists_split hδ.1 hδ.2
  exact lt_of_lt_of_le (mul_pos (Real.exp_pos _) (lambdaN_pos hW n)) (hC n r hr0 hr1).1

/-- the random metric is a pseudo-metric for every `ω` -/
lemma pmet_sq {ξ a : ℝ} (ha : 0 ≤ a) {f : ℂ → ℝ} (hf : Continuous f) :
    sqMetricC ξ a f ∈ pmetSet closedUnitSquare := by
  refine ⟨fun x => ?_, fun x y z => ?_⟩
  · rw [sqMetricC_apply' hf]
    simp only [lenMetricOn, crossLenIn_singleton,
      LFPP.lfppDOn_self DFGPS.convex_closedUnitSquare x.2, ENNReal.toReal_zero, mul_zero]
  · rw [sqMetricC_apply' hf, sqMetricC_apply' hf, sqMetricC_apply' hf, ← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 ha)
    simp only [lenMetricOn, crossLenIn_singleton]
    rw [← ENNReal.toReal_add (lfppDOn_unitSq_ne_top hf (x, y)) (lfppDOn_unitSq_ne_top hf (y, z))]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨lfppDOn_unitSq_ne_top hf (x, y),
      lfppDOn_unitSq_ne_top hf (y, z)⟩) (LFPP.lfppDOn_triangle _ _ _)

end S6Thm
end DDDF
end LQGMetric
