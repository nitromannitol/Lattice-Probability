/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L1Tail at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2Box
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Topology.Path
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.Notation
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2Bridge
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L7Trunc
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L5Kernel
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseKernel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L7
import LatticeProb.Bonanno.LQGMetric.Gaussian.SupTailField
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseCont
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeRestriction
import Mathlib.Probability.Process.FiniteDimensionalLaws
import LatticeProb.Bonanno.LQGMetric.Gaussian.FerniqueDZZ
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenBasic
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Measure.Interval
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# DG Lemma 3.1, last step: Gaussian tail of `max_K |h¹ − h²|` (task P2-DG3A, WP-118)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, proof of Lemma A.1 (DG:2160–2164),
after the increment bound (A.3) `Var(f(z₁) − f(z₂)) ≲ |z₁ − z₂|`: "this together with the
Kolmogorov continuity criterion will show that … `f` is locally Hölder continuous …
Furthermore, since `K` is compact a.s. `max_K |(h^U − ĥ^tr)(z)| < ∞` so the Borell–TIS
inequality … shows that `E[max_K |…|] < ∞` and that (A.1) holds for an appropriate choice of
`c₀` and `c₁`." (Lemma A.2 and hence Lemma 3.1 (3.5) end the same way.)

* `gaussian_tail_of_incr` — for a continuous centred Gaussian field `X` on a square with
  `E(X_v − X_u)² ≤ L|u − v|` and `Var X_v ≤ σ²` there, and any `K` inside the square,
  `P[max_K |X| > A] ≤ c₀ e^{−c₁ A²}` for all `A ≥ 0` (DZZ Lemma 2.3 (Fernique/chaining) gives the
  bound on `E max`, Borell–TIS the tail: `DZZ.dzz_box_sup_abs_tail`). DG get `E max < ∞` from
  a.s. finiteness; with (A.3) the chaining bound gives it directly.
* `dg_lemma32_of_field` — DG Lemma 3.2 for two fields whose difference on `K̄` is such an `X`
  (combining with `dg_lemma32_of_tail`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

namespace LQGMetric
namespace DG

open DZZ SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Borell–TIS step of DG Lemma A.1/3.1**: `P[max_K |X| > A] ≤ c₀ e^{−c₁A²}` -/
theorem gaussian_tail_of_incr [IsProbabilityMeasure P] {X : ℂ → Ω → ℝ}
    (hX : IsGaussianProcess X P) (h0 : ∀ v, ∫ ω, X v ω ∂P = 0) {y : ℂ} {b L σ : ℝ}
    (hb : 0 < b) (hL : 0 < L) (hσ : 0 < σ)
    (hc : ∀ ω, ContinuousOn (fun v => X v ω) (ferniqueBox y b))
    (hinc : ∀ u ∈ ferniqueBox y b, ∀ v ∈ ferniqueBox y b,
      ∫ ω, (X v ω - X u ω) ^ 2 ∂P ≤ L * ‖u - v‖)
    (hvar : ∀ v ∈ ferniqueBox y b, Var[X v; P] ≤ σ ^ 2) {K : Set ℂ}
    (hK : K ⊆ ferniqueBox y b) :
    ∃ c₀ c₁ : ℝ, 0 < c₁ ∧ ∀ A : ℝ, 0 ≤ A →
      P {ω | ¬ ∀ z ∈ K, |X z ω| ≤ A} ≤ ENNReal.ofReal (c₀ * Real.exp (-c₁ * A ^ 2)) := by
  set M := ferniqueCF * Real.sqrt (L * b)
  refine ⟨2 * Real.exp (M ^ 2 / (2 * σ ^ 2)), 1 / (2 * (2 * σ ^ 2)), by positivity,
    fun A hA => ?_⟩
  have h := dzz_box_sup_abs_tail hX h0 hb hL hc hinc hvar le_rfl hA
  have hsub : {ω | ¬ ∀ z ∈ K, |X z ω| ≤ A} ⊆
      {ω | A ≤ ⨆ v : ferniqueBox y b, |X v ω|} := by
    intro ω hω
    simp only [mem_ofPred_eq, not_forall, not_le] at hω ⊢
    obtain ⟨z, hz, hlt⟩ := hω
    have hbdd : BddAbove (range fun v : ferniqueBox y b => |X v ω|) := by
      obtain ⟨C, hC⟩ := ((isCompact_ferniqueBox y b).bddAbove_image (hc ω).abs)
      exact ⟨C, by rintro _ ⟨v, rfl⟩; exact hC ⟨v, v.2, rfl⟩⟩
    exact hlt.le.trans (le_ciSup hbdd ⟨z, hK hz⟩)
  refine (measure_mono hsub).trans ?_
  rw [← ofReal_measureReal (measure_ne_top _ _),
    show -(1 / (2 * (2 * σ ^ 2))) * A ^ 2 = -A ^ 2 / (2 * (2 * σ ^ 2)) by ring]
  exact ENNReal.ofReal_le_ofReal h

end DG
end LQGMetric
