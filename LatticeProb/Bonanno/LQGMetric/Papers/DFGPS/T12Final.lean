/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.T12Final at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T12P6D
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_13
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17Core3J
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_20TranslB
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_20BilipMain
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_1RadialMain
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GenTrans
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GenRatio
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffRed
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_12

/-!
# DFGPS Theorem 1.2: assembly (P-5), modulo the locality node `T12Locality`

Source: DFGPS arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Theorem 1.2,
T:1339–1386. With `φ` and the coupling of `exists_subseq_coupling_ae'`, the weak LQG metric is
`D := patchT (ε ∘ φ)` (D96):
* measurability: `measurable_patchT`;
* Axioms I, III: `ae_length_weyl_isGFFPlusCont` (T12P6B);
* Axiom IV′: `ae_patchT_translate` (T12P6D);
* Axiom V: `tightAcrossScales_patchT` (Lemma 2.13, T12P6C);
* convergence in probability: `tendstoInProbLU_patchT` (Lemma 2.12, T12P6C);
* Axiom II (locality, T:1358–1374 via Lemma 2.17): the open node `T12Locality` (handoff
  P2-DFT12d).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS.T12

open Blueprint

/-- **open node (Axiom II for `patchT`)**: locality of the glued metric at every GFF plus a
continuous function, given the conclusions `T12Good` of the coupling -/
def T12Locality (γ : ℝ) (εs : ℕ → ℝ) (hεs : ∀ k, 0 < εs k) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsGFFPlusCont h P → ∀ U : TopologicalSpace.Opens ℂ,
      ∃ F : DistOn U → (ℂ → ℂ → ℝ≥0∞), Measurable F ∧
        ∀ᵐ ω ∂P, ∀ z ∈ U, ∀ w ∈ U,
          (patchT (xiGamma γ) εs hεs (h ω)).internal U z w = F (restrictTo U (h ω)) z w

end LQGMetric.DFGPS.T12
