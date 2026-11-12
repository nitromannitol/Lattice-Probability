/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTPort.Foundations.ConeCirc at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.Cone
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgCont
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate

/-!
DMS Def 4.10 (L2198): the average of the cone field on `∂B(0, e^{-s})` is the radial process.
Deterministic form here: for any field `y` whose circle average at radius `r` about `0` exists
(as the limit of LM's mollified averages), and any continuous `A` making the radial function
locally integrable,
`circleAvg (coneField y A Q) r 0 = circleAvg y r 0 + Q(−log r) + A(−log r)`
(`circleAvg_coneField`), hence at `r = e^{-t}`: `Q t + A t` plus the circle average of `y`
(`circleAvg_coneField_exp`). For `y` the lateral part of a whole-plane GFF the latter vanishes a.s.

Proof: adapted from LM `CircleAvg.tendsto_mollAvg_ofCont` (LQGMetric/Field/CircleAvgCont.lean):
near the circle `|z| = r` the radial function agrees with the continuous function
`z ↦ F(−log max(|z|, r/2))`, and the mollifier at scale `2^{-n} ≤ r/2` only sees that region
(locality of `ofFunC`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric

namespace MatedCRTHarmonic.MoTPort

open LQGMetric

namespace ConeCirc

lemma ofFunC_apply' {f : ℂ → ℝ} (hf : LocallyIntegrable f volume) (φ : TestC) :
    ofFunC f φ = ∫ x, φ x * f x := by
  rw [ofFunC, Distribution.ofFun_apply (hf.locallyIntegrableOn _)]
  rfl

/-- locality: the pairing with the mollifier `ψ_{n,x}` only sees `f` on `B(x, 2^{-n})` -/
lemma ofFunC_bumpTest_eq {f g : ℂ → ℝ} (hf : LocallyIntegrable f volume)
    (hg : LocallyIntegrable g volume) {x : ℂ} {δ : ℝ} (hfg : ∀ y, dist y x < δ → f y = g y)
    {n : ℕ} (hn : (2 : ℝ)⁻¹ ^ n ≤ δ) :
    ofFunC f (bumpTest n x) = ofFunC g (bumpTest n x) := by
  rw [ofFunC_apply' hf, ofFunC_apply' hg]
  congr 1
  funext y
  by_cases hy : dist y x < δ
  · rw [hfg y hy]
  · rw [CircleAvg.bumpTest_eq_zero_of_le n (le_trans hn (not_lt.mp hy))]; simp

end ConeCirc

end MatedCRTHarmonic.MoTPort
