/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_17CoreG at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17CoreH
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.MarkovNorm
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8FinCmp

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.17, core case: the two fields of Step 3 are GFF plus bounded continuous

Source: DFGPS = arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Lemma 2.17,
Step 3 (T:1248–1250): "By assertion (item-lfpp-dyadic) of Lemma 2.5, applied once to each of `h`
and `h − φ𝔥`" — Lemma 2.5 (`Lem2_5B`) needs `IsGFFPlusBddCont`. Decision D80, packet P-C.

* `isGFFPlusBddCont_normField` — `h − h_r(z)` (a whole-plane GFF, `isNormalizedAt_recenter`).
* `isGFFPlusBddCont_sub_ofCont` — `g − fn` for a whole-plane GFF `g` and a measurable random
  bounded continuous `fn` (here `fn = φ𝔥`, `harmFn`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace

namespace LQGMetric.DFGPS.L217

open Blueprint

theorem isGFFPlusBddCont_normField {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsNormalizedWPGFF h P) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    IsGFFPlusBddCont (normField h z r) P :=
  isGFFPlusBddCont_of_wp (isNormalizedAt_recenter hh.1 hr z).1

lemma ofCont_neg (f : C(ℂ, ℝ)) : ofCont (-f) = -ofCont f := by
  ext φ
  rw [ofCont_apply, neg_apply, ofCont_apply, ← integral_neg]
  congr 1; funext x
  simp

theorem isGFFPlusBddCont_sub_ofCont {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {g : Ω → DistC} (hg : IsWholePlaneGFF g P) {fn : Ω → C(ℂ, ℝ)} (hfm : Measurable fn)
    (hfb : ∀ ω, ∃ M, ∀ z, |fn ω z| ≤ M) :
    IsGFFPlusBddCont (fun ω => g ω - ofCont (fn ω)) P := by
  refine ⟨measurable_distOn_iff.2 fun φ => ?_, fun ω => -fn ω,
    ContinuousMap.measurable_iff_eval.2 fun z =>
      ((ContinuousMap.measurable_iff_eval.1 hfm) z).neg,
    fun ω => ?_, ?_⟩
  · show Measurable fun ω => g ω φ - ofCont (fn ω) φ
    exact ((measurable_distOn_apply φ).comp hg.measurable).sub
      ((measurable_ofCont_apply φ).comp hfm)
  · obtain ⟨M, hM⟩ := hfb ω
    exact ⟨M, fun z => by simpa using hM z⟩
  · convert hg using 2 with ω
    rw [ofCont_neg, sub_neg_eq_add, sub_add_cancel]

end LQGMetric.DFGPS.L217
