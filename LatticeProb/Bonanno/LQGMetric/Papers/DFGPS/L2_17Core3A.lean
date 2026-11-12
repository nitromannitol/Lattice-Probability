/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_17Core3A at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17Core2H
import LatticeProb.Bonanno.LQGMetric.Metric.WeylLocal

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.17, core case: the `h̊` side of Step 4 (item R2 of handoff/P2-DFB11.md)

Source: DFGPS = arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Lemma 2.17,
Step 4 (T:1270–1273): "by Lemma 2.12, a.s. `D_h(·,·;W') = (e^{ξφ𝔥}·D_{h−φ𝔥})(·,·;W')`. Hence
`D_h(·,·;W')` is a measurable function of `𝔥` and `D_{h−φ𝔥}(·,·;W')`."

In the limit coupling (`indep_stage_limit`) the first limit metric `D₁` (of `h̃`) and the second
`D₂` (of `h̃ − fn`, `fn = Fb ∘ X`) are related by `D₁ = e^{ξ Fb}·D₂` (the Weyl relation in the
direction used by the paper at T:1271; item R1). Then:

* `intFn_eq_of_weyl` — (deterministic fibre property) the internal metric `D₁(·,·;W')` is
  determined by `Fb` and by `d₂_{W'}` (the limit of the internal metrics of the second LFPP on
  `W̄'`): Lemma 2.5 B identifies `D₂(·,·;W')` from `d₂_{W'}` (`intFn_eq_of_isDyadicLimit`), and
  the locality of Weyl scaling (`internal_weyl_eq_of_internal_eq`, Metric/WeylLocal.lean)
  identifies `(e^{ξF}·D₂)(·,·;W')` from `D₂(·,·;W')` and `F`.
* `comap_intFn_le_aeClosure_weyl` — hence `σ(D₁(·,·;W')) ⊆ σ(Fb, d₂_{W'})` up to null sets
  (Lusin separation, `comap_le_aeClosure_of_fiber`; the paper's "measurable function" claim).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace
open scoped ENNReal

namespace LQGMetric.DFGPS.L217

open Blueprint LFPP MetricGeometry GM.Bilip

/-- **Fibre property of Step 4** (T:1271–1272): for dyadic limits `x, y` with
`x.1 = e^{ξF}·y.1` (and the same for `x', y'` with the same `F`), `y.2 W = y'.2 W` forces
`D_{x.1}(·,·;W) = D_{x'.1}(·,·;W)`. -/
theorem intFn_eq_of_weyl {ξ : ℝ} {F : C(ℂ, ℝ)} {x x' y y' : DyProd} (hx : IsDyadicLimit x)
    (hx' : IsDyadicLimit x') (hy : IsDyadicLimit y) (hy' : IsDyadicLimit y')
    (hw : ∀ hc : IsContinuousMetric y.1, ∀ u v : ℂ,
      ENNReal.ofReal (x.1 (u, v)) = weylScale ξ F ⟨y.1, hc⟩ u v)
    (hw' : ∀ hc : IsContinuousMetric y'.1, ∀ u v : ℂ,
      ENNReal.ofReal (x'.1 (u, v)) = weylScale ξ F ⟨y'.1, hc⟩ u v)
    (W : dyadicDomainsC) (he : y.2 W = y'.2 W) :
    intFn W x.1 = intFn W x'.1 := by
  have hyy := intFn_eq_of_isDyadicLimit hy hy' W he
  obtain ⟨hcx, hlx⟩ := hx.1
  obtain ⟨hcx', hlx'⟩ := hx'.1
  obtain ⟨hcy, hly⟩ := hy.1
  obtain ⟨hcy', hly'⟩ := hy'.1
  have hWo := isOpen_of_dyadicDomainsC W
  rw [← internal_eq_intFn ⟨y.1, hcy⟩ hly hWo, ← internal_eq_intFn ⟨y'.1, hcy'⟩ hly' hWo] at hyy
  rw [← internal_eq_intFn ⟨x.1, hcx⟩ hlx hWo, ← internal_eq_intFn ⟨x'.1, hcx'⟩ hlx' hWo]
  funext u v
  exact internal_weyl_eq_of_internal_eq (D₁ := ⟨y.1, hcy⟩) (D₂ := ⟨y'.1, hcy'⟩)
    (D₁' := ⟨x.1, hcx⟩) (D₂' := ⟨x'.1, hcx'⟩) hWo (hw hcy) (hw' hcy')
    (fun a _ b _ => congrFun (congrFun hyy a) b) (fun _ _ => rfl) u v

end L217

end LQGMetric.DFGPS
