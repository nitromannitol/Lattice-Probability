/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.LFPP.WeylField at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.LFPP.WeylUpper
import LatticeProb.Bonanno.LQGMetric.Field.HeatMollifyCont
import LatticeProb.Bonanno.LQGMetric.Metric.WeylMetric

/-!
# DFGPS.S5: the LFPP Weyl identity `D^ε_{h+f} = e^{ξ f*_ε}·D^ε_h`

Task P2-LFPP, item 3 (DFGPS.S5, `lqg-metric-estimates-final.tex`; Weyl scaling GM (1.6),
`uniqueness-final.tex` l. 300–302). For a bounded continuous `f`, `(h + f)*_ε = h*_ε + f*_ε`
wherever the truncated pairings defining `h*_ε` converge (`heatMollify_addFun`), and the
deterministic identity `lfppD_add_eq_weylScale` gives the Weyl identity on the a.s. event where
`h*_ε` is continuous.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace LFPP

/-- **Additivity of the heat mollification** where the limits exist. -/
theorem heatMollify_add_of_tendsto {ε : ℝ} {h g : DistC} {z : ℂ}
    (hh : Tendsto (fun n : ℕ => h (heatTrunc (ε ^ 2 / 2) z n)) atTop (𝓝 (heatMollify ε h z)))
    (hg : Tendsto (fun n : ℕ => g (heatTrunc (ε ^ 2 / 2) z n)) atTop (𝓝 (heatMollify ε g z))) :
    heatMollify ε (h + g) z = heatMollify ε h z + heatMollify ε g z :=
  (hh.add hg).limUnder_eq

theorem tendsto_heatMollify_ofCont (f : C(ℂ, ℝ)) (M : ℝ) (hM : ∀ w, |f w| ≤ M) {ε : ℝ}
    (hε : ε ≠ 0) (z : ℂ) :
    Tendsto (fun n : ℕ => ofCont f (heatTrunc (ε ^ 2 / 2) z n)) atTop
      (𝓝 (heatMollify ε (ofCont f) z)) := by
  have hs : 0 < ε ^ 2 / 2 := by positivity
  have hi := integrable_heatKernel_mul_of_bdd f M hM _ hs z
  rw [heatMollify_ofCont_of_integrable f ε hε z hi]
  simp_rw [mul_comm (f _)]
  exact tendsto_ofCont_heatTrunc f _ hs z hi

/-- `(h + f)*_ε = h*_ε + f*_ε` when the truncations of `h` converge. -/
theorem heatMollify_addFun {ε : ℝ} (hε : ε ≠ 0) {h : DistC}
    (hconv : ∀ z, Tendsto (fun n : ℕ => h (heatTrunc (ε ^ 2 / 2) z n)) atTop
      (𝓝 (heatMollify ε h z))) (f : C(ℂ, ℝ)) (M : ℝ) (hM : ∀ w, |f w| ≤ M) :
    heatMollify ε (addFun h f) = fun z => heatMollify ε h z + heatMollify ε (ofCont f) z := by
  funext z
  exact heatMollify_add_of_tendsto (hconv z) (tendsto_heatMollify_ofCont f M hM hε z)

/-- `f*_ε` as a continuous function, for bounded continuous `f` -/
def mollCont (ε : ℝ) (hε : ε ≠ 0) (f : C(ℂ, ℝ)) (M : ℝ) (hM : ∀ w, |f w| ≤ M) : C(ℂ, ℝ) :=
  ⟨heatMollify ε (ofCont f), continuous_heatMollify_ofCont f M hM ε hε⟩

/-- **DFGPS.S5, the LFPP Weyl identity** (pathwise form): if the truncations of `h` converge
locally uniformly (so `h*_ε` is continuous), then for bounded continuous `f`,
`D^ε_{h+f} = e^{ξ f*_ε}·D^ε_h`. -/
theorem lfppDistE_addFun_eq_weylScale (ξ : ℝ) {ε : ℝ} (hε : ε ≠ 0) {h : DistC}
    (hconv : TendstoLocallyUniformly (fun (n : ℕ) (z : ℂ) => h (heatTrunc (ε ^ 2 / 2) z n))
      (heatMollify ε h) atTop) (hc : Continuous (heatMollify ε h)) (f : C(ℂ, ℝ)) (M : ℝ)
    (hM : ∀ w, |f w| ≤ M) (z w : ℂ) :
    lfppDistE ξ ε (addFun h f) z w =
      weylScale ξ (mollCont ε hε f M hM) (lfppDistCM ξ ε h hc) z w := by
  rw [lfppDistE_eq_lfppDOn, heatMollify_addFun hε (fun z => (tendstoLocallyUniformlyOn_univ.2 hconv).tendsto_at (mem_univ z)) f M hM]
  exact lfppD_add_eq_weylScale hc (mollCont ε hε f M hM) z w

end LFPP
end LQGMetric
