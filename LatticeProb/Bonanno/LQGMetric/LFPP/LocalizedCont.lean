/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.LFPP.LocalizedCont at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.LFPP.Localized
import LatticeProb.Bonanno.LQGMetric.LFPP.Length
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg

/-!
# DFGPS.S4: continuity of `ĥ*_ε` and the localized LFPP metric

Task P2-LFPP. DFGPS l. 675 ("`ĥ*_ε` a.s. has a continuous modification"): with `ĥ*_ε(z)`
defined as the pairing `⟨h, ψ_ε(z - ·) p_{ε²/2}(z, ·)⟩`, the map `z ↦ ψ_ε(z - ·) p_{ε²/2}(z, ·)`
is continuous into the test-function space (`continuous_testFamK`, Field/Measurable.lean, on
closed balls), so `ĥ*_ε` is continuous for *every* distribution `h` and no modification is
needed. Hence `D̂^ε_h` is a continuous length metric (`lfppLocCM`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace LFPP

theorem contDiff_locTest_uncurry (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry fun (z w : ℂ) => locBump ε hε (z - w) * heatKernel (ε ^ 2 / 2) z w) := by
  unfold heatKernel
  exact ((contDiff_locBump ε hε).comp (contDiff_fst.sub contDiff_snd)).mul
    (contDiff_const.mul (Real.contDiff_exp.comp
      (((contDiff_norm_sq ℝ).comp (contDiff_fst.sub contDiff_snd)).neg.div_const _)))

/-- `z ↦ ψ_ε(z - ·) p_{ε²/2}(z, ·)` is continuous into the test functions. -/
theorem continuous_locTest (ε : ℝ) (hε : 0 < ε) : Continuous (locTest ε hε) := by
  rw [continuous_iff_continuousAt]
  intro z0
  set B := closedBall z0 1
  let K : TopologicalSpace.Compacts ℂ :=
    ⟨closedBall z0 (1 + Real.sqrt ε), isCompact_closedBall _ _⟩
  let Ψ : B → ℂ → ℝ := fun x w => locBump ε hε (x.1 - w) * heatKernel (ε ^ 2 / 2) x.1 w
  have hs : ∀ x : B, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Ψ x) :=
    fun x => (locTest ε hε x.1).contDiff
  have hK : ∀ x : B, ∀ w ∉ (K : Set ℂ), Ψ x w = 0 := by
    intro x w hw
    have hw' : w ∉ closedBall x.1 (Real.sqrt ε) := by
      intro hin
      apply hw
      show w ∈ closedBall z0 (1 + Real.sqrt ε)
      rw [mem_closedBall] at hin ⊢
      have := x.2
      rw [mem_closedBall] at this
      linarith [dist_triangle w x.1 z0]
    simp only [Ψ, locBump_comp_eq_zero ε hε x.1 hw', zero_mul]
  have hD : ∀ i : ℕ, Continuous fun p : B × ℂ => iteratedFDeriv ℝ i (Ψ p.1) p.2 := fun i =>
    (continuous_iteratedFDeriv_snd (contDiff_locTest_uncurry ε hε) i).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hc := continuous_testFamK K Ψ hs hK hD
  have he : (fun x : B => locTest ε hε x.1) = (ofSuppC K) ∘ testFamK K Ψ hs hK := by
    funext x; ext w; rfl
  have hB : Continuous fun x : B => locTest ε hε x.1 := by
    rw [he]; exact (ofSuppC K).continuous.comp hc
  exact (continuousOn_iff_continuous_restrict.2 hB).continuousAt
    (closedBall_mem_nhds z0 one_pos)

/-- `ĥ*_ε` is continuous for every distribution `h`. -/
theorem continuous_locMollify (ε : ℝ) (hε : 0 < ε) (h : DistC) :
    Continuous (locMollify ε hε h) :=
  (map_continuous h).comp (continuous_locTest ε hε)

/-- `(h, z) ↦ ĥ*_ε(z)` is jointly measurable. -/
theorem measurable_locMollify (ε : ℝ) (hε : 0 < ε) :
    Measurable fun p : DistC × ℂ => locMollify ε hε p.1 p.2 := by
  have := measurable_uncurry_of_continuous_of_measurable (u := fun (z : ℂ) (h : DistC) =>
      h (locTest ε hε z))
    (fun h => continuous_locMollify ε hε h) (fun z => measurable_distOn_apply _)
  exact this.comp measurable_swap

end LFPP
end LQGMetric
