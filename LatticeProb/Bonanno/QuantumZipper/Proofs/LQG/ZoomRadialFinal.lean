/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.LQG.ZoomRadialFinal at commit fdb5cad; only the module paths of local imports are changed.
   Changed for Lean v4.35: set_option autoImplicit true after the imports, the default of the source repository (this library disables it).
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeTranslation

set_option autoImplicit true

/-!
This file supplies the measurability input of the D3 radial comparison
(`ZoomRadial.abs_prob_zoomRadial_sub_le`, TASKS.md row R6): for a Brownian motion `b`, the map

`ω ↦ trunc S (Vpath α Q c b ω) : Ω → (ℝ → ℝ)`

is a.e. strongly measurable for the product σ-algebra on `ℝ → ℝ` (step (i) of the task list). The
proof avoids filtrations and stopping-time measurability entirely, using two ingredients:

* `exists_nice_version`: a version `b₀` of a Brownian motion which is measurable as a function of
  `(s, ω)`, is continuous with `b₀ 0 = 0` for *every* `ω`, and whose drifted path
  `s ↦ √2 b₀ s − (Q − α) s` reaches level `−c` for *every* `ω` (the last two properties come from
  the a.e. statements by freezing the process on the null set where they fail, as in
  `WedgeTrans.wedge_translation`);
* `Thit`: a *measurable surrogate* for the first hitting time of `0` by the drifted radial path
  `Xc`, namely the volume of the set of times where the rational predicate
  `∀ n, ∃ q ∈ ℚ ∩ [0,t], √2 p q − (Q − α) q ≤ −c + 1/(n+1)` fails. The predicate tests only values
  of the path at rational times, hence is jointly measurable, and `Thit_eq` shows that for
  continuous paths that do hit `0` the surrogate is exactly the hitting time.

Sources: Sheffield (arXiv:1012.4797) §1.6 and the proof of Prop. 1.6 (the radial process at a zoom
is `BM + drift` re-centred at its first hit of `0`); the reduction of the hitting time to rational
times is an own elementary argument (the same device as in
`ZoomRadialMain.tendsto_prob_wedge_high`).
-/

noncomputable section

open Classical
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace ZoomRadial

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-! ## 2. The hitting time of `−c` by the drifted path, via a measurable surrogate -/

/-! ## 3. Step (i): measurability of the truncated zoom radial path -/

/-! ## 4. The surrogate is the hitting time -/

/-! ## 5. A nice version of a Brownian motion, and step (i) -/

/-- The wedge-path process of a wedge process is a.e. strongly measurable as a path. -/
theorem aemeasurable_wedgePath {α Q : ℝ} {A : ℝ → Ω → ℝ} (hA : IsWedgeProcess α Q A P) :
    AEMeasurable (fun ω => fun t => A t ω) P := by
  classical
  obtain ⟨B, B', hB, hB', hBB', hAB⟩ := hA
  obtain ⟨B₀, hB₀m, hB₀c, hB₀B⟩ := WedgeRes.exists_good_version hB
  obtain ⟨B₀', hB₀'m, hB₀'c, hB₀'B⟩ := WedgeRes.exists_good_version hB'
  have hYtc : ∀ ω, Continuous fun s : ℝ => √2 * B₀' s.toNNReal ω - (α - Q) * s := fun ω =>
    (continuous_const.mul ((hB₀'c ω).comp continuous_real_toNNReal)).sub
      (continuous_const.mul continuous_id)
  have hYtm : ∀ s : ℝ, Measurable fun ω => √2 * B₀' s.toNNReal ω - (α - Q) * s := fun s =>
    (((hB₀'m.of_uncurry_left (x := s.toNNReal)).const_mul (√2)).sub_const ((α - Q) * s))
  have hYtJ : Measurable fun p : Ω × ℝ => √2 * B₀' p.2.toNNReal p.1 - (α - Q) * p.2 :=
    (measurable_uncurry_of_continuous_of_measurable hYtc hYtm).comp measurable_swap
  have hLm : Measurable fun ω => lastZero (fun s : ℝ => √2 * B₀' s.toNNReal ω - (α - Q) * s) :=
    WedgeMeas.measurable_lastZero hYtc hYtm
  have hmeas : Measurable fun ω => fun t : ℝ => WedgeTrans.wA α Q B₀ B₀' t ω := by
    refine measurable_pi_iff.2 fun t => ?_
    by_cases ht : 0 ≤ t
    · have heq : (fun ω => WedgeTrans.wA α Q B₀ B₀' t ω)
          = fun ω => √2 * B₀ t.toNNReal ω + (α - Q) * t := by
        funext ω
        simp only [WedgeTrans.wA, wedgePath, if_pos ht]
      rw [heq]
      exact (((hB₀m.of_uncurry_left (x := t.toNNReal)).const_mul (√2)).add_const _)
    · have heq : (fun ω => WedgeTrans.wA α Q B₀ B₀' t ω)
          = fun ω => √2 * B₀' (-t + lastZero (fun s : ℝ => √2 * B₀' s.toNNReal ω
              - (α - Q) * s)).toNNReal ω - (α - Q) * (-t + lastZero (fun s : ℝ =>
                √2 * B₀' s.toNNReal ω - (α - Q) * s)) := by
        funext ω
        simp only [WedgeTrans.wA, wedgePath, if_neg ht]
      rw [heq]
      refine hYtJ.comp (measurable_id.prodMk ?_)
      exact (measurable_const.add hLm)
  refine hmeas.aemeasurable.congr ?_
  filter_upwards [hB₀B, hB₀'B] with ω h1 h2
  have h2' : ∀ s : ℝ≥0, B' s ω = B₀' s ω := fun s => (h2 s).symm
  have hYeq : (fun s : ℝ => √2 * B' s.toNNReal ω - (α - Q) * s)
      = fun s : ℝ => √2 * B₀' s.toNNReal ω - (α - Q) * s := by
    funext s
    rw [h2' s.toNNReal]
  funext t
  rw [hAB ω t]
  by_cases ht : 0 ≤ t
  · simp only [WedgeTrans.wA, wedgePath, if_pos ht]
    rw [← h1 t.toNNReal]
  · simp only [WedgeTrans.wA, wedgePath, if_neg ht, hYeq, h2']

/-! ## 6. Evaluating a path at a measurable time with countable range -/

/-! ## 7. The measurable path-space surrogate of the truncated zoom path -/

end ZoomRadial
end QuantumZipper
