/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Loewner.CoreArc3b at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.CoreArc3a
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Module.Connected

/-!
# CORE_ARC, part 3b: no jumps (the analytic core of left continuity of `arcTime`)

Plan node "No jump (left continuity)" of `blueprint/CORE_ARC_PLAN.md`.

## Main results

* `norm_fwdMap_sub_le_uniform` (forward form of UB): for `A` continuous with `A 0 = 0`,
  `0 < h`, `|A| ≤ M` on `[0,h]` and `z ∈ ℍ \ K_h`: `‖f_h z - z‖ ≤ 24 M + 8 √h`.
  Proof: `z = revMap W h (f_h z)` for the time-reversed driver `W t = A (h - t) - A h`
  (`isReverseSol_of_isForwardSol`), then UB (`norm_revMap_sub_le`).
* `tendsto_fwdMap_nhdsLT_of_mem`: a point `z ∈ K_s` not in `K_{s'}` for `s' < s` has
  `f_{s'} z → 0` as `s' ↑ s` (local growth T6, `norm_fwdMap_le_of_mem_diff`).
* `no_jump` (the Vitali-type limit argument that uses these) is in `CoreArc3c.lean`.

## Sources

Route of `blueprint/CORE_ARC_PLAN.md` (the project's own; see `handoff/CORE-2.md`). The
analytic tools are standard: Cauchy integral formula and power series of Cauchy integrals
(mathlib `Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable`,
`hasFPowerSeriesOn_cauchy_integral`), dominated convergence, identity theorem
(`AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero`). Own elementary proof of the
assembly (a Vitali-type limit argument).
-/

noncomputable section

open Set Filter Topology Metric MeasureTheory
open scoped Real NNReal

namespace QuantumZipper

namespace CoreArc

variable {A : ℝ → ℝ}

/-- **UB, forward form.** The forward map moves points by at most `24 M + 8 √h`. -/
theorem norm_fwdMap_sub_le_uniform (hA : Continuous A) (hA0 : A 0 = 0) {h M : ℝ} (hh : 0 < h)
    (hM : ∀ t ∈ Icc (0 : ℝ) h, |A t| ≤ M) {z : ℂ} (hz : z ∈ H \ fwdHull A h) :
    ‖fwdMap A h z - z‖ ≤ 24 * M + 8 * Real.sqrt h := by
  obtain ⟨hz0, T', hT', u, hu⟩ := (FwdHolo.mem_compl_fwdHull_iff hh.le).1 hz
  have huh : IsForwardSol A z h u := isForwardSol_restrict hu hh.le hT'.le
  set W : ℝ → ℝ := fun t => A (h - t) - A h with hWdef
  have hWc : Continuous W := by rw [hWdef]; fun_prop
  have hW0 : W 0 = 0 := by simp [hWdef]
  have hAW : (fun t => W (h - t) - W h) = A := by
    funext t
    simp only [hWdef, sub_sub_cancel, sub_self, hA0]
    ring
  have huh' : IsForwardSol (fun t => W (h - t) - W h) z h u := by rw [hAW]; exact huh
  obtain ⟨hrev, hu0⟩ := LoewnerAlgebra.isReverseSol_of_isForwardSol hW0 hWc huh' hz0 hh.le
  have hrevz : revMap W h (u h) = z := by
    rw [revMap_eq W hWc (u h) hh.le le_rfl hrev]
    simp [hu0]
  have hfz : fwdMap A h z = u h := fwdMap_eq hA hz0 huh ⟨hh.le, le_rfl⟩
  have hwH : u h ∈ H := (im_isForwardSol_le hA hz0 huh).2 h ⟨hh.le, le_rfl⟩
  have hWM : ∀ r ∈ Icc (0 : ℝ) h, |W r| ≤ 2 * M := by
    intro r hr
    have ha := hM (h - r) ⟨by linarith [hr.2], by linarith [hr.1]⟩
    have hb := hM h ⟨hh.le, le_rfl⟩
    calc |W r| = |A (h - r) - A h| := rfl
      _ ≤ |A (h - r)| + |A h| := abs_sub _ _
      _ ≤ 2 * M := by linarith
  have hub := norm_revMap_sub_le hWc hW0 hh hWM hwH
  rw [hrevz] at hub
  rw [hfz, norm_sub_rev]
  linarith

/-- Local growth at the swallowing time: `f_{s'} z → 0` as `s' ↑ s` for `z` swallowed exactly
at time `s`. -/
theorem tendsto_fwdMap_nhdsLT_of_mem (hA : Continuous A) {s : ℝ} (hs : 0 < s) {z : ℂ}
    (hz : z ∈ fwdHull A s) (hnot : ∀ s' ∈ Ico (0 : ℝ) s, z ∉ fwdHull A s') :
    Tendsto (fun s' => fwdMap A s' z) (𝓝[<] s) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hAδ⟩ := Metric.continuousAt_iff.1 (hA.continuousAt (x := s)) (ε / 16) (by positivity)
  set η := min (min δ s) ((ε / 8) ^ 2) with hη
  have hη0 : 0 < η := by positivity
  filter_upwards [Ioo_mem_nhdsLT (show s - η < s by linarith)] with s' hs'
  have hηδ : η ≤ δ := (min_le_left _ _).trans (min_le_left _ _)
  have hηs : η ≤ s := (min_le_left _ _).trans (min_le_right _ _)
  have hηe : η ≤ (ε / 8) ^ 2 := min_le_right _ _
  have hs'0 : 0 ≤ s' := by linarith [hs'.1]
  have hh : 0 ≤ s - s' := by linarith [hs'.2]
  have hM : ∀ t ∈ Icc (0 : ℝ) (s - s'), |A (s' + t) - A s'| ≤ ε / 8 := by
    intro t ht
    have h1 := hAδ (x := s' + t) (by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2, hs'.1])
    have h2 := hAδ (x := s') (by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hs'.1, hs'.2])
    rw [Real.dist_eq] at h1 h2
    calc |A (s' + t) - A s'| = |(A (s' + t) - A s) - (A s' - A s)| := by ring_nf
      _ ≤ |A (s' + t) - A s| + |A s' - A s| := abs_sub _ _
      _ ≤ ε / 8 := by linarith
  have hz' : z ∈ fwdHull A (s' + (s - s')) := by rwa [add_sub_cancel]
  have hb := norm_fwdMap_le_of_mem_diff hA hs'0 hh hM hz' (hnot s' ⟨hs'0, hs'.2⟩)
  have hsq : Real.sqrt (s - s') < ε / 8 :=
    (Real.sqrt_lt' (by positivity)).2 (by linarith [hs'.1])
  rw [dist_zero_right]
  linarith

/-- Off the hull, `f_{s'} z → f_s z` as `s' ↑ s`. -/
theorem tendsto_fwdMap_nhdsLT_of_notMem (hA : Continuous A) {s : ℝ} (hs : 0 < s) {z : ℂ}
    (hz : z ∈ H \ fwdHull A s) :
    Tendsto (fun s' => fwdMap A s' z) (𝓝[<] s) (𝓝 (fwdMap A s z)) := by
  have hc := (FwdHolo.continuousOn_fwdMap_time hA hs.le hz) s ⟨hs.le, le_rfl⟩
  refine hc.tendsto.mono_left ?_
  rw [← nhdsWithin_Ioo_eq_nhdsLT hs]
  exact nhdsWithin_mono _ Ioo_subset_Icc_self

end CoreArc

end QuantumZipper
