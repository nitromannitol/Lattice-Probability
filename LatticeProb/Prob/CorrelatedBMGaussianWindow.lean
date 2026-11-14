import LatticeProb.Prob.CorrelatedBMThreeWindows
import LatticeProb.Prob.CorrelatedBMIncrementGaussian
import LatticeProb.Prob.IndependentGaussianWindow

/-! # Gaussian window estimates for Brownian increments

A coordinate increment on a middle window is independent of the processes on
both outer windows. This gives a Gaussian window bound with a random center. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace LatticeProb.CorrelatedBM

open MatedCRTHarmonic.MatedCRT

/-- Independent outer-window events and a random center depending on those
windows satisfy a Gaussian interval estimate for a middle increment. -/
theorem measure_outer_inter_middle_window_le {ι : Type*} {γ : ℝ}
    {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ) (l r : ι → ℝ)
    (hsep : ∀ i j, i ≠ j → r i ≤ l j ∨ r j ≤ l i)
    (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hk : l k < r k) (c : Fin 2) {A B : Set Path2} {Y : Path2 → ℝ}
    (hA : MeasurableSet[MeasurableSpace.comap
      (fun ω (p : Fin 2 × {x : ℝ // x ∈ Icc (l i) (r i)}) =>
        coneIncr p.1 p.2.1 (l i) ω) inferInstance] A)
    (hB : MeasurableSet[MeasurableSpace.comap
      (fun ω (p : Fin 2 × {x : ℝ // x ∈ Icc (l j) (r j)}) =>
        coneIncr p.1 p.2.1 (l j) ω) inferInstance] B)
    (hY : Measurable[MeasurableSpace.comap
      (fun ω => ((fun (p : Fin 2 × {x : ℝ // x ∈ Icc (l i) (r i)}) =>
          coneIncr p.1 p.2.1 (l i) ω),
        (fun (p : Fin 2 × {x : ℝ // x ∈ Icc (l j) (r j)}) =>
          coneIncr p.1 p.2.1 (l j) ω))) inferInstance] Y)
    {q : ℝ} (hq : 0 ≤ q) :
    μ ((A ∩ B) ∩ {ω | |Y ω + coneIncr c (r k) (l k) ω| ≤ q}) ≤
      μ A * μ B * ENNReal.ofReal (2 * q / √(2 * Real.pi * (r k - l k))) := by
  let W := fun n ω (p : Fin 2 × {x : ℝ // x ∈ Icc (l n) (r n)}) =>
    coneIncr p.1 p.2.1 (l n) ω
  have : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hW : ∀ n, Measurable[ContinuousMap.measurableSpace] (W n) := by
    intro n
    exact measurable_pi_iff.mpr fun p => measurable_coneIncr p.1 p.2.1 (l n)
  let F := MeasurableSpace.comap (fun ω => (W i ω, W j ω)) inferInstance
  have hF : F ≤ ContinuousMap.measurableSpace := ((hW i).prodMk (hW j)).comap_le
  have hfst : Measurable[F] (W i) :=
    measurable_fst.comp (comap_measurable _)
  have hsnd : Measurable[F] (W j) :=
    measurable_snd.comp (comap_measurable _)
  have hAF : MeasurableSet[F] A := hfst.comap_le A hA
  have hBF : MeasurableSet[F] B := hsnd.comap_le B hB
  obtain ⟨hij', hijk⟩ := indep_outer_windows_and_middle_increment hμ l r hsep
    i j k hij hik hjk hk.le c
  have hAB : IndepSet A B μ := hij'.indepSet_of_measurableSet hA hB
  have hv : (|r k - l k|).toNNReal ≠ 0 := by
    have hp : 0 < |r k - l k| := abs_pos.mpr (ne_of_gt (sub_pos.mpr hk))
    exact ne_of_gt (Real.toNNReal_pos.mpr hp)
  have hb := measure_inter_inter_abs_add_le hF hAF hBF hAB hY
    (measurable_coneIncr c (r k) (l k)) hv
    (map_coneIncr_eq_gaussianReal hμ c (r k) (l k)) hijk hq
  simpa only [abs_of_pos (sub_pos.mpr hk), Real.coe_toNNReal (r k - l k) (le_of_lt (sub_pos.mpr hk))] using hb

end LatticeProb.CorrelatedBM
